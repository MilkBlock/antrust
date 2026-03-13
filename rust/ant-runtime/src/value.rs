use crate::reference::Reference;
use crate::word::Word;
use crate::words::{hash_word_seed, word_degree, Words};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Elem {
    Word(Word),
    Reference(Reference),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FullSummary {
    pub length: usize,
    pub hash: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Summary {
    pub degree: i32,
    pub max_degree: i32,
    pub full: Option<FullSummary>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Value {
    items: Vec<Elem>,
}

impl Value {
    pub fn empty() -> Self {
        Self { items: Vec::new() }
    }

    pub fn from_words(words: &Words) -> Self {
        let items = words.items().iter().cloned().map(Elem::Word).collect();
        Self { items }
    }

    pub fn from_elems(items: Vec<Elem>) -> Self {
        Self { items }
    }

    pub fn items(&self) -> &[Elem] {
        &self.items
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn append(&self, other: &Self) -> Self {
        let mut items = self.items.clone();
        items.extend_from_slice(&other.items);
        Self { items }
    }

    pub fn summary(&self) -> Summary {
        let mut degree = 0;
        let mut max_degree = 0;
        let mut full_len = 0;
        let mut full_hash = 0;
        let mut full = true;

        for elem in &self.items {
            match elem {
                Elem::Word(word) => {
                    degree += word_degree(word);
                    if full {
                        full_len += 1;
                        full_hash = hash_word_seed(full_hash, word);
                    }
                }
                Elem::Reference(reference) => {
                    degree += reference.values_count;
                    full = false;
                }
            }
            if degree > max_degree {
                max_degree = degree;
            }
        }

        Summary {
            degree,
            max_degree,
            full: if full {
                Some(FullSummary {
                    length: full_len,
                    hash: full_hash,
                })
            } else {
                None
            },
        }
    }

    pub fn pop_n(&self, n: i32) -> (Self, Self) {
        assert!(n >= 0);
        if n == 0 {
            return (Self::empty(), self.clone());
        }

        let summary = self.summary();
        assert!(summary.degree >= n);
        assert!(summary.max_degree >= n);

        let mut degree = 0;
        let mut max_degree = 0;

        for (idx, elem) in self.items.iter().enumerate() {
            let elem_degree = match elem {
                Elem::Word(word) => word_degree(word),
                Elem::Reference(reference) => reference.values_count,
            };
            degree += elem_degree;
            if degree > max_degree {
                max_degree = degree;
            }
            if max_degree >= n {
                let prefix_degree = degree - elem_degree;
                let mut left_items = self.items[..idx].to_vec();
                match elem {
                    Elem::Word(word) => {
                        assert!(prefix_degree + 1 == n);
                        left_items.push(Elem::Word(word.clone()));
                        let right = Self {
                            items: self.items[idx + 1..].to_vec(),
                        };
                        return (Self { items: left_items }, right);
                    }
                    Elem::Reference(reference) => {
                        assert!(prefix_degree < n);
                        assert!(prefix_degree + reference.values_count >= n);
                        let need = n - prefix_degree;
                        let mut left_ref = reference.clone();
                        left_ref.values_count = need;
                        left_items.push(Elem::Reference(left_ref));
                        if reference.values_count == need {
                            let right = Self {
                                items: self.items[idx + 1..].to_vec(),
                            };
                            return (Self { items: left_items }, right);
                        }
                        let mut right_items = Vec::with_capacity(1 + self.items[idx + 1..].len());
                        let mut right_ref = reference.clone();
                        right_ref.offset += need;
                        right_ref.values_count -= need;
                        right_items.push(Elem::Reference(right_ref));
                        right_items.extend_from_slice(&self.items[idx + 1..]);
                        return (Self { items: left_items }, Self { items: right_items });
                    }
                }
            }
        }

        panic!("pop_n exceeded value degree");
    }

    pub fn front_exn(&self) -> (Self, Elem) {
        let (head, tail) = self
            .items
            .split_first()
            .expect("front_exn on empty value");
        (Self::from_elems(tail.to_vec()), head.clone())
    }

    pub fn slice(&self, offset: i32, values_count: i32) -> Self {
        let summary = self.summary();
        assert!(summary.degree == summary.max_degree);
        assert!(summary.degree >= offset + values_count);
        let (_, rest) = self.pop_n(offset);
        let (slice, _) = rest.pop_n(values_count);
        slice
    }

    pub fn words_hash(&self) -> Option<u32> {
        let summary = self.summary();
        summary.full.as_ref().map(|f| f.hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::Source;

    #[test]
    fn summary_full_matches_words() {
        let words = Words::appends(&[Words::from_int(1), Words::from_int(2)]);
        let value = Value::from_words(&words);
        let summary = value.summary();
        let full = summary.full.expect("expected full summary");
        assert_eq!(full.length, 2);
        assert_eq!(full.hash, words.summary().hash);
    }

    #[test]
    fn pop_n_splits_reference() {
        let r = Reference {
            src: Source::K,
            hole_idx: 0,
            offset: 0,
            values_count: 2,
        };
        let value = Value::from_elems(vec![
            Elem::Word(Word::Int(1)),
            Elem::Reference(r.clone()),
            Elem::Word(Word::Int(3)),
        ]);

        let (left, right) = value.pop_n(2);
        assert_eq!(left.summary().degree, 2);
        assert_eq!(right.summary().degree, 2);

        match left.items() {
            [Elem::Word(_), Elem::Reference(split_ref)] => {
                assert_eq!(split_ref.values_count, 1);
                assert_eq!(split_ref.offset, 0);
            }
            _ => panic!("unexpected left slice"),
        }

        match right.items() {
            [Elem::Reference(split_ref), Elem::Word(_)] => {
                assert_eq!(split_ref.values_count, 1);
                assert_eq!(split_ref.offset, 1);
            }
            _ => panic!("unexpected right slice"),
        }
    }

    #[test]
    fn slice_uses_value_count() {
        let r = Reference {
            src: Source::K,
            hole_idx: 0,
            offset: 0,
            values_count: 2,
        };
        let value = Value::from_elems(vec![
            Elem::Word(Word::Int(1)),
            Elem::Reference(r),
            Elem::Word(Word::Int(3)),
        ]);

        let slice = value.slice(1, 2);
        assert_eq!(slice.summary().degree, 2);
        match slice.items() {
            [Elem::Reference(split_ref)] => {
                assert_eq!(split_ref.values_count, 2);
                assert_eq!(split_ref.offset, 0);
            }
            _ => panic!("unexpected slice"),
        }
    }
}
