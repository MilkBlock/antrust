use crate::word::Word;
use crc32c::crc32c_append;
use std::sync::{Mutex, OnceLock};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Summary {
    pub length: usize,
    pub degree: i32,
    pub max_degree: i32,
    pub hash: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Words {
    items: Vec<Word>,
}

static CONSTRUCTOR_DEGREES: OnceLock<Mutex<Vec<i32>>> = OnceLock::new();

fn degrees() -> &'static Mutex<Vec<i32>> {
    CONSTRUCTOR_DEGREES.get_or_init(|| Mutex::new(Vec::new()))
}

pub fn set_constructor_degree(ctag: i32, degree: i32) {
    let mut table = degrees().lock().expect("constructor degrees lock");
    let len = table.len() as i32;
    assert!(ctag == len, "constructor tag must be sequential");
    table.push(degree);
}

pub(crate) fn constructor_degree(ctag: i32) -> i32 {
    let table = degrees().lock().expect("constructor degrees lock");
    *table
        .get(ctag as usize)
        .unwrap_or_else(|| panic!("constructor degree missing for {ctag}"))
}

pub(crate) fn word_degree(word: &Word) -> i32 {
    match word {
        Word::Int(_) => 1,
        Word::ConstructorTag(tag) => constructor_degree(*tag),
    }
}

pub(crate) fn hash_word_seed(mut crc: u32, word: &Word) -> u32 {
    let (tag, value) = word.raw_repr();
    crc = crc32c_append(crc, &tag.to_ne_bytes());
    crc32c_append(crc, &value.to_ne_bytes())
}

pub(crate) fn hash_words(words: &[Word]) -> u32 {
    let mut crc = 0;
    for w in words {
        crc = hash_word_seed(crc, w);
    }
    crc
}

impl Words {
    pub fn empty() -> Self {
        Self { items: Vec::new() }
    }

    pub fn from_constructor(tag: i32) -> Self {
        Self {
            items: vec![Word::ConstructorTag(tag)],
        }
    }

    pub fn from_int(value: i32) -> Self {
        Self {
            items: vec![Word::Int(value)],
        }
    }

    pub fn from_word(word: Word) -> Self {
        match word {
            Word::Int(value) => Self::from_int(value),
            Word::ConstructorTag(tag) => Self::from_constructor(tag),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn items(&self) -> &[Word] {
        &self.items
    }

    pub fn to_word(&self) -> Word {
        assert!(self.items.len() == 1);
        self.items[0].clone()
    }

    pub fn summary(&self) -> Summary {
        let mut degree = 0;
        let mut max_degree = 0;
        for w in &self.items {
            degree += word_degree(w);
            if degree > max_degree {
                max_degree = degree;
            }
        }
        Summary {
            length: self.items.len(),
            degree,
            max_degree,
            hash: hash_words(&self.items),
        }
    }

    pub fn length(&self) -> usize {
        self.summary().length
    }

    pub fn degree(&self) -> i32 {
        self.summary().degree
    }

    pub fn max_degree(&self) -> i32 {
        self.summary().max_degree
    }

    pub fn append(&self, other: &Self) -> Self {
        let mut items = self.items.clone();
        items.extend_from_slice(&other.items);
        Self { items }
    }

    pub fn appends(words: &[Self]) -> Self {
        let mut items = Vec::new();
        for w in words {
            items.extend_from_slice(&w.items);
        }
        Self { items }
    }

    pub fn list_match(&self) -> Option<(Word, Self)> {
        let (head, tail) = self.items.split_first()?;
        Some((head.clone(), Self { items: tail.to_vec() }))
    }

    pub fn pop_n(&self, n: i32) -> (Self, Self) {
        assert!(n >= 0);
        if n == 0 {
            return (Self::empty(), self.clone());
        }
        let mut degree = 0;
        for (idx, w) in self.items.iter().enumerate() {
            degree += word_degree(w);
            if degree >= n {
                let left = Self {
                    items: self.items[..=idx].to_vec(),
                };
                let right = Self {
                    items: self.items[idx + 1..].to_vec(),
                };
                return (left, right);
            }
        }
        panic!("pop_n exceeded word degree");
    }

    pub fn slice_degree(&self, n: i32) -> (Self, Self) {
        self.pop_n(n)
    }

    pub fn slice_length(&self, len: usize) -> (Self, Self) {
        assert!(self.items.len() >= len);
        let left = Self {
            items: self.items[..len].to_vec(),
        };
        let right = Self {
            items: self.items[len..].to_vec(),
        };
        (left, right)
    }

    pub fn equal(&self, other: &Self) -> bool {
        self.summary().hash == other.summary().hash
    }

    pub fn splits(&self) -> Vec<Self> {
        let mut remaining = self.clone();
        let mut out = Vec::new();
        while !remaining.is_empty() {
            let (head, tail) = remaining.pop_n(1);
            out.push(head);
            remaining = tail;
        }
        out
    }
}

#[cfg(test)]
pub(crate) fn reset_constructor_degrees_for_test() {
    let mut table = degrees().lock().expect("constructor degrees lock");
    table.clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn words_summary_and_pop() {
        reset_constructor_degrees_for_test();
        set_constructor_degree(0, 0);
        set_constructor_degree(1, -1);

        let node = Words::from_constructor(1);
        let leaf = Words::from_constructor(0);
        let w = Words::appends(&[
            node.clone(),
            leaf.clone(),
            Words::from_int(1),
            leaf.clone(),
            Words::from_int(2),
        ]);

        let summary = w.summary();
        assert_eq!(summary.length, 5);
        assert_eq!(summary.degree, 1);
        assert_eq!(summary.max_degree, 1);

        let (left, right) = w.pop_n(1);
        assert!(right.is_empty());
        assert_eq!(left.summary().degree, 1);

        let (l2, r2) = left.slice_length(2);
        assert_eq!(l2.length(), 2);
        assert_eq!(r2.length(), 3);
        assert!(left.equal(&left.clone()));
    }
}
