use crate::words::Words;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Measure {
    pub degree: i32,
    pub max_degree: i32,
    pub hole_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    Var(i32),
    Con(Words),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Pattern {
    parts: Vec<Pat>,
}

pub fn make_pvar(n: i32) -> Pat {
    assert!(n > 0);
    Pat::Var(n)
}

fn pat_measure(p: &Pat) -> Measure {
    match p {
        Pat::Var(n) => Measure {
            degree: *n,
            max_degree: *n,
            hole_count: 1,
        },
        Pat::Con(c) => {
            let summary = c.summary();
            Measure {
                degree: summary.degree,
                max_degree: summary.max_degree,
                hole_count: 0,
            }
        }
    }
}

impl Pattern {
    pub fn empty() -> Self {
        Self { parts: Vec::new() }
    }

    pub fn from_parts(parts: Vec<Pat>) -> Self {
        Self { parts }
    }

    pub fn parts(&self) -> &[Pat] {
        &self.parts
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    pub fn front_exn(&self) -> (Pat, Pattern) {
        let (head, tail) = self
            .parts
            .split_first()
            .expect("pattern_front_exn on empty pattern");
        (head.clone(), Pattern::from_parts(tail.to_vec()))
    }

    pub fn rear_exn(&self) -> (Pattern, Pat) {
        let (last, rest) = self
            .parts
            .split_last()
            .expect("pattern_rear_exn on empty pattern");
        (Pattern::from_parts(rest.to_vec()), last.clone())
    }

    pub fn cons(p: Pat, q: &Pattern) -> Pattern {
        if q.is_empty() {
            return Pattern::from_parts(vec![p]);
        }
        let (qh, qt) = q.front_exn();
        match (p, qh) {
            (Pat::Var(pn), Pat::Var(qn)) => {
                let mut parts = vec![make_pvar(pn + qn)];
                parts.extend_from_slice(qt.parts());
                Pattern::from_parts(parts)
            }
            (Pat::Con(pw), Pat::Con(qw)) => {
                let mut parts = vec![Pat::Con(pw.append(&qw))];
                parts.extend_from_slice(qt.parts());
                Pattern::from_parts(parts)
            }
            (p, qh) => {
                let mut parts = vec![p, qh];
                parts.extend_from_slice(qt.parts());
                Pattern::from_parts(parts)
            }
        }
    }

    pub fn snoc(q: &Pattern, p: Pat) -> Pattern {
        if q.is_empty() {
            return Pattern::from_parts(vec![p]);
        }
        let (qh, qt) = q.rear_exn();
        match (qt, p) {
            (Pat::Var(qn), Pat::Var(pn)) => {
                let mut parts = qh.parts().to_vec();
                parts.push(make_pvar(qn + pn));
                Pattern::from_parts(parts)
            }
            (Pat::Con(qw), Pat::Con(pw)) => {
                let mut parts = qh.parts().to_vec();
                parts.push(Pat::Con(qw.append(&pw)));
                Pattern::from_parts(parts)
            }
            (qt, p) => {
                let mut parts = qh.parts().to_vec();
                parts.push(qt);
                parts.push(p);
                Pattern::from_parts(parts)
            }
        }
    }

    pub fn append_unsafe(x: &Pattern, y: &Pattern) -> Pattern {
        let mut parts = x.parts.clone();
        parts.extend_from_slice(y.parts());
        Pattern::from_parts(parts)
    }

    pub fn cons_unsafe(x: Pat, y: &Pattern) -> Pattern {
        let mut parts = vec![x];
        parts.extend_from_slice(y.parts());
        Pattern::from_parts(parts)
    }

    pub fn snoc_unsafe(x: &Pattern, y: Pat) -> Pattern {
        let mut parts = x.parts.clone();
        parts.push(y);
        Pattern::from_parts(parts)
    }

    pub fn append(x: &Pattern, y: &Pattern) -> Pattern {
        if x.is_empty() {
            return y.clone();
        }
        if y.is_empty() {
            return x.clone();
        }
        let (rest_x, last_x) = x.rear_exn();
        let (first_y, rest_y) = y.front_exn();
        let with_middle =
            |middle| Pattern::append_unsafe(&rest_x, &Pattern::cons_unsafe(middle, &rest_y));
        match (last_x, first_y) {
            (Pat::Var(n1), Pat::Var(n2)) => with_middle(make_pvar(n1 + n2)),
            (Pat::Con(c1), Pat::Con(c2)) => with_middle(Pat::Con(c1.append(&c2))),
            _ => Pattern::append_unsafe(x, y),
        }
    }

    pub fn measure(&self) -> Measure {
        let mut degree = 0;
        let mut max_degree = 0;
        let mut hole_count = 0;
        for pat in &self.parts {
            let pm = pat_measure(pat);
            max_degree = max_degree.max(degree + pm.max_degree);
            degree += pm.degree;
            hole_count += pm.hole_count;
        }
        Measure {
            degree,
            max_degree,
            hole_count,
        }
    }

    pub fn slice(&self, offset: i32) -> (Pattern, Pattern) {
        assert!(offset >= 0);
        let total = self.measure();
        if offset == 0 {
            return (Pattern::empty(), self.clone());
        }
        let mut degree = 0;
        let mut prefix = Vec::new();
        for (idx, pat) in self.parts.iter().enumerate() {
            let pm = pat_measure(pat);
            let candidate = degree + pm.max_degree;
            if candidate >= offset {
                let needed = offset - degree;
                assert!(needed > 0);
                match pat {
                    Pat::Var(n) => {
                        assert!(needed <= *n);
                        let left = Pattern::snoc_unsafe(&Pattern::from_parts(prefix), make_pvar(needed));
                        let mut right = Pattern::from_parts(self.parts[idx + 1..].to_vec());
                        if n - needed > 0 {
                            right = Pattern::cons_unsafe(make_pvar(n - needed), &right);
                        }
                        debug_assert_eq!(left.measure().degree, offset);
                        debug_assert_eq!(offset + right.measure().degree, total.degree);
                        return (left, right);
                    }
                    Pat::Con(c) => {
                        let (c_words, c_children) = c.slice_degree(needed);
                        let left = Pattern::snoc_unsafe(&Pattern::from_parts(prefix), Pat::Con(c_words));
                        let mut right = Pattern::from_parts(self.parts[idx + 1..].to_vec());
                        if !c_children.is_empty() {
                            right = Pattern::cons_unsafe(Pat::Con(c_children), &right);
                        }
                        debug_assert_eq!(left.measure().degree, offset);
                        debug_assert_eq!(offset + right.measure().degree, total.degree);
                        return (left, right);
                    }
                }
            }
            degree += pm.degree;
            prefix.push(pat.clone());
        }
        panic!("pattern_slice exceeded pattern degree");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cons_and_snoc_fuse() {
        let p = Pattern::from_parts(vec![make_pvar(2)]);
        let merged = Pattern::cons(make_pvar(1), &p);
        assert_eq!(merged.parts(), &[make_pvar(3)]);

        let merged = Pattern::snoc(&p, make_pvar(1));
        assert_eq!(merged.parts(), &[make_pvar(3)]);
    }

    #[test]
    fn append_fuses_concrete_segments() {
        let p1 = Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]);
        let p2 = Pattern::from_parts(vec![Pat::Con(Words::from_int(2))]);
        let merged = Pattern::append(&p1, &p2);
        assert_eq!(merged.parts().len(), 1);
        match &merged.parts()[0] {
            Pat::Con(words) => assert_eq!(words.length(), 2),
            _ => panic!("expected merged constructor words"),
        }
    }

    #[test]
    fn slice_inside_var() {
        let p = Pattern::from_parts(vec![make_pvar(3)]);
        let (left, right) = p.slice(1);
        assert_eq!(left.parts(), &[make_pvar(1)]);
        assert_eq!(right.parts(), &[make_pvar(2)]);
    }

    #[test]
    fn slice_inside_concrete() {
        let words = Words::appends(&[
            Words::from_int(1),
            Words::from_int(2),
            Words::from_int(3),
        ]);
        let p = Pattern::from_parts(vec![Pat::Con(words)]);
        let (left, right) = p.slice(2);
        match left.parts() {
            [Pat::Con(w)] => assert_eq!(w.length(), 2),
            _ => panic!("unexpected left slice"),
        }
        match right.parts() {
            [Pat::Con(w)] => assert_eq!(w.length(), 1),
            _ => panic!("unexpected right slice"),
        }
    }
}
