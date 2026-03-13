use crate::pattern::Pattern;
use crate::reference::Source;
use crate::value::Value;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exp {
    pub pc: i32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cek<T> {
    pub c: Exp,
    pub e: Vec<T>,
    pub k: T,
    pub sc: i32,
}

pub type State = Cek<Value>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub src: Cek<Pattern>,
    pub dst: Cek<Value>,
    pub sc: i32,
}

pub fn cek_get<T>(cek: &Cek<T>, src: Source) -> &T {
    match src {
        Source::E(i) => &cek.e[i],
        Source::K => &cek.k,
    }
}

pub fn cek_get_mut<T>(cek: &mut Cek<T>, src: Source) -> &mut T {
    match src {
        Source::E(i) => &mut cek.e[i],
        Source::K => &mut cek.k,
    }
}

pub fn fold_ek<T, Acc, F>(s: &Cek<T>, mut acc: Acc, mut f: F) -> Acc
where
    F: FnMut(Acc, &T) -> Acc,
{
    for v in &s.e {
        acc = f(acc, v);
    }
    f(acc, &s.k)
}

pub fn map_ek<A, B, F>(s: &Cek<A>, mut f: F) -> Cek<B>
where
    F: FnMut(&A) -> B,
{
    let e = s.e.iter().map(|v| f(v)).collect();
    let k = f(&s.k);
    Cek {
        c: s.c.clone(),
        e,
        k,
        sc: s.sc,
    }
}

pub fn maps_ek<A, B, F>(s: &Cek<A>, mut f: F) -> Cek<B>
where
    F: FnMut(&A, Source) -> B,
{
    let e = s
        .e
        .iter()
        .enumerate()
        .map(|(i, v)| f(v, Source::E(i)))
        .collect();
    let k = f(&s.k, Source::K);
    Cek {
        c: s.c.clone(),
        e,
        k,
        sc: s.sc,
    }
}

pub fn zip_ek<A, B>(s1: &Cek<A>, s2: &Cek<B>) -> Option<Cek<(A, B)>>
where
    A: Clone,
    B: Clone,
{
    if s1.e.len() != s2.e.len() {
        return None;
    }
    let e = s1
        .e
        .iter()
        .cloned()
        .zip(s2.e.iter().cloned())
        .collect();
    let k = (s1.k.clone(), s2.k.clone());
    Some(Cek {
        c: s1.c.clone(),
        e,
        k,
        sc: s1.sc,
    })
}

pub fn option_ek_to_ek_option<T: Clone>(s: &Cek<Option<T>>) -> Option<Cek<T>> {
    let mut e = Vec::with_capacity(s.e.len());
    for v in &s.e {
        match v {
            Some(value) => e.push(value.clone()),
            None => return None,
        }
    }
    let k = s.k.clone()?;
    Some(Cek {
        c: s.c.clone(),
        e,
        k,
        sc: s.sc,
    })
}

pub fn state_equal(x: &State, y: &State) -> bool {
    x.c.pc == y.c.pc && x.e == y.e && x.k == y.k
}
