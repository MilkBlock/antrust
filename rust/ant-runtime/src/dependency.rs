use crate::pattern::{make_pvar, Pat, Pattern};
use crate::reference::Source;
use crate::state::{
    cek_get, cek_get_mut, map_ek, maps_ek, option_ek_to_ek_option, zip_ek, Cek, State, Step,
};
use crate::value::{Elem, Value};
use crate::word::Word;
use crate::words::{hash_words, Words};

pub type PatternSubstMap = Vec<Pattern>;
pub type PatternSubstCek = Cek<PatternSubstMap>;
pub type ValueSubstMap = Vec<Value>;
pub type ValueSubstCek = Cek<ValueSubstMap>;

fn split_value_prefix(v: &Value, limit: usize) -> (Vec<Word>, Value, Value) {
    let mut words = Vec::new();
    let mut idx = 0;
    for (i, elem) in v.items().iter().enumerate() {
        match elem {
            Elem::Word(word) => {
                if words.len() == limit {
                    break;
                }
                words.push(word.clone());
                idx = i + 1;
            }
            Elem::Reference(_) => break,
        }
    }
    let prefix = Value::from_elems(v.items()[..idx].to_vec());
    let rest = Value::from_elems(v.items()[idx..].to_vec());
    (words, prefix, rest)
}

pub fn unify(x: &Pattern, y: &Pattern) -> Pattern {
    if x.is_empty() {
        assert!(y.is_empty());
        return Pattern::empty();
    }
    let (xh, xt) = x.front_exn();
    let (yh, yt) = y.front_exn();
    match (xh, yh) {
        (Pat::Var(xh), _) => {
            let (yl, yr) = y.slice(xh);
            Pattern::append(&yl, &unify(&xt, &yr))
        }
        (_, Pat::Var(yh)) => {
            let (xl, xr) = x.slice(yh);
            Pattern::append(&xl, &unify(&xr, &yt))
        }
        (Pat::Con(xh), Pat::Con(yh)) => {
            let xl = xh.length();
            let yl = yh.length();
            if xl < yl {
                let (yhh, yht) = yh.slice_length(xl);
                assert!(xh.equal(&yhh));
                Pattern::cons_unsafe(
                    Pat::Con(xh),
                    &unify(&xt, &Pattern::cons_unsafe(Pat::Con(yht), &yt)),
                )
            } else if xl > yl {
                let (xhh, xht) = xh.slice_length(yl);
                assert!(xhh.equal(&yh));
                Pattern::cons_unsafe(
                    Pat::Con(xhh),
                    &unify(&Pattern::cons_unsafe(Pat::Con(xht), &xt), &yt),
                )
            } else {
                assert!(xh.equal(&yh));
                Pattern::cons_unsafe(Pat::Con(xh), &unify(&xt, &yt))
            }
        }
    }
}

pub fn compose_pattern(p: &Pattern, s: &[Pattern]) -> Pattern {
    if p.is_empty() {
        if s.is_empty() {
            return Pattern::empty();
        }
        panic!("hole count mismatch");
    }
    let (ph, pt) = p.front_exn();
    match ph {
        Pat::Var(_) => match s.split_first() {
            Some((sh, st)) => Pattern::append(sh, &compose_pattern(&pt, st)),
            None => panic!("hole count mismatch"),
        },
        Pat::Con(ph) => Pattern::cons(Pat::Con(ph), &compose_pattern(&pt, s)),
    }
}

pub fn words_to_value(w: &Words) -> Value {
    Value::from_words(w)
}

fn pattern_to_value_aux(p: &Pattern, src: Source, hole_idx: usize) -> Value {
    if p.is_empty() {
        return Value::empty();
    }
    let (ph, pt) = p.front_exn();
    match ph {
        Pat::Var(n) => {
            let left = Value::from_elems(vec![Elem::Reference(crate::reference::Reference {
                src,
                hole_idx,
                offset: 0,
                values_count: n,
            })]);
            left.append(&pattern_to_value_aux(&pt, src, hole_idx + 1))
        }
        Pat::Con(c) => words_to_value(&c).append(&pattern_to_value_aux(&pt, src, hole_idx)),
    }
}

pub fn pattern_to_value(p: &Cek<Pattern>) -> Cek<Value> {
    maps_ek(p, |pat, src| pattern_to_value_aux(pat, src, 0))
}

pub fn value_match_pattern_aux(v: &Value, p: &Pattern) -> Option<Vec<Value>> {
    let v_summary = v.summary();
    let p_measure = p.measure();
    assert_eq!(v_summary.degree, p_measure.degree);
    assert_eq!(v_summary.degree, v_summary.max_degree);
    assert_eq!(p_measure.degree, p_measure.max_degree);
    if p.is_empty() {
        assert!(v.is_empty());
        return Some(Vec::new());
    }
    let (ph, pt) = p.front_exn();
    match ph {
        Pat::Var(ph) => {
            let (vh, vt) = v.pop_n(ph);
            let mut vs = value_match_pattern_aux(&vt, &pt)?;
            vs.insert(0, vh);
            Some(vs)
        }
        Pat::Con(ph) => {
            let pl = ph.length();
            let (words, _vh, vt) = split_value_prefix(v, pl);
            if words.len() < pl {
                return None;
            }
            let hash = hash_words(&words);
            if hash == ph.summary().hash {
                value_match_pattern_aux(&vt, &pt)
            } else {
                None
            }
        }
    }
}

pub fn value_match_pattern(v: &Value, p: &Pattern) -> Option<ValueSubstMap> {
    value_match_pattern_aux(v, p)
}

pub fn value_match_pattern_ek(v: &Cek<Value>, p: &Cek<Pattern>) -> Option<ValueSubstCek> {
    let vp = zip_ek(v, p)?;
    let mapped = map_ek(&vp, |(v, p)| value_match_pattern(v, p));
    option_ek_to_ek_option(&mapped)
}

pub fn subst_value(subst: &ValueSubstCek, v: &Value) -> Value {
    let mut items = Vec::new();
    for elem in v.items() {
        match elem {
            Elem::Word(word) => items.push(Elem::Word(word.clone())),
            Elem::Reference(reference) => {
                let sm = cek_get(subst, reference.src);
                let sub_v = &sm[reference.hole_idx];
                let slice = sub_v.slice(reference.offset, reference.values_count);
                items.extend(slice.items().iter().cloned());
            }
        }
    }
    Value::from_elems(items)
}

fn unify_vp_aux(v: &Value, p: &Pattern, s: &mut PatternSubstCek) {
    let v_summary = v.summary();
    let p_measure = p.measure();
    assert_eq!(v_summary.degree, p_measure.degree);
    assert_eq!(v_summary.degree, v_summary.max_degree);
    assert_eq!(p_measure.degree, p_measure.max_degree);
    if p.is_empty() {
        assert!(v.is_empty());
        return;
    }
    let (ph, pt) = p.front_exn();
    match ph {
        Pat::Var(ph) => {
            let (_vh, vt) = v.pop_n(ph);
            unify_vp_aux(&vt, &pt, s);
        }
        Pat::Con(ph) => {
            let pl = ph.length();
            let (words, _vh, vt) = split_value_prefix(v, pl);
            let prefix_len = words.len();
            let prefix_hash = hash_words(&words);
            if prefix_len == 0 {
                let (rest, head) = v.front_exn();
                match head {
                    Elem::Reference(r) => {
                        let (mut ph, pt) = p.slice(r.values_count);
                        let sm = cek_get_mut(s, r.src);
                        let unify_with = sm[r.hole_idx].clone();
                        if r.offset > 0 {
                            ph = Pattern::cons(make_pvar(r.offset), &ph);
                        }
                        let needed = unify_with.measure().max_degree - (r.offset + r.values_count);
                        assert!(needed >= 0);
                        if needed > 0 {
                            ph = Pattern::snoc(&ph, make_pvar(needed));
                        }
                        sm[r.hole_idx] = unify(&unify_with, &ph);
                        unify_vp_aux(&rest, &pt, s);
                    }
                    Elem::Word(_) => panic!("unexpected word at head for unify_vp_aux"),
                }
            } else if prefix_len < pl {
                let (phh, pht) = ph.slice_length(prefix_len);
                assert_eq!(prefix_hash, phh.summary().hash);
                let next = Pattern::cons_unsafe(Pat::Con(pht), &pt);
                unify_vp_aux(&vt, &next, s);
            } else {
                assert_eq!(prefix_hash, ph.summary().hash);
                unify_vp_aux(&vt, &pt, s);
            }
        }
    }
}

pub fn unify_vp(v: &Cek<Value>, p: &Cek<Pattern>, mut s: PatternSubstCek) -> PatternSubstCek {
    let vp = zip_ek(v, p).expect("unify_vp expects matching cek shapes");
    for (v, p) in &vp.e {
        unify_vp_aux(v, p, &mut s);
    }
    let (vk, pk) = &vp.k;
    unify_vp_aux(vk, pk, &mut s);
    s
}

pub fn can_step_through(step: &Step, state: &State) -> bool {
    step.src.c.pc == state.c.pc && value_match_pattern_ek(state, &step.src).is_some()
}

pub fn step_through(step: &Step, state: &State) -> State {
    assert!(step.src.c.pc == state.c.pc);
    let subst = value_match_pattern_ek(state, &step.src).expect("missing substitution");
    let mut next = map_ek(&step.dst, |v| subst_value(&subst, v));
    next.sc = state.sc + step.sc;
    next
}

fn pattern_to_subst_map(p: &Pattern) -> PatternSubstMap {
    let mut out = Vec::new();
    let mut cur = p.clone();
    while !cur.is_empty() {
        let (ph, pt) = cur.front_exn();
        if let Pat::Var(n) = ph {
            out.push(Pattern::from_parts(vec![make_pvar(n)]));
        }
        cur = pt;
    }
    out
}

pub fn compose_step(x: &Step, y: &Step) -> Step {
    assert!(x.dst.c.pc == y.src.c.pc);
    let s = unify_vp(&x.dst, &y.src, map_ek(&x.src, |p| pattern_to_subst_map(p)));
    let src = map_ek(
        &zip_ek(&x.src, &s).expect("compose_step zip"),
        |(p, s)| compose_pattern(p, s),
    );
    let mut dst = pattern_to_value(&src);
    dst.sc = 0;
    let dst = step_through(x, &dst);
    assert!(can_step_through(y, &dst));
    let dst = step_through(y, &dst);
    assert_eq!(dst.sc, x.sc + y.sc);
    let sc = dst.sc;
    Step { src, dst, sc }
}

pub fn make_step<F>(state: &State, resolved: &Cek<bool>, mut step_fn: F) -> Step
where
    F: FnMut(&State) -> State,
{
    let zipped = zip_ek(state, resolved).expect("make_step expects matching cek shapes");
    let src = map_ek(&zipped, |(v, resolved)| {
        let summary = v.summary();
        assert!(summary.degree > 0);
        if *resolved {
            let (vt, vh) = v.front_exn();
            match vh {
                Elem::Word(word) => {
                    let head = Words::from_word(word);
                    if vt.summary().degree == 0 {
                        Pattern::from_parts(vec![Pat::Con(head)])
                    } else {
                        Pattern::from_parts(vec![Pat::Con(head), make_pvar(vt.summary().degree)])
                    }
                }
                Elem::Reference(_) => panic!("cannot make step from unresolved reference"),
            }
        } else {
            Pattern::from_parts(vec![make_pvar(summary.degree)])
        }
    });

    let generalized = pattern_to_value(&src);
    let dst = step_fn(&generalized);
    Step { src, dst, sc: 1 }
}

pub fn value_equal(x: &Value, y: &Value) -> bool {
    x == y
}

pub fn state_equal(x: &State, y: &State) -> bool {
    crate::state::state_equal(x, y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::Source;
    use crate::state::Exp;

    fn exp() -> Exp {
        Exp { pc: 0 }
    }

    #[test]
    fn unify_var_with_concrete() {
        let p_var = Pattern::from_parts(vec![make_pvar(1), Pat::Con(Words::from_int(2))]);
        let p_con = Pattern::from_parts(vec![
            Pat::Con(Words::from_int(1)),
            Pat::Con(Words::from_int(2)),
        ]);
        let unified = unify(&p_var, &p_con);
        match unified.parts() {
            [Pat::Con(words)] => assert_eq!(words.length(), 2),
            _ => panic!("expected fused concrete pattern"),
        }
    }

    #[test]
    fn compose_pattern_fills_holes() {
        let p = Pattern::from_parts(vec![
            make_pvar(1),
            Pat::Con(Words::from_int(2)),
            make_pvar(1),
        ]);
        let s = vec![
            Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]),
            Pattern::from_parts(vec![Pat::Con(Words::from_int(3))]),
        ];
        let composed = compose_pattern(&p, &s);
        match composed.parts() {
            [Pat::Con(words)] => assert_eq!(words.length(), 3),
            _ => panic!("expected fused concrete pattern"),
        }
    }

    #[test]
    fn value_match_pattern_binds_holes() {
        let words = Words::appends(&[Words::from_int(1), Words::from_int(2)]);
        let value = Value::from_words(&words);
        let pattern =
            Pattern::from_parts(vec![make_pvar(1), Pat::Con(Words::from_int(2))]);
        let bindings = value_match_pattern(&value, &pattern).expect("match should succeed");
        assert_eq!(bindings.len(), 1);
        let expected = Value::from_words(&Words::from_int(1));
        assert_eq!(bindings[0], expected);
    }

    #[test]
    fn unify_vp_updates_reference_subst() {
        let value = Value::from_elems(vec![Elem::Reference(crate::reference::Reference {
            src: Source::K,
            hole_idx: 0,
            offset: 0,
            values_count: 1,
        })]);
        let pattern = Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]);
        let v = Cek {
            c: exp(),
            e: vec![],
            k: value,
            sc: 0,
        };
        let p = Cek {
            c: exp(),
            e: vec![],
            k: pattern,
            sc: 0,
        };
        let s = Cek {
            c: exp(),
            e: vec![],
            k: vec![Pattern::from_parts(vec![make_pvar(1)])],
            sc: 0,
        };
        let updated = unify_vp(&v, &p, s);
        match updated.k[0].parts() {
            [Pat::Con(words)] => assert_eq!(words.length(), 1),
            _ => panic!("expected reference hole to unify to concrete"),
        }
    }

    #[test]
    fn compose_step_chains_steps() {
        let src_pat = Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]);
        let dst_val = Value::from_words(&Words::from_int(2));
        let step_x = Step {
            src: Cek {
                c: exp(),
                e: vec![],
                k: src_pat.clone(),
                sc: 0,
            },
            dst: Cek {
                c: exp(),
                e: vec![],
                k: dst_val,
                sc: 0,
            },
            sc: 1,
        };

        let src_pat_y = Pattern::from_parts(vec![Pat::Con(Words::from_int(2))]);
        let dst_val_y = Value::from_words(&Words::from_int(3));
        let step_y = Step {
            src: Cek {
                c: exp(),
                e: vec![],
                k: src_pat_y,
                sc: 0,
            },
            dst: Cek {
                c: exp(),
                e: vec![],
                k: dst_val_y,
                sc: 0,
            },
            sc: 1,
        };

        let composed = compose_step(&step_x, &step_y);
        assert_eq!(composed.sc, 2);
        match composed.src.k.parts() {
            [Pat::Con(words)] => assert_eq!(words.length(), 1),
            _ => panic!("unexpected composed src"),
        }
        assert_eq!(composed.dst.k, Value::from_words(&Words::from_int(3)));
    }

    #[test]
    #[should_panic]
    fn compose_step_panics_on_mismatch() {
        let src_pat = Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]);
        let dst_val = Value::from_words(&Words::from_int(2));
        let step_x = Step {
            src: Cek {
                c: exp(),
                e: vec![],
                k: src_pat,
                sc: 0,
            },
            dst: Cek {
                c: exp(),
                e: vec![],
                k: dst_val,
                sc: 0,
            },
            sc: 1,
        };

        let src_pat_y = Pattern::from_parts(vec![Pat::Con(Words::from_int(99))]);
        let dst_val_y = Value::from_words(&Words::from_int(3));
        let step_y = Step {
            src: Cek {
                c: exp(),
                e: vec![],
                k: src_pat_y,
                sc: 0,
            },
            dst: Cek {
                c: exp(),
                e: vec![],
                k: dst_val_y,
                sc: 0,
            },
            sc: 1,
        };

        let _ = compose_step(&step_x, &step_y);
    }

    #[test]
    fn unify_vp_partial_prefix_updates_hole() {
        let value = Value::from_elems(vec![
            Elem::Word(Word::Int(1)),
            Elem::Reference(crate::reference::Reference {
                src: Source::K,
                hole_idx: 0,
                offset: 0,
                values_count: 1,
            }),
        ]);
        let pattern = Pattern::from_parts(vec![Pat::Con(Words::appends(&[
            Words::from_int(1),
            Words::from_int(2),
        ]))]);
        let v = Cek {
            c: exp(),
            e: vec![],
            k: value,
            sc: 0,
        };
        let p = Cek {
            c: exp(),
            e: vec![],
            k: pattern,
            sc: 0,
        };
        let s = Cek {
            c: exp(),
            e: vec![],
            k: vec![Pattern::from_parts(vec![make_pvar(1)])],
            sc: 0,
        };
        let updated = unify_vp(&v, &p, s);
        match updated.k[0].parts() {
            [Pat::Con(words)] => assert_eq!(words.length(), 1),
            _ => panic!("expected hole to unify via partial prefix"),
        }
    }

    #[test]
    fn value_match_pattern_fails_on_reference_prefix() {
        let value = Value::from_elems(vec![Elem::Reference(crate::reference::Reference {
            src: Source::K,
            hole_idx: 0,
            offset: 0,
            values_count: 2,
        })]);
        let pattern = Pattern::from_parts(vec![Pat::Con(Words::appends(&[
            Words::from_int(1),
            Words::from_int(2),
        ]))]);
        assert!(value_match_pattern(&value, &pattern).is_none());
    }

    #[test]
    fn make_step_resolved_and_unresolved() {
        let state = Cek {
            c: exp(),
            e: vec![],
            k: Value::from_words(&Words::appends(&[
                Words::from_int(1),
                Words::from_int(2),
            ])),
            sc: 0,
        };
        let resolved_true = Cek {
            c: exp(),
            e: vec![],
            k: true,
            sc: 0,
        };
        let resolved_false = Cek {
            c: exp(),
            e: vec![],
            k: false,
            sc: 0,
        };

        let step = make_step(&state, &resolved_true, |s| s.clone());
        match step.src.k.parts() {
            [Pat::Con(_), Pat::Var(n)] => assert_eq!(*n, 1),
            _ => panic!("expected resolved pattern with head + hole"),
        }
        match step.dst.k.items() {
            [Elem::Word(_), Elem::Reference(r)] => assert_eq!(r.values_count, 1),
            _ => panic!("expected generalized dst with trailing reference"),
        }

        let step = make_step(&state, &resolved_false, |s| s.clone());
        match step.src.k.parts() {
            [Pat::Var(n)] => assert_eq!(*n, 2),
            _ => panic!("expected unresolved pattern with single hole"),
        }
        match step.dst.k.items() {
            [Elem::Reference(r)] => assert_eq!(r.values_count, 2),
            _ => panic!("expected generalized dst with reference"),
        }
    }
}
