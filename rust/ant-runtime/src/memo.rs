use crate::dependency::{can_step_through, compose_step, make_step, step_through};
use crate::reference::Source;
use crate::state::{cek_get, cek_get_mut, map_ek, Cek, State, Step};
use crate::value::{Elem, Value};
use crate::word::Word;

#[derive(Clone, Debug, Default)]
pub struct Memo {
    pub steps: Vec<Step>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecResult {
    pub state: State,
    pub step: i32,
    pub without_memo_step: i32,
}

#[derive(Clone, Debug)]
pub struct World {
    pub state: State,
    pub resolved: Cek<bool>,
}

impl World {
    pub fn new(state: State) -> Self {
        let resolved = map_ek(&state, |_| false);
        Self { state, resolved }
    }

    pub fn get_value(&self, src: Source) -> &Value {
        cek_get(&self.state, src)
    }

    pub fn set_value(&mut self, src: Source, value: Value) {
        *cek_get_mut(&mut self.state, src) = value;
    }

    pub fn mark_resolved(&mut self, src: Source) {
        *cek_get_mut(&mut self.resolved, src) = true;
    }

    pub fn resolve(&mut self, src: Source) -> (Word, Value) {
        self.mark_resolved(src);
        let value = self.get_value(src).clone();
        let (tail, head) = value.front_exn();
        match head {
            Elem::Word(word) => (word, tail),
            Elem::Reference(_) => panic!("cannot resolve reference"),
        }
    }
}

#[derive(Clone, Debug)]
struct Slice {
    state: State,
    step: Step,
}

#[derive(Clone, Debug)]
enum Digit<T> {
    Zero,
    One(T),
}

impl Memo {
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }

    pub fn record(&mut self, step: Step) {
        self.steps.push(step);
    }

    pub fn lookup_step(&self, state: &State) -> Option<Step> {
        self.steps
            .iter()
            .filter(|step| can_step_through(step, state))
            .max_by_key(|step| step.sc)
            .cloned()
    }

    fn compose_slice(&mut self, newer: Slice, older: Slice) -> Slice {
        let step = compose_step(&older.step, &newer.step);
        self.record(step.clone());
        Slice {
            state: older.state,
            step,
        }
    }

    fn inc_hist(&mut self, hist: &mut Vec<Digit<Slice>>, mut carry: Slice) {
        let mut idx = 0;
        loop {
            if idx == hist.len() {
                hist.push(Digit::One(carry));
                return;
            }
            match std::mem::replace(&mut hist[idx], Digit::Zero) {
                Digit::Zero => {
                    hist[idx] = Digit::One(carry);
                    return;
                }
                Digit::One(existing) => {
                    carry = self.compose_slice(carry, existing);
                    idx += 1;
                }
            }
        }
    }

    fn fold_hist(&mut self, hist: Vec<Digit<Slice>>) {
        let mut acc: Option<Slice> = None;
        for digit in hist {
            if let Digit::One(slice) = digit {
                acc = Some(match acc {
                    None => slice,
                    Some(acc_slice) => self.compose_slice(acc_slice, slice),
                });
            }
        }
    }

    pub fn exec<F, G>(&mut self, mut state: State, mut raw_step: F, mut is_done: G) -> ExecResult
    where
        F: FnMut(&mut World),
        G: FnMut(&State) -> bool,
    {
        let mut hist: Vec<Digit<Slice>> = Vec::new();
        let mut steps = 0;
        while !is_done(&state) {
            steps += 1;
            if let Some(step) = self.lookup_step(&state) {
                let slice = Slice {
                    state: state.clone(),
                    step: step.clone(),
                };
                self.inc_hist(&mut hist, slice);
                state = step_through(&step, &state);
            } else {
                let old = state.clone();
                let mut world = World::new(state);
                raw_step(&mut world);
                let raw_state = world.state.clone();
                let resolved = world.resolved.clone();
                let step = make_step(&old, &resolved, |s| {
                    let mut gen_world = World::new(s.clone());
                    raw_step(&mut gen_world);
                    gen_world.state
                });
                self.record(step.clone());
                let slice = Slice {
                    state: old.clone(),
                    step: step.clone(),
                };
                self.inc_hist(&mut hist, slice);
                let stepped = step_through(&step, &old);
                if stepped != raw_state {
                    panic!("memo step mismatch: {:?} vs {:?}", stepped, raw_state);
                }
                state = stepped;
            }
        }
        let without_memo_step = state.sc;
        self.fold_hist(hist);
        ExecResult {
            state,
            step: steps,
            without_memo_step,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pattern::{Pat, Pattern};
    use crate::state::{Cek, Exp};
    use crate::value::{Elem, Value};
    use crate::word::Word;
    use crate::words::Words;

    fn exp() -> Exp {
        Exp { pc: 0 }
    }

    fn value_int(i: i32) -> Value {
        Value::from_words(&Words::from_int(i))
    }

    fn state_with_int(i: i32, sc: i32) -> State {
        State {
            c: exp(),
            e: vec![],
            k: value_int(i),
            sc,
        }
    }

    fn state_with_env(k: i32, e0: i32, e1: i32, sc: i32) -> State {
        State {
            c: exp(),
            e: vec![value_int(e0), value_int(e1)],
            k: value_int(k),
            sc,
        }
    }

    fn state_int(state: &State) -> i32 {
        match state.k.items().first() {
            Some(Elem::Word(Word::Int(value))) => *value,
            _ => panic!("unexpected state value"),
        }
    }

    fn world_head_int(world: &mut World) -> i32 {
        let (head, _) = world.resolve(Source::K);
        match head {
            Word::Int(value) => value,
            _ => panic!("unexpected word"),
        }
    }

    #[test]
    fn memo_hit_matches_raw_steps() {
        let step = Step {
            src: Cek {
                c: exp(),
                e: vec![],
                k: Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]),
                sc: 0,
            },
            dst: Cek {
                c: exp(),
                e: vec![],
                k: Value::from_words(&Words::from_int(3)),
                sc: 0,
            },
            sc: 2,
        };
        let mut memo = Memo { steps: vec![step] };
        let raw_step = |world: &mut World| {
            let next_val = world_head_int(world) + 1;
            world.state = state_with_int(next_val, world.state.sc + 1);
        };
        let is_done = |state: &State| state_int(state) >= 3;

        let memo_end = memo.exec(state_with_int(1, 0), raw_step, is_done);

        let mut raw_state = state_with_int(1, 0);
        for _ in 0..2 {
            raw_state = {
                let next_val = state_int(&raw_state) + 1;
                state_with_int(next_val, raw_state.sc + 1)
            };
        }

        assert_eq!(memo_end.state, raw_state);
    }

    #[test]
    fn memo_falls_back_when_no_match() {
        let step = Step {
            src: Cek {
                c: exp(),
                e: vec![],
                k: Pattern::from_parts(vec![Pat::Con(Words::from_int(99))]),
                sc: 0,
            },
            dst: Cek {
                c: exp(),
                e: vec![],
                k: Value::from_words(&Words::from_int(100)),
                sc: 0,
            },
            sc: 1,
        };
        let mut memo = Memo { steps: vec![step] };
        let raw_step = |world: &mut World| {
            let next_val = world_head_int(world) + 1;
            world.state = state_with_int(next_val, world.state.sc + 1);
        };
        let is_done = |state: &State| state_int(state) >= 2;

        let end = memo.exec(state_with_int(1, 0), raw_step, is_done);
        assert_eq!(state_int(&end.state), 2);
        assert_eq!(end.state.sc, 1);
    }

    #[test]
    fn memo_exec_composes_steps() {
        let mut memo = Memo::new();
        let raw_step = |world: &mut World| {
            let next_val = world_head_int(world) + 1;
            world.state = state_with_int(next_val, world.state.sc + 1);
        };
        let is_done = |state: &State| state_int(state) >= 4;

        let first = memo.exec(state_with_int(0, 0), raw_step, is_done);
        assert_eq!(first.without_memo_step, 4);
        assert!(memo.steps.iter().any(|step| step.sc >= 2));

        let second = memo.exec(state_with_int(0, 0), raw_step, is_done);
        assert!(second.step < second.without_memo_step);
    }

    #[test]
    fn memo_tracks_resolved_slots() {
        let mut memo = Memo::new();
        let raw_step = |world: &mut World| {
            let (head, tail) = world.resolve(Source::K);
            let next_val = match head {
                Word::Int(v) => v + 1,
                _ => 0,
            };
            let mut items = Vec::new();
            items.extend_from_slice(tail.items());
            items.push(Elem::Word(Word::Int(next_val)));
            world.state = State {
                c: exp(),
                e: vec![],
                k: Value::from_elems(items),
                sc: world.state.sc + 1,
            };
        };
        let is_done = |state: &State| state_int(state) >= 2;

        let start_words = Words::appends(&[Words::from_int(1), Words::from_int(2)]);
        let start = State {
            c: exp(),
            e: vec![],
            k: Value::from_words(&start_words),
            sc: 0,
        };

        let _ = memo.exec(start, raw_step, is_done);

        let step = memo
            .steps
            .iter()
            .find(|step| step.sc == 1)
            .expect("expected recorded step");
        match step.src.k.parts() {
            [Pat::Con(words), Pat::Var(_)] => {
                assert_eq!(words.items(), &[Word::Int(1)]);
            }
            _ => panic!("expected resolved head pattern"),
        }
    }

    #[test]
    fn memo_exec_fast_forwards_with_env() {
        let mut memo = Memo::new();
        let raw_step = |world: &mut World| {
            let (k_word, _) = world.resolve(Source::K);
            let (e0_word, _) = world.resolve(Source::E(0));
            let k_next = match k_word {
                Word::Int(value) => value + 1,
                _ => 0,
            };
            let e0_next = match e0_word {
                Word::Int(value) => value + 2,
                _ => 0,
            };
            let e1 = world.get_value(Source::E(1)).clone();
            world.state = State {
                c: exp(),
                e: vec![value_int(e0_next), e1],
                k: value_int(k_next),
                sc: world.state.sc + 1,
            };
        };
        let is_done = |state: &State| state_int(state) >= 3;

        let first = memo.exec(state_with_env(0, 1, 5, 0), raw_step, is_done);
        let second = memo.exec(state_with_env(0, 1, 5, 0), raw_step, is_done);

        assert_eq!(first.state, second.state);
        assert!(second.step < second.without_memo_step);
    }
}
