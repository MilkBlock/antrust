use ant_runtime::dependency::{compose_step, value_match_pattern};
use ant_runtime::memo::{Memo, World};
use ant_runtime::pattern::{make_pvar, Pat, Pattern};
use ant_runtime::state::{Cek, Exp, Step};
use ant_runtime::value::{Elem, Value};
use ant_runtime::word::Word;
use ant_runtime::words::Words;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn exp() -> Exp {
    Exp { pc: 0 }
}

fn bench_words(c: &mut Criterion) {
    let parts: Vec<Words> = (0..256).map(|i| Words::from_int(i)).collect();
    let words = Words::appends(&parts);
    c.bench_function("words_pop_n_1", |b| b.iter(|| black_box(words.pop_n(1))));
    c.bench_function("words_splits", |b| b.iter(|| black_box(words.splits())));
}

fn bench_dependency(c: &mut Criterion) {
    let value_words = Words::appends(&[
        Words::from_int(1),
        Words::from_int(2),
        Words::from_int(3),
        Words::from_int(4),
    ]);
    let value = Value::from_words(&value_words);
    let pattern = Pattern::from_parts(vec![
        make_pvar(2),
        Pat::Con(Words::appends(&[Words::from_int(3), Words::from_int(4)])),
    ]);
    c.bench_function("dependency_value_match_pattern", |b| {
        b.iter(|| black_box(value_match_pattern(&value, &pattern)))
    });

    let step_x = Step {
        src: Cek {
            c: exp(),
            e: vec![],
            k: Pattern::from_parts(vec![Pat::Con(Words::from_int(1))]),
            sc: 0,
        },
        dst: Cek {
            c: exp(),
            e: vec![],
            k: Value::from_words(&Words::from_int(2)),
            sc: 0,
        },
        sc: 1,
    };
    let step_y = Step {
        src: Cek {
            c: exp(),
            e: vec![],
            k: Pattern::from_parts(vec![Pat::Con(Words::from_int(2))]),
            sc: 0,
        },
        dst: Cek {
            c: exp(),
            e: vec![],
            k: Value::from_words(&Words::from_int(3)),
            sc: 0,
        },
        sc: 1,
    };
    c.bench_function("dependency_compose_step", |b| {
        b.iter(|| black_box(compose_step(&step_x, &step_y)))
    });
}

fn bench_memo(c: &mut Criterion) {
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
        let (head, _) = world.resolve(ant_runtime::reference::Source::K);
        let next_val = match head {
            Word::Int(v) => v + 1,
            _ => 0,
        };
        world.state = Cek {
            c: exp(),
            e: vec![],
            k: Value::from_words(&Words::from_int(next_val)),
            sc: world.state.sc + 1,
        };
    };
    let is_done = |state: &Cek<Value>| match state.k.items() {
        [Elem::Word(Word::Int(v))] => *v >= 3,
        _ => true,
    };
    let start = Cek {
        c: exp(),
        e: vec![],
        k: Value::from_words(&Words::from_int(1)),
        sc: 0,
    };
    c.bench_function("memo_exec", |b| {
        b.iter(|| black_box(memo.exec(start.clone(), raw_step, is_done)))
    });
}

criterion_group!(benches, bench_words, bench_dependency, bench_memo);
criterion_main!(benches);
