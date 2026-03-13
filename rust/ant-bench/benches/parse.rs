use ant_frontend::parse_prog;
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_parse(c: &mut Criterion) {
    let source = include_str!("../../../examples/Test.ant");
    c.bench_function("parse_test", |b| {
        b.iter(|| {
            let _ = parse_prog(source).expect("parse");
        })
    });
}

criterion_group!(benches, bench_parse);
criterion_main!(benches);
