use ant_runtime::memo::{ExecResult, Memo, World};
use ant_runtime::reference::Source;
use ant_runtime::state::{Exp, State};
use ant_runtime::value::{Elem, Value};
use ant_runtime::word::Word;
use ant_runtime::words::{set_constructor_degree, Words};
use std::path::PathBuf;
use std::sync::Once;

const LIMIT: i32 = 4;

fn init_constructor_degrees() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        set_constructor_degree(0, 1);
    });
}

fn env_value(head: i32, tail: i32) -> Value {
    Value::from_words(&Words::appends(&[Words::from_int(head), Words::from_int(tail)]))
}

fn is_done(state: &State) -> bool {
    state.c.pc == 0
        && matches!(
            state.k.items().first(),
            Some(Elem::Word(Word::ConstructorTag(0)))
        )
}

fn exec_case(memo: &mut Memo, head: i32, tail: i32) -> ExecResult {
    let raw_step = |world: &mut World| {
        let (head_word, tail_value) = world.resolve(Source::E(0));
        let next_head = match head_word {
            Word::Int(value) => value + 1,
            Word::ConstructorTag(_) => panic!("unexpected constructor tag in env value"),
        };

        let mut items = Vec::with_capacity(1 + tail_value.items().len());
        items.push(Elem::Word(Word::Int(next_head)));
        items.extend_from_slice(tail_value.items());
        world.set_value(Source::E(0), Value::from_elems(items));

        if world.state.sc == LIMIT - 1 {
            world.state.k = Value::from_words(&Words::from_constructor(0));
        }
        world.state.sc += 1;
    };

    let state = State {
        c: Exp { pc: 0 },
        e: vec![env_value(head, tail)],
        k: Value::from_words(&Words::from_int(0)),
        sc: 0,
    };

    memo.exec(state, raw_step, is_done)
}

fn render(result: &ExecResult) -> String {
    format!(
        "took {} step, but without memo take {} step.\n",
        result.step, result.without_memo_step
    )
}

#[test]
fn memo_exec_matches_ocaml_golden() {
    init_constructor_degrees();
    let mut memo = Memo::new();

    let mut actual = String::new();
    actual.push_str("# seed\n");
    actual.push_str(&render(&exec_case(&mut memo, 0, 10)));
    actual.push_str("# repeat\n");
    actual.push_str(&render(&exec_case(&mut memo, 0, 10)));
    actual.push_str("# shared-prefix\n");
    actual.push_str(&render(&exec_case(&mut memo, 0, 99)));
    actual.push_str("# fallback\n");
    actual.push_str(&render(&exec_case(&mut memo, 99, 10)));

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let golden_path = manifest_dir.join("../goldens/runtime/memo_parity.stdout");
    let expected = std::fs::read_to_string(&golden_path)
        .unwrap_or_else(|err| panic!("Failed to read {}: {err}", golden_path.display()));

    assert_eq!(actual, expected);
}

