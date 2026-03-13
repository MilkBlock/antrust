use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::TempDir;

#[derive(Debug, Deserialize)]
struct Manifest {
    cases: Vec<GoldenCase>,
    errors: Vec<GoldenCase>,
}

#[derive(Debug, Deserialize)]
struct GoldenCase {
    name: String,
    input: String,
    args: Vec<String>,
    stdout: String,
    stderr: String,
    output: Option<String>,
    exit_code: i32,
    output_exists: bool,
}

fn repo_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("repo root")
        .to_path_buf()
}

fn read_bytes(path: &Path) -> Vec<u8> {
    fs::read(path).unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
}

fn is_supported(case: &GoldenCase) -> bool {
    if case.name == "unknown-flag"
        || case.name == "lexing-error"
        || case.name == "syntax-error"
        || case.name == "typing-error"
        || case.name == "typing-error-print-ast"
        || case.name == "compile-plain-error"
        || case.name == "compile-seq-error"
    {
        return true;
    }
    (case.args.len() == 1 && case.args[0] == "--print-ast")
        || (case.args.len() == 2
            && case.args[0] == "--print-ast"
            && case.args[1] == "--typing")
        || (case.args.len() == 1 && case.args[0] == "--pat")
        || (case.args.len() == 1 && case.args[0] == "--typing")
        || (case.args.len() == 2 && case.args[0] == "--typing" && case.args[1] == "-L")
        || (case.args.len() == 1 && case.args[0] == "--print-cps")
        || (case.args.len() == 2
            && case.args[0] == "--print-cps"
            && case.args[1] == "--typing")
        || (case.args.len() == 1 && case.args[0] == "--print-defunc")
        || (case.args.len() == 2
            && case.args[0] == "--print-defunc"
            && case.args[1] == "--typing")
        || (case.args.len() == 1 && case.args[0] == "--print-cps-defunc")
        || (case.args.len() == 1 && case.args[0] == "--compile")
        || (case.args.len() == 3
            && case.args[0] == "--compile"
            && case.args[1] == "-b"
            && case.args[2] == "plain")
        || (case.args.len() == 3
            && case.args[0] == "--compile"
            && case.args[1] == "-b"
            && case.args[2] == "seq")
        || (case.args.len() == 3
            && case.args[0] == "--compile"
            && case.args[1] == "-b"
            && case.args[2] == "memo")
}

#[test]
fn golden_parity() {
    let run_all = std::env::var("ANT_RUN_GOLDENS").map(|v| v == "1").unwrap_or(false);

    let root = repo_root();
    let manifest_path = root.join("rust/goldens/manifest.json");
    let manifest: Manifest = serde_json::from_slice(&read_bytes(&manifest_path))
        .unwrap_or_else(|err| panic!("failed to parse manifest: {err}"));

    let bin = env!("CARGO_BIN_EXE_ant-cli");
    let mut all_cases = Vec::new();
    all_cases.extend(manifest.cases);
    all_cases.extend(manifest.errors);

    for case in all_cases {
        if !run_all && !is_supported(&case) {
            continue;
        }

        let temp_dir = TempDir::new().expect("tempdir");
        let output_path = temp_dir.path().join("output.txt");

        let mut cmd = Command::new(bin);
        cmd.arg(root.join(&case.input));
        cmd.arg(&output_path);
        for arg in &case.args {
            cmd.arg(arg);
        }

        let output = cmd.output().unwrap_or_else(|err| {
            panic!("failed to run ant-cli for {}: {err}", case.name)
        });

        let status_code = output.status.code().unwrap_or(-1);
        assert_eq!(
            status_code, case.exit_code,
            "exit code mismatch for {}",
            case.name
        );

        let expected_stdout = read_bytes(&root.join(&case.stdout));
        let expected_stderr = read_bytes(&root.join(&case.stderr));
        assert_eq!(
            output.stdout, expected_stdout,
            "stdout mismatch for {}",
            case.name
        );
        assert_eq!(
            output.stderr, expected_stderr,
            "stderr mismatch for {}",
            case.name
        );

        if case.output_exists {
            assert!(output_path.exists(), "expected output file for {}", case.name);
            let expected_output = case
                .output
                .as_ref()
                .map(|path| read_bytes(&root.join(path)))
                .unwrap_or_default();
            let actual_output = read_bytes(&output_path);
            assert_eq!(
                actual_output, expected_output,
                "output file mismatch for {}",
                case.name
            );
        } else {
            assert!(
                !output_path.exists(),
                "unexpected output file for {}",
                case.name
            );
        }
    }
}
