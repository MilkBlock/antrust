use ant_backend::{compile_memo, compile_plain, compile_seq, BackendError};
use ant_frontend::{parse_prog, pp_prog, resolve_globals};
use ant_transform::{cps_defunc_prog, cps_prog, defunc_prog, pat_output, TransformError};
use ant_typing::typing_output;
use std::env;
use std::fs;
use std::path::PathBuf;

const USAGE: &str = "Usage: ant [--help] [OPTION]… INPUT OUTPUT";

#[derive(Default)]
struct Options {
    print_ast: bool,
    compile_pat: bool,
    compile: bool,
    typing: bool,
    print_level: bool,
    print_cps: bool,
    print_defunc: bool,
    print_cps_defunc: bool,
    backend: Backend,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Backend {
    Memo,
    Seq,
    Plain,
}

impl Default for Backend {
    fn default() -> Self {
        Backend::Memo
    }
}

impl Backend {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "memo" => Some(Backend::Memo),
            "seq" => Some(Backend::Seq),
            "plain" => Some(Backend::Plain),
            _ => None,
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut options = Options::default();
    let mut positionals: Vec<String> = Vec::new();

    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg.starts_with('-') {
            match arg.as_str() {
                "-p" | "--print-ast" => options.print_ast = true,
                "--pat" | "--compile-pat" => options.compile_pat = true,
                "--compile" => options.compile = true,
                "-t" | "--typing" => options.typing = true,
                "-L" | "--print-level" => options.print_level = true,
                "-c" | "--print-cps" => options.print_cps = true,
                "-d" | "--print-defunc" => options.print_defunc = true,
                "-D" | "--print-cps-defunc" => options.print_cps_defunc = true,
                "-b" | "--backend" => {
                    let Some(value) = iter.next() else {
                        missing_backend_value();
                    };
                    options.backend = Backend::parse(value).unwrap_or_else(|| unknown_backend(value));
                }
                "--help" | "-h" => {
                    eprintln!("{USAGE}");
                    println!();
                    std::process::exit(0);
                }
                _ => {
                    unknown_option(arg);
                }
            }
        } else {
            positionals.push(arg.clone());
        }
    }

    if positionals.len() < 2 {
        eprintln!("{USAGE}");
        println!();
        std::process::exit(124);
    }

    let input = PathBuf::from(&positionals[0]);
    let output = PathBuf::from(&positionals[1]);

    let source = match fs::read_to_string(&input) {
        Ok(src) => src,
        Err(err) => {
            eprintln!("Failed to read input {}: {err}", input.display());
            std::process::exit(1);
        }
    };

    let prog = match parse_prog(&source) {
        Ok(prog) => prog,
        Err(err) => {
            eprintln!("{}", err.to_stderr());
            std::process::exit(1);
        }
    };
    let resolved = resolve_globals(prog);
    let typing_output_str = match typing_output(&resolved, options.print_level) {
        Ok(output) => output,
        Err(err) => {
            if let Some(message) = err.stdout_message() {
                print!("{message}");
            } else {
                eprintln!("{err}");
            }
            std::process::exit(1);
        }
    };

    let mut outputs = Vec::new();
    if options.print_ast {
        outputs.push(pp_prog(&resolved));
    }
    if options.compile_pat {
        outputs.push(pat_output(&resolved));
    }
    if options.compile {
        let compiled = match options.backend {
            Backend::Plain => compile_plain(&resolved),
            Backend::Seq => compile_seq(&resolved),
            Backend::Memo => compile_memo(&resolved),
        };
        match compiled {
            Ok(output) => outputs.push(output),
            Err(err) => compile_error(err),
        }
    }
    if options.typing {
        outputs.push(typing_output_str);
    }
    if options.print_cps {
        let cpsed = match cps_prog(&resolved) {
            Ok(prog) => prog,
            Err(err) => transform_error(err),
        };
        outputs.push(pp_prog(&cpsed));
    } else if options.print_defunc {
        let defunced = match defunc_prog(&resolved) {
            Ok(prog) => prog,
            Err(err) => transform_error(err),
        };
        outputs.push(pp_prog(&defunced));
    } else if options.print_cps_defunc {
        let defunced = match cps_defunc_prog(&resolved) {
            Ok(prog) => prog,
            Err(err) => transform_error(err),
        };
        outputs.push(pp_prog(&defunced));
    }
    let output_contents = if outputs.is_empty() {
        String::new()
    } else {
        outputs.join("")
    };

    if let Err(err) = fs::write(&output, output_contents) {
        eprintln!("Failed to write output {}: {err}", output.display());
        std::process::exit(1);
    }

    println!();
}

fn unknown_option(arg: &str) -> ! {
    eprintln!("{USAGE}");
    eprintln!("ant: unknown option '{arg}'");
    println!();
    std::process::exit(124);
}

fn missing_backend_value() -> ! {
    eprintln!("{USAGE}");
    eprintln!("ant: missing backend value");
    println!();
    std::process::exit(124);
}

fn unknown_backend(value: &str) -> ! {
    eprintln!("{USAGE}");
    eprintln!("ant: unknown backend '{value}'");
    println!();
    std::process::exit(124);
}

fn compile_error(err: BackendError) -> ! {
    eprintln!("ant: compile error: {err}");
    std::process::exit(1);
}

fn transform_error(err: TransformError) -> ! {
    eprintln!("ant: compile error: {err}");
    std::process::exit(1);
}
