# antrust

Rust implementation of the Ant toolchain (CLI, frontend, transforms, and runtime).

## Build & Test

```bash
cargo test --manifest-path rust/Cargo.toml -p ant-cli --test goldens
cargo test --manifest-path rust/Cargo.toml -p ant-runtime
```

## Run the CLI

```bash
cargo run --manifest-path rust/Cargo.toml -p ant-cli -- <INPUT.ant> <OUTPUT.txt> --print-ast
```

## Notes

- `rust/goldens/` contains byte-for-byte output snapshots captured from the upstream OCaml implementation.
- Regenerating goldens requires the OCaml toolchain from the original Ant repo.

