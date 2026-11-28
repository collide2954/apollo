use std::io::Write;
use std::process::{Command, Stdio};

#[test]
#[cfg_attr(miri, ignore)]
fn binary_checks_and_builds_apollo_from_stdin() {
    let bin = env!("CARGO_BIN_EXE_apollo-wasm");
    let src = "fn id(0 A: Type 0, 1 x: A) -> A { x }";

    let child = Command::new(bin)
        .arg("build")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .ok();
    assert!(child.is_some());
    if let Some(mut proc) = child {
        if let Some(mut stdin) = proc.stdin.take() {
            assert!(stdin.write_all(src.as_bytes()).is_ok());
        }
        let output = proc.wait_with_output().ok();
        assert!(output.is_some());
        if let Some(out) = output {
            assert!(out.status.success());
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(stdout.contains("\"ok\":true"));
            assert!(stdout.contains("pub fn id<A>(x: A) -> A"));
        }
    }
}
