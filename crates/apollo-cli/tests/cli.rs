use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn examples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("examples")
}

#[test]
#[cfg_attr(miri, ignore)]
fn binary_prints_version_checks_prelude_and_rejects_errors() {
    let bin = env!("CARGO_BIN_EXE_apollo");

    let ok = Command::new(bin).arg("--version").output();
    assert!(ok.is_ok());
    if let Ok(output) = ok {
        assert!(output.status.success());
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            format!("{}\n", env!("CARGO_PKG_VERSION"))
        );
    }

    let prelude = examples_dir().join("prelude.ap");
    let checked = Command::new(bin).arg("check").arg(&prelude).output();
    assert!(checked.is_ok());
    if let Ok(output) = checked {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("checked 9 declarations"));
    }

    let missing = Command::new(bin)
        .arg("check")
        .arg("nonexistent-apollo-file.ap")
        .output();
    assert!(missing.is_ok());
    if let Ok(output) = missing {
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("cannot read"));
    }

    let bad = Command::new(bin).arg("unknown-subcommand").output();
    assert!(bad.is_ok());
    if let Ok(output) = bad {
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("unknown command"));
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn binary_builds_extractable_example_to_valid_rust() {
    let bin = env!("CARGO_BIN_EXE_apollo");
    let extractable = examples_dir().join("extractable.ap");

    let stdout_build = Command::new(bin).arg("build").arg(&extractable).output();
    assert!(stdout_build.is_ok());
    if let Ok(output) = stdout_build {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let emitted = String::from_utf8_lossy(&output.stdout);
        assert!(emitted.contains("#![no_std]"));
        assert!(emitted.contains("pub fn dup<A: Clone>(x: A) -> (A, A)"));
    }

    let tmp_dir = std::env::temp_dir().join(format!("apollo-cli-build-{}", std::process::id()));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_rs = tmp_dir.join("extractable.rs");
    let out_rlib = tmp_dir.join("libextractable.rlib");

    let file_build = Command::new(bin)
        .arg("build")
        .arg(&extractable)
        .arg("-o")
        .arg(&out_rs)
        .output();
    assert!(file_build.is_ok());
    if let Ok(output) = file_build {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("wrote "));
    }

    let rustc = Command::new("rustc")
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "-D",
            "warnings",
            "--crate-name",
            "apollo_extractable",
            "-o",
        ])
        .arg(&out_rlib)
        .arg(&out_rs)
        .output();
    let _ = fs::remove_dir_all(&tmp_dir);

    assert!(rustc.is_ok());
    if let Ok(output) = rustc {
        assert!(
            output.status.success(),
            "rustc stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let missing_build = Command::new(bin)
        .arg("build")
        .arg("nonexistent-apollo-file.ap")
        .output();
    assert!(missing_build.is_ok());
    if let Ok(output) = missing_build {
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("cannot read"));
    }
}
