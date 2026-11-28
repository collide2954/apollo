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

#[test]
#[cfg_attr(miri, ignore)]
fn binary_checks_and_builds_arithmetic_and_data_examples() {
    let bin = env!("CARGO_BIN_EXE_apollo");
    let arithmetic = examples_dir().join("arithmetic.ap");
    let arith_check = Command::new(bin).arg("check").arg(&arithmetic).output();
    assert!(arith_check.is_ok());
    if let Ok(output) = arith_check {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("checked 10 declarations"));
    }

    let arith_build = Command::new(bin).arg("build").arg(&arithmetic).output();
    assert!(arith_build.is_ok());
    if let Ok(output) = arith_build {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let emitted = String::from_utf8_lossy(&output.stdout);
        assert!(emitted.contains("pub fn mul(n: u128, m: u128) -> u128"));
        assert!(!emitted.contains("add_zero_right"));
    }

    let data_ap = examples_dir().join("data.ap");
    let data_check = Command::new(bin).arg("check").arg(&data_ap).output();
    assert!(data_check.is_ok());
    if let Ok(output) = data_check {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let data_build = Command::new(bin).arg("build").arg(&data_ap).output();
    assert!(data_build.is_ok());
    if let Ok(output) = data_build {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let emitted = String::from_utf8_lossy(&output.stdout);
        assert!(emitted.contains("pub enum List<A>"));
        assert!(emitted.contains("pub struct VerifiedNat"));
        assert!(!emitted.contains("append_nil_right"));
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn binary_checks_and_builds_auto_example() {
    let bin = env!("CARGO_BIN_EXE_apollo");
    let auto_ap = examples_dir().join("auto.ap");
    let check = Command::new(bin).arg("check").arg(&auto_ap).output();
    assert!(check.is_ok());
    if let Ok(output) = check {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("checked 8 declarations"));
    }

    let build = Command::new(bin).arg("build").arg(&auto_ap).output();
    assert!(build.is_ok());
    if let Ok(output) = build {
        assert!(
            output.status.success(),
            "stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let emitted = String::from_utf8_lossy(&output.stdout);
        assert!(emitted.contains("pub fn double(n: u128) -> u128"));
        assert!(emitted.contains("pub fn sum_with_proof(a: u128, b: u128) -> u128"));
        assert!(!emitted.contains("add_comm"));
        assert!(!emitted.contains("rewrite_under_map"));
    }
}
