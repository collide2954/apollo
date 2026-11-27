use std::path::PathBuf;
use std::process::Command;

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

    let prelude = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("examples")
        .join("prelude.ap");
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
