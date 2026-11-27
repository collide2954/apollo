use std::process::Command;

#[test]
#[cfg_attr(miri, ignore)]
fn binary_prints_version_and_rejects_unknown_command() {
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

    let bad = Command::new(bin).arg("unknown-subcommand").output();
    assert!(bad.is_ok());
    if let Ok(output) = bad {
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("unknown command"));
    }
}
