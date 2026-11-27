use std::fs;
use std::io::Write;
use std::process::ExitCode;

pub fn run<I, S, W, E>(args: I, out: &mut W, err: &mut E) -> ExitCode
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
    W: Write,
    E: Write,
{
    let mut iter = args.into_iter();
    let _program = iter.next();
    match iter.next().as_ref().map(AsRef::as_ref) {
        None | Some("--help" | "-h" | "help") => {
            let _ = writeln!(out, "apollo {}", apollo_kernel::version());
            let _ = writeln!(out, "usage: apollo check <file.ap>");
            ExitCode::SUCCESS
        }
        Some("--version" | "-V" | "version") => {
            let _ = writeln!(out, "{}", apollo_kernel::version());
            ExitCode::SUCCESS
        }
        Some("check") => {
            let Some(path) = iter.next() else {
                let _ = writeln!(err, "usage: apollo check <file.ap>");
                return ExitCode::FAILURE;
            };
            check_path(path.as_ref(), out, err)
        }
        Some(other) => {
            let _ = writeln!(err, "unknown command: {other}");
            ExitCode::FAILURE
        }
    }
}

fn check_path<W: Write, E: Write>(path: &str, out: &mut W, err: &mut E) -> ExitCode {
    match fs::read_to_string(path) {
        Ok(source) => check_text(path, &source, out, err),
        Err(io_err) => {
            let _ = writeln!(err, "cannot read {path}: {io_err}");
            ExitCode::FAILURE
        }
    }
}

fn check_text<W: Write, E: Write>(path: &str, source: &str, out: &mut W, err: &mut E) -> ExitCode {
    match apollo_elab::check_source(source) {
        Ok(module) => {
            let count = module.decls.len();
            let noun = if count == 1 {
                "declaration"
            } else {
                "declarations"
            };
            let _ = writeln!(out, "checked {count} {noun} in {path}");
            ExitCode::SUCCESS
        }
        Err(elab_err) => {
            let _ = writeln!(err, "{}", elab_err.format_diagnostic(path, source));
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use std::process::ExitCode;

    use super::{check_text, run};

    #[test]
    fn help_prints_banner_and_succeeds() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "--help"], &mut out, &mut err);
        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(
            String::from_utf8_lossy(&out),
            format!(
                "apollo {}\nusage: apollo check <file.ap>\n",
                env!("CARGO_PKG_VERSION")
            )
        );
        assert_eq!(String::from_utf8_lossy(&err), "");
    }

    #[test]
    fn version_prints_kernel_version() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "--version"], &mut out, &mut err);
        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(
            String::from_utf8_lossy(&out),
            format!("{}\n", env!("CARGO_PKG_VERSION"))
        );
        assert_eq!(String::from_utf8_lossy(&err), "");
    }

    #[test]
    fn unknown_command_and_missing_check_path_fail() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "nope"], &mut out, &mut err);
        assert_eq!(code, ExitCode::FAILURE);
        assert_eq!(String::from_utf8_lossy(&out), "");
        assert_eq!(String::from_utf8_lossy(&err), "unknown command: nope\n");

        let mut out2 = Vec::new();
        let mut err2 = Vec::new();
        let code2 = run(["apollo", "check"], &mut out2, &mut err2);
        assert_eq!(code2, ExitCode::FAILURE);
        assert_eq!(String::from_utf8_lossy(&out2), "");
        assert_eq!(
            String::from_utf8_lossy(&err2),
            "usage: apollo check <file.ap>\n"
        );
    }

    #[test]
    fn check_text_reports_counts_and_diagnostics() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let single = "fn id(0 A: Type 0, 1 x: A) -> A { x }";
        let code = check_text("one.ap", single, &mut out, &mut err);
        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(
            String::from_utf8_lossy(&out),
            "checked 1 declaration in one.ap\n"
        );
        assert_eq!(String::from_utf8_lossy(&err), "");

        let mut out2 = Vec::new();
        let mut err2 = Vec::new();
        let multi = "fn a(0 A: Type 0, 1 x: A) -> A { x }\nfn b(0 A: Type 0, 1 x: A) -> A { x }";
        let code2 = check_text("two.ap", multi, &mut out2, &mut err2);
        assert_eq!(code2, ExitCode::SUCCESS);
        assert_eq!(
            String::from_utf8_lossy(&out2),
            "checked 2 declarations in two.ap\n"
        );
        assert_eq!(String::from_utf8_lossy(&err2), "");

        let mut out3 = Vec::new();
        let mut err3 = Vec::new();
        let bad = "fn bad(0 A: Type 0, 1 x: A) -> Sigma(1 _: A, A) { (x, x) }";
        let code3 = check_text("bad.ap", bad, &mut out3, &mut err3);
        assert_eq!(code3, ExitCode::FAILURE);
        assert_eq!(String::from_utf8_lossy(&out3), "");
        assert!(String::from_utf8_lossy(&err3).contains("bad.ap:1:1: error:"));
    }
}
