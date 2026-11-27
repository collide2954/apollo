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
            let _ = writeln!(out, "       apollo build <file.ap> [-o <out.rs>]");
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
        Some("build") => {
            let Some(path) = iter.next() else {
                let _ = writeln!(err, "usage: apollo build <file.ap> [-o <out.rs>]");
                return ExitCode::FAILURE;
            };
            let output_path = match iter.next().as_ref().map(AsRef::as_ref) {
                None => None,
                Some("-o") => {
                    let Some(target) = iter.next() else {
                        let _ = writeln!(err, "usage: apollo build <file.ap> [-o <out.rs>]");
                        return ExitCode::FAILURE;
                    };
                    Some(target.as_ref().to_owned())
                }
                Some(_) => {
                    let _ = writeln!(err, "usage: apollo build <file.ap> [-o <out.rs>]");
                    return ExitCode::FAILURE;
                }
            };
            build_path(path.as_ref(), output_path.as_deref(), out, err)
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

fn build_path<W: Write, E: Write>(
    path: &str,
    output_path: Option<&str>,
    out: &mut W,
    err: &mut E,
) -> ExitCode {
    let source = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(io_err) => {
            let _ = writeln!(err, "cannot read {path}: {io_err}");
            return ExitCode::FAILURE;
        }
    };
    let Some(rust_code) = build_text(path, &source, err) else {
        return ExitCode::FAILURE;
    };
    if let Some(target) = output_path {
        if let Err(io_err) = fs::write(target, &rust_code) {
            let _ = writeln!(err, "cannot write {target}: {io_err}");
            return ExitCode::FAILURE;
        }
        let _ = writeln!(out, "wrote {target}");
    } else {
        let _ = write!(out, "{rust_code}");
    }
    ExitCode::SUCCESS
}

fn build_text<E: Write>(path: &str, source: &str, err: &mut E) -> Option<String> {
    let checked = match apollo_elab::check_source(source) {
        Ok(module) => module,
        Err(elab_err) => {
            let _ = writeln!(err, "{}", elab_err.format_diagnostic(path, source));
            return None;
        }
    };
    match apollo_codegen::emit_module(&checked) {
        Ok(code) => Some(code),
        Err(codegen_err) => {
            let _ = writeln!(err, "{path}: error: {codegen_err}");
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::process::ExitCode;

    use super::{build_text, check_text, run};

    #[test]
    fn help_prints_banner_and_succeeds() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "--help"], &mut out, &mut err);
        assert_eq!(code, ExitCode::SUCCESS);
        assert_eq!(
            String::from_utf8_lossy(&out),
            format!(
                "apollo {}\nusage: apollo check <file.ap>\n       apollo build <file.ap> [-o <out.rs>]\n",
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
    fn unknown_command_and_bad_usage_fail() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        let code = run(["apollo", "nope"], &mut out, &mut err);
        assert_eq!(code, ExitCode::FAILURE);
        assert_eq!(String::from_utf8_lossy(&out), "");
        assert_eq!(String::from_utf8_lossy(&err), "unknown command: nope\n");

        for args in [
            vec!["apollo", "check"],
            vec!["apollo", "build"],
            vec!["apollo", "build", "a.ap", "-o"],
            vec!["apollo", "build", "a.ap", "--bad"],
        ] {
            let mut o = Vec::new();
            let mut e = Vec::new();
            assert_eq!(run(args, &mut o, &mut e), ExitCode::FAILURE);
            assert!(String::from_utf8_lossy(&e).contains("usage: apollo"));
        }
    }

    #[test]
    fn check_and_build_text_report_results_and_diagnostics() {
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

        let mut b_err = Vec::new();
        let built = build_text("one.ap", single, &mut b_err);
        assert!(built.is_some());
        if let Some(rs) = built {
            assert!(rs.contains("pub fn id<A>(x: A) -> A"));
        }
        assert_eq!(String::from_utf8_lossy(&b_err), "");

        let mut bad_elab_err = Vec::new();
        assert!(build_text("bad.ap", bad, &mut bad_elab_err).is_none());
        assert!(String::from_utf8_lossy(&bad_elab_err).contains("bad.ap:1:1: error:"));

        let transport = "fn transport(0 A: Type 0, 0 B: Type 0, 0 p: Path(_ => Type 0, A, B), 1 x: A) -> B { coe(i => p @ i, 0, 1, x) }";
        let mut bad_cg_err = Vec::new();
        assert!(build_text("tr.ap", transport, &mut bad_cg_err).is_none());
        assert!(String::from_utf8_lossy(&bad_cg_err).contains("tr.ap: error:"));
    }
}
