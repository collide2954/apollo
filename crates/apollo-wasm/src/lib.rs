use std::fmt::Write as _;
use std::io::{Read, Write};
use std::process::ExitCode;

use apollo_elab::{CheckedModule, ElabError, check_source};
use apollo_syntax::{DeclKind, line_col};

#[must_use]
pub const fn version() -> &'static str {
    apollo_kernel::version()
}

fn json_escape(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for ch in input.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c < '\u{20}' => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out
}

fn format_error_json(stage: &str, line: usize, column: usize, message: &str) -> String {
    format!(
        "{{\"ok\":false,\"version\":\"{}\",\"stage\":\"{}\",\"line\":{line},\"column\":{column},\"message\":\"{}\"}}",
        json_escape(version()),
        json_escape(stage),
        json_escape(message)
    )
}

fn format_elab_error_json(source: &str, err: &ElabError) -> String {
    let stage = if matches!(err, ElabError::Parse(_)) {
        "syntax"
    } else {
        "elab"
    };
    let loc = line_col(source, err.span().start);
    format_error_json(stage, loc.line, loc.col, &err.to_string())
}

fn module_counts(module: &CheckedModule) -> (usize, usize, usize) {
    let data_count = module.data_decls.len();
    let decl_count = module.decls.len();
    let theorem_count = module
        .decls
        .iter()
        .filter(|d| d.kind == DeclKind::Theorem)
        .count();
    (data_count, decl_count, theorem_count)
}

#[must_use]
pub fn check_source_json(source: &str) -> String {
    match check_source(source) {
        Ok(module) => {
            let (data_count, decl_count, theorem_count) = module_counts(&module);
            let decl_noun = if decl_count == 1 {
                "declaration"
            } else {
                "declarations"
            };
            let data_noun = if data_count == 1 {
                "data type"
            } else {
                "data types"
            };
            let msg = format!("checked {decl_count} {decl_noun} and {data_count} {data_noun}");
            format!(
                "{{\"ok\":true,\"version\":\"{}\",\"data_count\":{data_count},\"decl_count\":{decl_count},\"theorem_count\":{theorem_count},\"message\":\"{}\"}}",
                json_escape(version()),
                json_escape(&msg)
            )
        }
        Err(err) => format_elab_error_json(source, &err),
    }
}

#[must_use]
pub fn build_source_json(source: &str) -> String {
    let module = match check_source(source) {
        Ok(checked) => checked,
        Err(err) => return format_elab_error_json(source, &err),
    };
    let (data_count, decl_count, theorem_count) = module_counts(&module);
    match apollo_codegen::emit_module(&module) {
        Ok(rust) => format!(
            "{{\"ok\":true,\"version\":\"{}\",\"data_count\":{data_count},\"decl_count\":{decl_count},\"theorem_count\":{theorem_count},\"rust\":\"{}\"}}",
            json_escape(version()),
            json_escape(&rust)
        ),
        Err(err) => format_error_json("codegen", 1, 1, &err.to_string()),
    }
}

#[must_use]
pub fn run_command(cmd: &str, source: &str) -> String {
    match cmd {
        "check" => check_source_json(source),
        "build" => build_source_json(source),
        "version" => format!("{{\"ok\":true,\"version\":\"{}\"}}", json_escape(version())),
        other => format_error_json("cli", 1, 1, &format!("unknown command: {other}")),
    }
}

pub fn run_io<I, S, R, W>(args: I, reader: &mut R, writer: &mut W) -> ExitCode
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
    R: Read,
    W: Write,
{
    let mut iter = args.into_iter();
    let _program = iter.next();
    let cmd = iter
        .next()
        .map_or_else(|| "build".to_owned(), |s| s.as_ref().to_owned());
    let mut source = String::new();
    let output = if cmd == "version" {
        run_command("version", "")
    } else if let Err(io_err) = reader.read_to_string(&mut source) {
        let json = format_error_json("io", 1, 1, &io_err.to_string());
        let _ = writer.write_all(json.as_bytes());
        return ExitCode::FAILURE;
    } else {
        run_command(&cmd, &source)
    };
    if writer.write_all(output.as_bytes()).is_err() {
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use std::io::{self, Cursor, Read, Write};
    use std::process::ExitCode;

    use super::{build_source_json, check_source_json, json_escape, run_command, run_io, version};

    struct FailReader;

    impl Read for FailReader {
        fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
            Err(io::Error::other("read failed"))
        }
    }

    struct FailWriter;

    impl Write for FailWriter {
        fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
            Err(io::Error::other("write failed"))
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn reports_version_and_escapes_all_json_control_characters() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
        assert_eq!(
            json_escape("a\"b\\c\u{08}d\u{0c}e\nf\rg\th\u{00}\u{1f} "),
            "a\\\"b\\\\c\\bd\\fe\\nf\\rg\\th\\u0000\\u001f "
        );
        let ver = run_command("version", "");
        assert_eq!(
            ver,
            format!(
                "{{\"ok\":true,\"version\":\"{}\"}}",
                env!("CARGO_PKG_VERSION")
            )
        );
    }

    #[test]
    fn checks_and_builds_apollo_modules_to_structured_json() {
        let single = "enum Box1 { Mk(1 x: Nat) }\nfn id(0 A: Type 0, 1 x: A) -> A { x }";
        let checked_one = check_source_json(single);
        assert!(checked_one.contains("\"ok\":true"));
        assert!(checked_one.contains("\"data_count\":1"));
        assert!(checked_one.contains("\"decl_count\":1"));
        assert!(checked_one.contains("\"theorem_count\":0"));
        assert!(checked_one.contains("checked 1 declaration and 1 data type"));

        let multi = r"
            enum A { Mk }
            struct B { 1 x: Nat }
            fn f(1 n: Nat) -> Nat { n }
            fn g(1 n: Nat) -> Nat { n }
            theorem r(0 n: Nat) -> Path(_ => Nat, n, n) { <i> n }
        ";
        let checked_multi = check_source_json(multi);
        assert!(checked_multi.contains("\"data_count\":2"));
        assert!(checked_multi.contains("\"decl_count\":3"));
        assert!(checked_multi.contains("\"theorem_count\":1"));
        assert!(checked_multi.contains("checked 3 declarations and 2 data types"));

        let built = build_source_json(multi);
        assert!(built.contains("\"ok\":true"));
        assert!(built.contains("\"data_count\":2"));
        assert!(built.contains("\"decl_count\":3"));
        assert!(built.contains("\"theorem_count\":1"));
        assert!(built.contains("pub fn f(n: u128) -> u128"));
        assert!(!built.contains("pub fn r"));
    }

    #[test]
    fn reports_syntax_elab_codegen_and_cli_errors_as_json() {
        let syn_err = check_source_json("\nfn broken(");
        assert!(syn_err.contains("\"ok\":false"));
        assert!(syn_err.contains("\"stage\":\"syntax\""));
        assert!(syn_err.contains("\"line\":2"));

        let elab_err =
            build_source_json("fn bad(0 A: Type 0, 1 x: A) -> Sigma(1 _: A, A) { (x, x) }");
        assert!(elab_err.contains("\"ok\":false"));
        assert!(elab_err.contains("\"stage\":\"elab\""));
        assert!(elab_err.contains("\"line\":1"));
        assert!(elab_err.contains("\"column\":1"));

        let transport = "fn transport(0 A: Type 0, 0 B: Type 0, 0 p: Path(_ => Type 0, A, B), 1 x: A) -> B { coe(i => p @ i, 0, 1, x) }";
        let cg_err = build_source_json(transport);
        assert!(cg_err.contains("\"ok\":false"));
        assert!(cg_err.contains("\"stage\":\"codegen\""));

        let cli_err = run_command("nope", "");
        assert!(cli_err.contains("\"ok\":false"));
        assert!(cli_err.contains("\"stage\":\"cli\""));
        assert!(cli_err.contains("unknown command: nope"));
    }

    #[test]
    fn runs_io_dispatch_and_handles_reader_and_writer_errors() {
        let src = "fn id(0 A: Type 0, 1 x: A) -> A { x }";

        let mut out_default = Vec::new();
        let code_default = run_io(["apollo-wasm"], &mut Cursor::new(src), &mut out_default);
        assert_eq!(code_default, ExitCode::SUCCESS);
        assert!(String::from_utf8_lossy(&out_default).contains("pub fn id<A>(x: A) -> A"));

        let mut out_check = Vec::new();
        let code_check = run_io(
            ["apollo-wasm", "check"],
            &mut Cursor::new(src),
            &mut out_check,
        );
        assert_eq!(code_check, ExitCode::SUCCESS);
        assert!(String::from_utf8_lossy(&out_check).contains("checked 1 declaration"));

        let mut out_ver = Vec::new();
        let code_ver = run_io(["apollo-wasm", "version"], &mut FailReader, &mut out_ver);
        assert_eq!(code_ver, ExitCode::SUCCESS);
        assert!(String::from_utf8_lossy(&out_ver).contains(env!("CARGO_PKG_VERSION")));

        let mut out_read_err = Vec::new();
        let code_read_err = run_io(["apollo-wasm", "check"], &mut FailReader, &mut out_read_err);
        assert_eq!(code_read_err, ExitCode::FAILURE);
        assert!(String::from_utf8_lossy(&out_read_err).contains("\"stage\":\"io\""));

        let code_write_err = run_io(
            ["apollo-wasm", "version"],
            &mut Cursor::new(""),
            &mut FailWriter,
        );
        assert_eq!(code_write_err, ExitCode::FAILURE);
    }
}
