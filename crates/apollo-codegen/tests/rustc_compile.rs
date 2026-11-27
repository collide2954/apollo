use std::fs;
use std::process::Command;

#[test]
#[cfg_attr(miri, ignore)]
fn extracted_rust_compiles_cleanly_with_rustc_deny_warnings() {
    let src = r"
        fn id(0 A: Type 0, 1 x: A) -> A {
            x
        }

        fn dup(0 A: Type 0, ω x: A) -> Sigma(1 _: A, A) {
            (x, x)
        }

        fn swap(0 A: Type 0, 0 B: Type 0, ω p: Sigma(1 _: A, B)) -> Sigma(1 _: B, A) {
            (p.1, p.0)
        }

        fn drop_second(0 A: Type 0, 0 B: Type 0, 1 x: A, ω y: B) -> A {
            x
        }

        fn apply(0 A: Type 0, 0 B: Type 0, 1 f: (1 _: A) -> B, 1 x: A) -> B {
            f(x)
        }

        fn twice(0 A: Type 0, ω f: (1 _: A) -> A, 1 x: A) -> A {
            f(f(x))
        }

        fn use_id(0 A: Type 0, 1 x: A) -> A {
            let 1 y: A = id(A, x);
            let 0 p: Path(_ => A, y, y) = <i> y;
            y
        }

        fn apply_id(0 A: Type 0, 1 x: A) -> A {
            apply(A, A, id(A), x)
        }

        fn const_fn(0 A: Type 0, 0 B: Type 0, 1 a: A) -> (ω _: B) -> A {
            |ω b| a
        }

        fn refine(0 A: Type 0, 1 x: A) -> Sigma(1 y: A, Path(_ => A, y, y)) {
            (x, <i> x)
        }

        fn unrefine(0 A: Type 0, 1 p: Sigma(1 y: A, Path(_ => A, y, y))) -> A {
            p.0
        }

        fn erased_first(0 A: Type 0, 0 x: A, 1 y: A) -> Sigma(0 _: Path(_ => A, x, x), A) {
            (<i> x, y)
        }

        fn project_erased_first(0 A: Type 0, 0 x: A, 1 p: Sigma(0 _: Path(_ => A, x, x), A)) -> A {
            p.1
        }

        fn coe_refl(0 A: Type 0, 1 x: A) -> A {
            coe(i => A, 0, 0, x)
        }

        fn hcom_top(0 A: Type 0, 1 x: A) -> A {
            hcom(A, 0, 1, [top => <j> x], x)
        }

        fn impl(0 A: Type 0, 1 type: A) -> A {
            type
        }

        theorem refl(0 A: Type 0, 0 x: A) -> Path(_ => A, x, x) {
            <i> x
        }
    ";

    let rust_code = apollo_codegen::compile_source(src);
    assert!(rust_code.is_ok(), "codegen failed: {:?}", rust_code.err());
    let Ok(code) = rust_code else {
        return;
    };

    let tmp_dir = std::env::temp_dir().join(format!("apollo-codegen-test-{}", std::process::id()));
    let _ = fs::create_dir_all(&tmp_dir);
    let rs_path = tmp_dir.join("extracted.rs");
    let rlib_path = tmp_dir.join("libextracted.rlib");
    assert!(fs::write(&rs_path, &code).is_ok());

    let output = Command::new("rustc")
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "-D",
            "warnings",
            "--crate-name",
            "apollo_extracted",
            "-o",
        ])
        .arg(&rlib_path)
        .arg(&rs_path)
        .output();

    let _ = fs::remove_dir_all(&tmp_dir);

    assert!(output.is_ok());
    if let Ok(res) = output {
        assert!(
            res.status.success(),
            "rustc rejected emitted code:\n{code}\nstderr:\n{}",
            String::from_utf8_lossy(&res.stderr)
        );
    }
}

const ARITH_SRC: &str = r"
    fn absurd(0 A: Type 0, 1 v: Void) -> A { match v {} }
    fn unit_id(1 u: Unit) -> Unit { match u { () => () } }
    fn not(1 b: Bool) -> Bool { match b { true => false, false => true } }
    fn and(1 a: Bool, ω b: Bool) -> Bool { match a { true => b, false => false } }
    fn choose(0 A: Type 0, 1 b: Bool, 1 x: A) -> A { match b { true => x, false => x } }
    theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
        match b as |x| Path(_ => Bool, not(not(x)), x) { true => <i> true, false => <i> false }
    }
    fn two() -> Nat { succ(succ(zero)) }
    fn pred(1 n: Nat) -> Nat { match n { zero => zero, succ(k) => k } }
    fn add(1 n: Nat, 1 m: Nat) -> Nat { match n { zero => m, succ(_, acc) => succ(acc) } }
    fn add_two(1 n: Nat) -> Nat { add(two, n) }
    theorem add_zero_right(0 n: Nat) -> Path(_ => Nat, add(n, zero), n) {
        match n as |x| Path(_ => Nat, add(x, zero), x) { zero => <i> zero, succ(k, ih) => <i> succ(ih @ i) }
    }
    fn mul(1 n: Nat, ω m: Nat) -> Nat { match n { zero => zero, succ(_, acc) => add(m, acc) } }
    fn repeat(0 A: Type 0, 1 n: Nat, ω x: A) -> A { match n { zero => x, succ(_, _) => x } }
    fn flip_n(0 A: Type 0, 1 n: Nat, 1 p: Sigma(1 _: A, A)) -> Sigma(1 _: A, A) {
        match n { zero => p, succ(_, acc) => (acc.1, acc.0) }
    }
";

const ARITH_DRIVER: &str = r#"
    fn main() {
        assert_eq!(apollo_arith::unit_id(()), ());
        assert!(!apollo_arith::not(true));
        assert!(apollo_arith::not(false));
        assert!(!apollo_arith::and(true, false));
        assert!(apollo_arith::and(true, true));
        assert_eq!(apollo_arith::choose(true, String::from("ok")), "ok");
        assert_eq!(apollo_arith::two(), 2);
        assert_eq!(apollo_arith::pred(0), 0);
        assert_eq!(apollo_arith::pred(5), 4);
        assert_eq!(apollo_arith::add(17, 25), 42);
        assert_eq!(apollo_arith::add_two(40), 42);
        assert_eq!(apollo_arith::mul(6, 7), 42);
        assert_eq!(apollo_arith::repeat(3, String::from("hi")), "hi");
        assert_eq!(
            apollo_arith::flip_n(3, (String::from("a"), String::from("b"))),
            (String::from("b"), String::from("a"))
        );
    }
"#;

#[test]
#[cfg_attr(miri, ignore)]
fn extracted_inductive_arithmetic_compiles_and_executes_correctly() {
    let rust_code = apollo_codegen::compile_source(ARITH_SRC);
    assert!(rust_code.is_ok(), "codegen failed: {:?}", rust_code.err());
    let Ok(code) = rust_code else {
        return;
    };

    let tmp_dir = std::env::temp_dir().join(format!("apollo-codegen-arith-{}", std::process::id()));
    let _ = fs::create_dir_all(&tmp_dir);
    let lib_rs = tmp_dir.join("arith.rs");
    let rlib_path = tmp_dir.join("libapollo_arith.rlib");
    let driver_rs = tmp_dir.join("driver.rs");
    let driver_exe = tmp_dir.join(if cfg!(windows) {
        "driver.exe"
    } else {
        "driver"
    });
    assert!(fs::write(&lib_rs, &code).is_ok());
    assert!(fs::write(&driver_rs, ARITH_DRIVER).is_ok());

    let lib_out = Command::new("rustc")
        .args([
            "--edition=2024",
            "--crate-type=lib",
            "-D",
            "warnings",
            "--crate-name",
            "apollo_arith",
            "-o",
        ])
        .arg(&rlib_path)
        .arg(&lib_rs)
        .output();
    assert!(lib_out.is_ok());
    if let Ok(res) = lib_out {
        assert!(
            res.status.success(),
            "rustc rejected arith lib:\n{code}\nstderr:\n{}",
            String::from_utf8_lossy(&res.stderr)
        );
    }

    let bin_out = Command::new("rustc")
        .args(["--edition=2024", "-D", "warnings", "--extern"])
        .arg(format!("apollo_arith={}", rlib_path.display()))
        .arg("-o")
        .arg(&driver_exe)
        .arg(&driver_rs)
        .output();
    assert!(bin_out.is_ok());
    if let Ok(res) = bin_out {
        assert!(
            res.status.success(),
            "rustc rejected driver:\n{}",
            String::from_utf8_lossy(&res.stderr)
        );
    }

    let run_out = Command::new(&driver_exe).output();
    let _ = fs::remove_dir_all(&tmp_dir);
    assert!(run_out.is_ok());
    if let Ok(res) = run_out {
        assert!(
            res.status.success(),
            "extracted arithmetic binary failed:\n{}",
            String::from_utf8_lossy(&res.stderr)
        );
    }
}
