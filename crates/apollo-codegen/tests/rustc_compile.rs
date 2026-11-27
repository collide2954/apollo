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

        fn match(0 A: Type 0, 1 type: A) -> A {
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
