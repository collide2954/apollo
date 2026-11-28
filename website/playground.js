import { runApolloWasm } from "./wasi-runner.js";

export const PRESETS = {
  identity: {
    label: "Identity and Erasure",
    code: `fn id(0 A: Type 0, 1 x: A) -> A {
    x
}

fn const_fn(0 A: Type 0, 0 B: Type 0, 1 x: A, ω y: B) -> A {
    x
}

fn dup(0 A: Type 0, ω x: A) -> Sigma(1 _: A, A) {
    (x, x)
}
`,
  },
  arithmetic: {
    label: "Verified Arithmetic and Erased Proof",
    code: `fn add(1 n: Nat, 1 m: Nat) -> Nat {
    match n {
        zero => m,
        succ(_, acc) => succ(acc),
    }
}

theorem add_zero_right(0 n: Nat) -> Path(_ => Nat, add(n, zero), n) {
    match n as |k| Path(_ => Nat, add(k, zero), k) {
        zero => <i> zero,
        succ(_, ih) => <i> succ(ih @ i),
    }
}

fn double(ω n: Nat) -> Nat {
    add(n, n)
}
`,
  },
  adts: {
    label: "Custom ADTs, Proof Fields, and List",
    code: `enum Option(0 A: Type 0) {
    None,
    Some(1 val: A),
}

struct VerifiedNat {
    1 val: Nat,
    0 ok: Path(_ => Nat, val, val),
}

enum List(0 A: Type 0) {
    Nil,
    Cons(1 head: A, 1 tail: List(A)),
}

fn unwrap_or(0 A: Type 0, 1 o: Option(A), ω d: A) -> A {
    match o {
        Option::None => d,
        Option::Some(v) => v,
    }
}

fn mk_verified(1 n: Nat) -> VerifiedNat {
    VerifiedNat { val: n, ok: <i> n }
}

fn append(0 A: Type 0, 1 xs: List(A), ω ys: List(A)) -> List(A) {
    match xs {
        List::Nil => ys,
        List::Cons(h, _, ih) => List::Cons(h, ih),
    }
}
`,
  },
  linearError: {
    label: "QTT Linear Ownership Error",
    code: `// Linear values (multiplicity 1) cannot duplicate.
// Change "1 x: A" to "ω x: A" to fix this error.
fn bad_dup(0 A: Type 0, 1 x: A) -> Sigma(1 _: A, A) {
    (x, x)
}
`,
  },
  universeGuard: {
    label: "Universe Hierarchy and Erasure",
    code: `// Storing a Type 0 field requires the struct to live in Type 1.
// Try removing ": Type 1" to watch the kernel reject it.
struct BoxedType : Type 1 {
    0 T: Type 0,
    1 count: Nat,
}

fn mk_box(1 n: Nat) -> BoxedType {
    BoxedType { T: Nat, count: n }
}
`,
  },
  univalence: {
    label: "Computational Univalence (V-types and ua)",
    code: `fn not(1 b: Bool) -> Bool {
    match b {
        true => false,
        false => true,
    }
}

theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
    match b as |x| Path(_ => Bool, not(not(x)), x) {
        true => <i> true,
        false => <i> false,
    }
}

theorem Equiv(0 A: Type 0, 0 B: Type 0) -> Type 0 {
    Sigma(0 f: (1 _: A) -> B, Sigma(0 g: (1 _: B) -> A, Sigma(0 sec: (0 b: B) -> Path(_ => B, f(g(b)), b), (0 a: A) -> Path(_ => A, g(f(a)), a))))
}

theorem not_equiv() -> Equiv(Bool, Bool) {
    (not, (not, (not_not, not_not)))
}

theorem ua(0 A: Type 0, 0 B: Type 0, 0 e: Equiv(A, B)) -> Path(_ => Type 0, A, B) {
    <i> V(i, A, B, e)
}

theorem bool_flip() -> Path(_ => Type 0, Bool, Bool) {
    ua(Bool, Bool, not_equiv)
}

// Transporting across the Univalence path computes to zero-overhead Rust!
fn flip_via_univalence(1 b: Bool) -> Bool {
    coe(i => bool_flip @ i, 0, 1, b)
}
`,
  },
  hits: {
    label: "Higher Inductive Types (S1 and UPair)",
    code: `// The Circle S1 as a Higher Inductive Type
enum S1 {
    Base,
    Loop(<i>) = S1::Base .. S1::Base,
}

fn not(1 b: Bool) -> Bool {
    match b { true => false, false => true }
}

theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
    match b as |x| Path(_ => Bool, not(not(x)), x) {
        true => <i> true,
        false => <i> false,
    }
}

theorem Equiv(0 A: Type 0, 0 B: Type 0) -> Type 0 {
    Sigma(0 f: (1 _: A) -> B, Sigma(0 g: (1 _: B) -> A, Sigma(0 sec: (0 b: B) -> Path(_ => B, f(g(b)), b), (0 a: A) -> Path(_ => A, g(f(a)), a))))
}

theorem not_equiv() -> Equiv(Bool, Bool) {
    (not, (not, (not_not, not_not)))
}

// Double cover of S1 via Univalence: transporting true around Loop yields false!
theorem double_cover(1 x: S1) -> Type 0 {
    match x as |_| Type 0 {
        S1::Base => Bool,
        S1::Loop(i) => V(i, Bool, Bool, not_equiv),
    }
}

theorem loop_flips_true() -> Path(_ => Bool, coe(i => double_cover(S1::Loop(i)), 0, 1, true), false) {
    <i> false
}

// Unordered pair quotient: every match must prove symmetry!
enum UPair(0 A: Type 0) {
    Pair(1 a: A, 1 b: A),
    Swap(1 a: A, 1 b: A, <i>) = UPair::Pair(a, b) .. UPair::Pair(b, a),
}

fn add(1 a: Nat, 1 b: Nat) -> Nat {
    match a { zero => b, succ(_, ih) => succ(ih) }
}

theorem add_zero_right(0 n: Nat) -> Path(_ => Nat, add(n, zero), n) {
    match n as |k| Path(_ => Nat, add(k, zero), k) {
        zero => <i> zero,
        succ(_, ih) => <i> succ(ih @ i),
    }
}

theorem add_succ_right(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, add(a, succ(b)), succ(add(a, b))) {
    match a as |k| Path(_ => Nat, add(k, succ(b)), succ(add(k, b))) {
        zero => <i> succ(b),
        succ(_, ih) => <i> succ(ih @ i),
    }
}

theorem sym(0 A: Type 0, 0 x: A, 0 y: A, 0 p: Path(_ => A, x, y)) -> Path(_ => A, y, x) {
    <i> hcom(A, 0, 1, [i = 0 => <j> p @ j, i = 1 => <j> x], x)
}

theorem trans(0 A: Type 0, 0 x: A, 0 y: A, 0 z: A, 0 p: Path(_ => A, x, y), 0 q: Path(_ => A, y, z)) -> Path(_ => A, x, z) {
    <i> hcom(A, 0, 1, [i = 0 => <j> x, i = 1 => <j> q @ j], p @ i)
}

theorem add_comm(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, add(a, b), add(b, a)) {
    match a as |k| Path(_ => Nat, add(k, b), add(b, k)) {
        zero => sym(Nat, add(b, zero), b, add_zero_right(b)),
        succ(k, ih) => trans(Nat, succ(add(k, b)), succ(add(b, k)), add(b, succ(k)), <i> succ(ih @ i), sym(Nat, add(b, succ(k)), succ(add(b, k)), add_succ_right(b, k))),
    }
}

fn sum_upair(1 p: UPair(Nat)) -> Nat {
    match p {
        UPair::Pair(a, b) => add(a, b),
        UPair::Swap(a, b, i) => add_comm(a, b) @ i,
    }
}
`,
  },
};

function encodeBase64Url(text) {
  const raw = new TextEncoder().encode(text);
  let bin = "";
  for (const b of raw) {
    bin += String.fromCharCode(b);
  }
  return btoa(bin).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/g, "");
}

function decodeBase64Url(encoded) {
  const padded = encoded.replace(/-/g, "+").replace(/_/g, "/");
  const mod = padded.length % 4;
  const full = mod === 0 ? padded : padded + "=".repeat(4 - mod);
  const bin = atob(full);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i += 1) {
    bytes[i] = bin.charCodeAt(i);
  }
  return new TextDecoder("utf-8").decode(bytes);
}

async function loadWasmModule(url) {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`HTTP ${response.status} while loading ${url}`);
  }
  if (typeof WebAssembly.compileStreaming === "function") {
    try {
      return await WebAssembly.compileStreaming(response.clone());
    } catch {
      // Fallback when local servers serve .wasm without application/wasm MIME type.
    }
  }
  const buffer = await response.arrayBuffer();
  return WebAssembly.compile(buffer);
}

function readInitialSource() {
  const params = new URLSearchParams(window.location.search);
  const codeParam = params.get("code");
  if (codeParam) {
    try {
      return decodeBase64Url(codeParam);
    } catch {
      // Ignore malformed share parameter and fall back to preset.
    }
  }
  const hash = window.location.hash || "";
  if (hash.startsWith("#code=")) {
    try {
      return decodeBase64Url(hash.slice("#code=".length));
    } catch {
      // Ignore malformed hash code and fall back to preset.
    }
  }
  const presetKey = params.get("example");
  if (presetKey && PRESETS[presetKey]) {
    return PRESETS[presetKey].code;
  }
  return PRESETS.arithmetic.code;
}

function initPlayground() {
  const shell = document.querySelector(".pg-shell");
  const editor = document.getElementById("pg-source");
  const output = document.getElementById("pg-output");
  const status = document.getElementById("pg-status");
  const meta = document.getElementById("pg-meta");
  const presetSelect = document.getElementById("pg-preset");
  const checkBtn = document.getElementById("pg-check");
  const buildBtn = document.getElementById("pg-build");
  const omegaBtn = document.getElementById("pg-omega");
  const copyBtn = document.getElementById("pg-copy");
  const shareBtn = document.getElementById("pg-share");
  const tabEditor = document.getElementById("pg-tab-editor");
  const tabOutput = document.getElementById("pg-tab-output");
  const tabDot = document.getElementById("pg-tab-dot");

  if (!editor || !output || !status || !meta || !presetSelect) {
    return;
  }

  function setMobileTab(tabName) {
    if (!shell || !tabEditor || !tabOutput) {
      return;
    }
    shell.dataset.mobileTab = tabName;
    const isEditor = tabName === "editor";
    tabEditor.classList.toggle("active", isEditor);
    tabEditor.setAttribute("aria-selected", String(isEditor));
    tabOutput.classList.toggle("active", !isEditor);
    tabOutput.setAttribute("aria-selected", String(!isEditor));
  }

  if (tabEditor && tabOutput) {
    tabEditor.addEventListener("click", () => setMobileTab("editor"));
    tabOutput.addEventListener("click", () => setMobileTab("output"));
  }

  for (const [key, preset] of Object.entries(PRESETS)) {
    const opt = document.createElement("option");
    opt.value = key;
    opt.textContent = preset.label;
    presetSelect.appendChild(opt);
  }
  const initialPreset = new URLSearchParams(window.location.search).get("example");
  presetSelect.value = initialPreset && PRESETS[initialPreset] ? initialPreset : "arithmetic";
  editor.value = readInitialSource();

  let wasmModule = null;
  let lastRust = "";

  function setStatus(kind, label, detail) {
    status.className = `pg-badge ${kind}`;
    status.textContent = label;
    if (tabDot) {
      tabDot.className = `pg-dot ${kind}`;
    }
    meta.textContent = detail;
  }

  function execute(command, switchTab = false) {
    if (!wasmModule) {
      setStatus("loading", "LOADING WASM", "Wait for the Apollo WebAssembly module to finish loading.");
      return;
    }
    const started = performance.now();
    try {
      const res = runApolloWasm(wasmModule, command, editor.value);
      const elapsed = Math.max(0.1, performance.now() - started).toFixed(1);
      if (res.ok) {
        const summary = `${res.decl_count ?? 0} decls · ${res.data_count ?? 0} ADTs · ${res.theorem_count ?? 0} erased proofs · ${elapsed} ms`;
        if (command === "build") {
          lastRust = res.rust || "";
          output.textContent = lastRust;
          setStatus("ok", "BUILT RUST", summary);
        } else {
          output.textContent = `${res.message}\n\nClick "Build Rust" to extract #![no_std] Rust code.`;
          setStatus("ok", "CHECKED", summary);
        }
      } else {
        lastRust = "";
        output.textContent = `playground.ap:${res.line}:${res.column}: error (${res.stage}):\n${res.message}`;
        setStatus("err", `ERROR (${res.stage.toUpperCase()})`, `line ${res.line}, col ${res.column} · ${elapsed} ms`);
      }
      if (switchTab) {
        setMobileTab("output");
      }
    } catch (err) {
      lastRust = "";
      output.textContent = String(err);
      setStatus("err", "RUNTIME ERROR", "WebAssembly execution failed.");
      if (switchTab) {
        setMobileTab("output");
      }
    }
  }

  presetSelect.addEventListener("change", () => {
    const chosen = PRESETS[presetSelect.value];
    if (chosen) {
      editor.value = chosen.code;
      execute("build");
    }
  });

  checkBtn.addEventListener("click", () => execute("check", true));
  buildBtn.addEventListener("click", () => execute("build", true));

  omegaBtn.addEventListener("click", () => {
    setMobileTab("editor");
    const start = editor.selectionStart ?? editor.value.length;
    const end = editor.selectionEnd ?? editor.value.length;
    editor.value = `${editor.value.slice(0, start)}ω${editor.value.slice(end)}`;
    editor.focus();
    editor.setSelectionRange(start + 1, start + 1);
  });

  copyBtn.addEventListener("click", async () => {
    const text = lastRust || output.textContent || "";
    if (!text || !navigator.clipboard) {
      return;
    }
    try {
      await navigator.clipboard.writeText(text);
      const prev = copyBtn.textContent;
      copyBtn.textContent = "Copied";
      setTimeout(() => {
        copyBtn.textContent = prev;
      }, 1400);
    } catch {
      // Clipboard write unavailable in restricted contexts.
    }
  });

  shareBtn.addEventListener("click", async () => {
    const encoded = encodeBase64Url(editor.value);
    const url = `${window.location.origin}${window.location.pathname}?code=${encoded}#playground`;
    window.history.replaceState(null, "", `?code=${encoded}#playground`);
    if (navigator.clipboard) {
      try {
        await navigator.clipboard.writeText(url);
        const prev = shareBtn.textContent;
        shareBtn.textContent = "Link Copied";
        setTimeout(() => {
          shareBtn.textContent = prev;
        }, 1400);
      } catch {
        // Clipboard write unavailable in restricted contexts.
      }
    }
  });

  editor.addEventListener("keydown", (event) => {
    if ((event.ctrlKey || event.metaKey) && event.key === "Enter") {
      event.preventDefault();
      execute("build");
    }
  });

  setStatus("loading", "LOADING WASM", "Compiling apollo-wasm.wasm locally in your browser...");
  loadWasmModule("./apollo-wasm.wasm")
    .then((mod) => {
      wasmModule = mod;
      execute("build");
    })
    .catch((err) => {
      output.textContent = `Could not load apollo-wasm.wasm.\nBuild locally with:\n  cargo build --release --target wasm32-wasip1 -p apollo-wasm\n  cp target/wasm32-wasip1/release/apollo-wasm.wasm website/\n\nDetails: ${err}`;
      setStatus("err", "WASM UNAVAILABLE", "Static preview mode without apollo-wasm.wasm.");
    });
}

if (typeof document !== "undefined") {
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initPlayground);
  } else {
    initPlayground();
  }
}
