use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub const MAX_DESCRIPTIVE_WORDS: usize = 25;
pub const MAX_PROCEDURAL_WORDS: usize = 20;

const BANNED_WORDS: &[(&str, &str)] = &[
    ("actually", "remove filler word"),
    ("additionally", "also"),
    ("allow", "let"),
    ("allowed", "let"),
    ("allows", "lets"),
    ("approximately", "about"),
    ("basically", "remove filler word"),
    ("commence", "start"),
    ("display", "show"),
    ("displays", "shows"),
    ("ensure", "make sure"),
    ("ensures", "makes sure"),
    ("etc", "remove abbreviation"),
    ("execute", "run"),
    ("executes", "runs"),
    ("facilitate", "help"),
    ("facilitates", "helps"),
    ("furthermore", "also"),
    ("however", "but"),
    ("implement", "build or make"),
    ("implements", "builds or makes"),
    ("leverage", "use"),
    ("leverages", "uses"),
    ("modify", "change"),
    ("modifies", "changes"),
    ("multiple", "more than one"),
    ("obtain", "get"),
    ("obtains", "gets"),
    ("perform", "do"),
    ("performs", "does"),
    ("provide", "give"),
    ("provides", "gives"),
    ("require", "need"),
    ("requires", "needs"),
    ("simply", "remove filler word"),
    ("subsequently", "then"),
    ("terminate", "stop"),
    ("therefore", "so"),
    ("utilize", "use"),
    ("utilizes", "uses"),
    ("various", "different"),
    ("verify", "check"),
    ("verifies", "checks"),
    ("via", "through"),
];

const BANNED_ABBREVIATIONS: &[(&str, &str)] = &[("e.g.", "for example"), ("i.e.", "that is")];

const BE_AUXILIARIES: &[&str] = &["am", "are", "be", "been", "is", "was", "were"];

const PARTICIPLES_ALLOWED_AS_ADJECTIVES: &[&str] = &[
    "approved",
    "content-addressed",
    "fixed",
    "licensed",
    "named",
    "required",
    "verified",
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    pub path: PathBuf,
    pub line: usize,
    pub message: String,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.path.display(), self.line, self.message)
    }
}

pub fn check_root(root: &Path) -> io::Result<Vec<Violation>> {
    let files = collect_doc_files(root)?;
    let mut violations = Vec::new();
    for path in files {
        let content = fs::read_to_string(&path)?;
        let display_path = path.strip_prefix(root).unwrap_or(&path);
        violations.extend(check_markdown(display_path, &content));
    }
    Ok(violations)
}

pub fn collect_doc_files(root: &Path) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    let readme = root.join("README.md");
    if readme.is_file() {
        files.push(readme);
    }
    let docs_dir = root.join("docs");
    if docs_dir.is_dir() {
        collect_markdown_recursive(&docs_dir, &mut files)?;
    }
    files.sort();
    Ok(files)
}

fn collect_markdown_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_markdown_recursive(&path, out)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("md") {
            out.push(path);
        }
    }
    Ok(())
}

#[must_use]
pub fn check_markdown(path: &Path, content: &str) -> Vec<Violation> {
    let mut violations = Vec::new();
    let mut in_code_fence = false;

    for (index, raw_line) in content.lines().enumerate() {
        let line_number = index + 1;
        let trimmed = raw_line.trim();

        if trimmed.starts_with("```") {
            in_code_fence = !in_code_fence;
            continue;
        }
        if in_code_fence || trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        let (is_procedural, body) = strip_list_prefix(trimmed);
        let cleaned = strip_inline_markup(body);

        for sentence in split_sentences(&cleaned) {
            check_sentence(path, line_number, is_procedural, &sentence, &mut violations);
        }
    }

    violations
}

fn strip_list_prefix(line: &str) -> (bool, &str) {
    if let Some(rest) = line.strip_prefix("- ").or_else(|| line.strip_prefix("* ")) {
        return (false, rest);
    }
    let bytes = line.as_bytes();
    let mut digits = 0;
    while digits < bytes.len() && bytes[digits].is_ascii_digit() {
        digits += 1;
    }
    if digits > 0 && bytes.get(digits) == Some(&b'.') && bytes.get(digits + 1) == Some(&b' ') {
        return (true, &line[digits + 2..]);
    }
    (false, line)
}

fn strip_inline_markup(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;
    let mut in_code = false;

    while i < chars.len() {
        let ch = chars[i];
        if ch == '`' {
            in_code = !in_code;
            if !in_code {
                out.push_str(" code ");
            }
            i += 1;
            continue;
        }
        if in_code {
            i += 1;
            continue;
        }
        if ch == '['
            && let Some((label, next_index)) = parse_markdown_link(&chars, i)
        {
            out.push_str(&label);
            i = next_index;
            continue;
        }
        if ch == '*' || ch == '_' {
            i += 1;
            continue;
        }
        out.push(ch);
        i += 1;
    }

    out
}

fn parse_markdown_link(chars: &[char], start: usize) -> Option<(String, usize)> {
    let mut i = start + 1;
    let mut label = String::new();
    while i < chars.len() && chars[i] != ']' {
        label.push(chars[i]);
        i += 1;
    }
    if i + 1 >= chars.len() || chars[i] != ']' || chars[i + 1] != '(' {
        return None;
    }
    i += 2;
    while i < chars.len() && chars[i] != ')' {
        i += 1;
    }
    if i < chars.len() && chars[i] == ')' {
        Some((label, i + 1))
    } else {
        None
    }
}

fn split_sentences(line: &str) -> Vec<String> {
    let mut sentences = Vec::new();
    let mut current = String::new();
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        let ch = chars[i];
        current.push(ch);
        let is_boundary =
            matches!(ch, '.' | '!' | '?') && (i + 1 == chars.len() || chars[i + 1].is_whitespace());
        if is_boundary && !ends_with_abbreviation(&current) {
            let trimmed = current.trim();
            if !trimmed.is_empty() {
                sentences.push(trimmed.to_owned());
            }
            current.clear();
        }
        i += 1;
    }

    let trimmed = current.trim();
    if !trimmed.is_empty() {
        sentences.push(trimmed.to_owned());
    }

    sentences
}

fn ends_with_abbreviation(text: &str) -> bool {
    let lower = text.to_ascii_lowercase();
    BANNED_ABBREVIATIONS
        .iter()
        .any(|(abbr, _)| lower.ends_with(abbr))
        || lower.ends_with("e.g.")
        || lower.ends_with("i.e.")
}

fn check_sentence(
    path: &Path,
    line: usize,
    is_procedural: bool,
    sentence: &str,
    violations: &mut Vec<Violation>,
) {
    let lower_sentence = sentence.to_ascii_lowercase();
    for &(abbr, suggestion) in BANNED_ABBREVIATIONS {
        if lower_sentence.contains(abbr) {
            violations.push(Violation {
                path: path.to_path_buf(),
                line,
                message: format!("avoid abbreviation '{abbr}'; use '{suggestion}'"),
            });
        }
    }

    let raw_words: Vec<&str> = sentence.split_whitespace().collect();
    let limit = if is_procedural {
        MAX_PROCEDURAL_WORDS
    } else {
        MAX_DESCRIPTIVE_WORDS
    };
    if raw_words.len() > limit {
        violations.push(Violation {
            path: path.to_path_buf(),
            line,
            message: format!(
                "sentence has {} words (max {limit} under ASD-STE100)",
                raw_words.len()
            ),
        });
    }

    let mut normalized_words = Vec::with_capacity(raw_words.len());
    for raw in &raw_words {
        let cleaned = raw
            .trim_matches(|ch: char| !ch.is_alphanumeric() && ch != '\'' && ch != '-')
            .to_ascii_lowercase();
        if cleaned.is_empty() {
            continue;
        }
        if is_contraction(&cleaned) {
            violations.push(Violation {
                path: path.to_path_buf(),
                line,
                message: format!("avoid contraction '{cleaned}' under ASD-STE100"),
            });
        }
        if let Some(suggestion) = find_banned_word(&cleaned) {
            violations.push(Violation {
                path: path.to_path_buf(),
                line,
                message: format!("avoid non-STE100 word '{cleaned}'; use '{suggestion}'"),
            });
        }
        normalized_words.push(cleaned);
    }

    for pair in normalized_words.windows(2) {
        if let [first, second] = pair
            && BE_AUXILIARIES.contains(&first.as_str())
            && is_passive_participle(second)
        {
            violations.push(Violation {
                path: path.to_path_buf(),
                line,
                message: format!("use active voice instead of '{first} {second}'"),
            });
        }
    }
}

fn is_contraction(word: &str) -> bool {
    word.contains('\'')
        && (word.ends_with("n't")
            || word.ends_with("'re")
            || word.ends_with("'ve")
            || word.ends_with("'ll")
            || word.ends_with("'m")
            || word.ends_with("'d")
            || matches!(word, "it's" | "that's" | "there's" | "let's" | "what's"))
}

fn find_banned_word(word: &str) -> Option<&'static str> {
    BANNED_WORDS
        .iter()
        .find(|&&(banned, _)| banned == word)
        .map(|&(_, suggestion)| suggestion)
}

fn is_passive_participle(word: &str) -> bool {
    word.len() > 4 && word.ends_with("ed") && !PARTICIPLES_ALLOWED_AS_ADJECTIVES.contains(&word)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{check_markdown, check_root};

    #[test]
    fn accepts_clean_ste100_markdown() {
        let doc = "# Title\n\nApollo checks proofs fast.\n\n1. Run the check tool.\n\n```rust\nfn utilize() {}\n```\n";
        let violations = check_markdown(Path::new("README.md"), doc);
        assert_eq!(violations, Vec::new());
    }

    #[test]
    fn flags_long_descriptive_sentence() {
        let doc = "one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree twentyfour twentyfive twentysix.";
        let violations = check_markdown(Path::new("README.md"), doc);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].message.contains("26 words (max 25"));
    }

    #[test]
    fn flags_long_procedural_sentence() {
        let doc = "1. one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen eighteen nineteen twenty twentyone.";
        let violations = check_markdown(Path::new("docs/guide.md"), doc);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].message.contains("21 words (max 20"));
    }

    #[test]
    fn flags_contractions_and_banned_words() {
        let doc = "Do not utilize tools that don't work, e.g. via hacks.";
        let violations = check_markdown(Path::new("README.md"), doc);
        assert_eq!(violations.len(), 4);
        assert!(violations.iter().any(|v| v.message.contains("utilize")));
        assert!(violations.iter().any(|v| v.message.contains("don't")));
        assert!(violations.iter().any(|v| v.message.contains("e.g.")));
        assert!(violations.iter().any(|v| v.message.contains("via")));
    }

    #[test]
    fn flags_passive_voice_and_ignores_code_and_links() {
        let doc = "The file is checked by `utilize` in [Apache 2.0](https://example.com/utilize).";
        let violations = check_markdown(Path::new("docs/test.md"), doc);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].message.contains("is checked"));
        assert!(violations[0].to_string().contains("docs/test.md:1:"));
    }

    #[test]
    fn checks_repository_documentation_root() {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let root = manifest_dir.parent().unwrap_or(manifest_dir);
        let result = check_root(root);
        assert!(result.is_ok());
        assert_eq!(result.unwrap_or_default(), Vec::new());
    }

    #[test]
    fn handles_unclosed_brackets_and_bullet_items() {
        let doc = "* Apollo uses [brackets without link.\n- Apollo uses [label](missing\n";
        let violations = check_markdown(Path::new("docs/edge.md"), doc);
        assert_eq!(violations, Vec::new());
    }
}
