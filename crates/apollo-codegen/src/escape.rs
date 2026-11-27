#[must_use]
pub fn escape_ident(name: &str) -> String {
    match name {
        "self" => "apollo_self".to_owned(),
        "Self" => "apollo_Self".to_owned(),
        "super" => "apollo_super".to_owned(),
        "crate" => "apollo_crate".to_owned(),
        "as" | "async" | "await" | "break" | "const" | "continue" | "dyn" | "else" | "enum"
        | "extern" | "false" | "fn" | "for" | "if" | "impl" | "in" | "let" | "loop" | "match"
        | "mod" | "move" | "mut" | "pub" | "ref" | "return" | "static" | "struct" | "trait"
        | "true" | "type" | "unsafe" | "use" | "where" | "while" | "abstract" | "become"
        | "box" | "do" | "final" | "gen" | "macro" | "override" | "priv" | "try" | "typeof"
        | "unsized" | "virtual" | "yield" => format!("r#{name}"),
        other => other.to_owned(),
    }
}

#[must_use]
pub fn mark_unused(name: &str) -> String {
    if name.starts_with('_') {
        name.to_owned()
    } else if let Some(raw) = name.strip_prefix("r#") {
        format!("_{raw}")
    } else {
        format!("_{name}")
    }
}

#[cfg(test)]
mod tests {
    use super::{escape_ident, mark_unused};

    #[test]
    fn escapes_rust_keywords_and_marks_unused_names() {
        assert_eq!(escape_ident("id"), "id");
        assert_eq!(escape_ident("match"), "r#match");
        assert_eq!(escape_ident("type"), "r#type");
        assert_eq!(escape_ident("self"), "apollo_self");
        assert_eq!(escape_ident("Self"), "apollo_Self");
        assert_eq!(escape_ident("super"), "apollo_super");
        assert_eq!(escape_ident("crate"), "apollo_crate");

        assert_eq!(mark_unused("x"), "_x");
        assert_eq!(mark_unused("_x"), "_x");
        assert_eq!(mark_unused("r#type"), "_type");
    }
}
