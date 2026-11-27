use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    #[must_use]
    pub const fn merge(self, other: Self) -> Self {
        let start = if self.start < other.start {
            self.start
        } else {
            other.start
        };
        let end = if self.end > other.end {
            self.end
        } else {
            other.end
        };
        Self { start, end }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LineCol {
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for LineCol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[must_use]
pub fn line_col(source: &str, offset: usize) -> LineCol {
    let clamped = offset.min(source.len());
    let mut line = 1;
    let mut col = 1;
    for (idx, ch) in source.char_indices() {
        if idx >= clamped {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    LineCol { line, col }
}

#[cfg(test)]
mod tests {
    use super::{LineCol, Span, line_col};

    #[test]
    fn merges_spans_in_either_order() {
        let left = Span::new(2, 5);
        let right = Span::new(7, 12);
        assert_eq!(left.merge(right), Span::new(2, 12));
        assert_eq!(right.merge(left), Span::new(2, 12));
    }

    #[test]
    fn computes_one_based_line_and_column() {
        let src = "fn id(x: A) {\n    x\n}";
        assert_eq!(line_col(src, 0), LineCol { line: 1, col: 1 });
        assert_eq!(line_col(src, 3), LineCol { line: 1, col: 4 });
        assert_eq!(line_col(src, 14), LineCol { line: 2, col: 1 });
        assert_eq!(line_col(src, 18), LineCol { line: 2, col: 5 });
        assert_eq!(line_col(src, 999), LineCol { line: 3, col: 2 });
        assert_eq!(LineCol { line: 2, col: 5 }.to_string(), "2:5");
    }
}
