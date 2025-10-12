pub mod format;

use phf_macros::phf_map;
use std::iter::Peekable;
use std::str::Chars;
use thiserror::Error;

/// Represents a region of the source code.
#[derive(Clone, Debug, PartialEq, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// A token along with its position in the source code.
#[derive(Clone, Debug, PartialEq)]
pub struct SpannedToken {
    pub token: Token,
    pub span: Span,
}

/// A token represents a single meaningful unit in the source code.
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    LeftParen,
    RightParen,

    Plus,
    Minus,
    Star,
    Slash,

    Identifier(String),
    String(String),
    Double(f64),
    Integer(i64),
    Boolean(bool),

    Bang,

    Equal,
    Lambda,
    EqualEqual,
    BangEqual,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,

    And,
    Or,

    If,
    Then,
    Else,
    Fn,
    Let,
    In,
    Fix,
}

static KEYWORDS: phf::Map<&'static str, Token> = phf_map! {
    "if" => Token::If,
    "then" => Token::Then,
    "else" => Token::Else,
    "fn" => Token::Fn,
    "let" => Token::Let,
    "fix" => Token::Fix,
    "true" => Token::Boolean(true),
    "false" => Token::Boolean(false),
    "in" => Token::In,
    "and" => Token::And,
    "or" => Token::Or,
};

fn is_special_char(ch: char) -> bool {
    matches!(
        ch,
        '(' | ')' | '+' | '-' | '*' | '/' | '!' | '>' | '<' | '=' | '"'
    )
}

/// Errors that can occur during lexical analysis.
#[derive(Error, Debug, PartialEq)]
pub enum LexError {
    #[error("unexpected character")]
    UnexpectedChar(usize),
    #[error("unterminated string")]
    UnterminatedString(usize),
}

/// A lexical analyzer that converts source code into a stream of tokens.
pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    position: usize,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer for the given input string.
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.chars().peekable(),
            position: 0,
        }
    }

    /// Collects all tokens from the input, separating successful tokens from errors.
    pub fn collect_all(&mut self) -> (Vec<Token>, Vec<LexError>) {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();

        for result in self {
            match result {
                Ok(token) => tokens.push(token),
                Err(err) => errors.push(err),
            }
        }

        (tokens, errors)
    }

    fn match_next(&mut self, expected: char) -> bool {
        if self.input.peek() == Some(&expected) {
            self.input.next();
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn next_or(&mut self, expected: char, result: Token, default: Token) -> Token {
        if self.match_next(expected) {
            result
        } else {
            default
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(&ch) = self.input.peek() {
            if ch.is_whitespace() {
                self.input.next();
                self.position += 1;
            } else {
                break;
            }
        }
    }

    fn skip_line_comment(&mut self) {
        self.input.next();
        self.position += 1;

        while let Some(&ch) = self.input.peek() {
            self.input.next();
            self.position += 1;
            if ch == '\n' {
                break;
            }
        }
    }

    fn parse_string(&mut self, start: usize) -> Result<Token, LexError> {
        let mut value = String::new();

        loop {
            let ch = self
                .input
                .next()
                .ok_or(LexError::UnterminatedString(start))?;
            self.position += 1;
            match ch {
                '"' => return Ok(Token::String(value)),
                '\\' => {
                    // In this language, we only escape the quote character.
                    // WYSIWYG, except for ".
                    match self.input.next() {
                        Some('"') => {
                            value.push('"');
                        }
                        Some(ch) => {
                            value.push('\\');
                            value.push(ch);
                        }
                        None => {
                            return Err(LexError::UnterminatedString(start));
                        }
                    }
                }
                ch => {
                    value.push(ch);
                }
            }
        }
    }

    fn parse_number(&mut self, start: usize, first: char) -> Result<Token, LexError> {
        let mut num_str = String::from(first);
        let mut has_decimal = false;

        while let Some(&ch) = self.input.peek() {
            match ch {
                '.' if !has_decimal => {
                    has_decimal = true;
                    num_str.push(ch);
                    self.input.next();
                    self.position += 1;
                }
                '0'..='9' => {
                    num_str.push(ch);
                    self.input.next();
                    self.position += 1;
                }
                _ => break,
            }
        }

        if has_decimal {
            num_str
                .parse()
                .map(Token::Double)
                .map_err(|_| LexError::UnexpectedChar(start))
        } else {
            num_str
                .parse()
                .map(Token::Integer)
                .map_err(|_| LexError::UnexpectedChar(start))
        }
    }

    fn parse_identifier(&mut self, first: char) -> Token {
        let mut result = String::from(first);
        while let Some(&ch) = self.input.peek()
            && !ch.is_whitespace()
            && !is_special_char(ch)
        {
            result.push(ch);
            self.input.next();
            self.position += 1;
        }
        KEYWORDS
            .get(&result)
            .cloned()
            .unwrap_or_else(|| Token::Identifier(result))
    }
}
impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();

        let start = self.position;

        let ch = self.input.next()?;
        self.position += 1;

        let result = match ch {
            '(' => Ok(Token::LeftParen),
            ')' => Ok(Token::RightParen),

            '+' => Ok(Token::Plus),
            '-' => Ok(Token::Minus),
            '*' => Ok(Token::Star),

            '/' if self.input.peek() == Some(&'/') => {
                self.skip_line_comment();
                return self.next();
            }
            '/' => Ok(Token::Slash),

            '!' => Ok(self.next_or('=', Token::BangEqual, Token::Bang)),
            '=' => {
                let first = self.next_or('>', Token::Lambda, Token::Equal);
                Ok(self.next_or('=', Token::EqualEqual, first))
            }
            '>' => Ok(self.next_or('=', Token::GreaterEqual, Token::Greater)),
            '<' => Ok(self.next_or('=', Token::LessEqual, Token::Less)),

            '"' => self.parse_string(start),

            '0'..='9' => self.parse_number(start, ch),

            ch => Ok(self.parse_identifier(ch)),
        };

        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_char_tokens() {
        let input = "( ) + - * /";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::RightParen,
                Token::Plus,
                Token::Minus,
                Token::Star,
                Token::Slash,
            ]
        );
    }

    #[test]
    fn test_comparison_operators() {
        let input = "< > <= >= == != = !";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Less,
                Token::Greater,
                Token::LessEqual,
                Token::GreaterEqual,
                Token::EqualEqual,
                Token::BangEqual,
                Token::Equal,
                Token::Bang,
            ]
        );
    }

    #[test]
    fn test_integers() {
        let input = "0 42 123 999";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Integer(0),
                Token::Integer(42),
                Token::Integer(123),
                Token::Integer(999),
            ]
        );
    }

    #[test]
    fn test_negative_integers() {
        let input = "-1 -42 -999";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Minus,
                Token::Integer(1),
                Token::Minus,
                Token::Integer(42),
                Token::Minus,
                Token::Integer(999),
            ]
        );
    }

    #[test]
    fn test_doubles() {
        let input = "3.14 0.5 99.99";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Double(3.14),
                Token::Double(0.5),
                Token::Double(99.99),
            ]
        );
    }

    #[test]
    fn test_negative_doubles() {
        let input = "-3.14 -0.5";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Minus,
                Token::Double(3.14),
                Token::Minus,
                Token::Double(0.5),
            ]
        );
    }

    #[test]
    fn test_strings() {
        let input = r#""hello" "world" """#;
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::String("hello".to_string()),
                Token::String("world".to_string()),
                Token::String("".to_string()),
            ]
        );
    }

    #[test]
    fn test_string_with_escape() {
        let input = r#""hello \"world\"""#;
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(tokens, vec![Token::String(r#"hello "world""#.to_string()),]);
    }

    #[test]
    fn test_string_wysiwyg_escape() {
        let input = r#""hello\nworld""#;
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(tokens, vec![Token::String(r#"hello\nworld"#.to_string()),]);
    }

    #[test]
    fn test_unterminated_string() {
        let input = r#""hello"#;
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(tokens.len(), 0);
        assert_eq!(errors.len(), 1);
        assert!(matches!(errors[0], LexError::UnterminatedString(_)));
    }

    #[test]
    fn test_keywords() {
        let input = "if else fn let fix true false and or";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::If,
                Token::Else,
                Token::Fn,
                Token::Let,
                Token::Fix,
                Token::Boolean(true),
                Token::Boolean(false),
                Token::And,
                Token::Or,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        let input = "foo bar baz myVariable";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier("foo".to_string()),
                Token::Identifier("bar".to_string()),
                Token::Identifier("baz".to_string()),
                Token::Identifier("myVariable".to_string()),
            ]
        );
    }

    #[test]
    fn test_line_comments() {
        let input = "// this is a comment\n42 // another comment\n99";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(tokens, vec![Token::Integer(42), Token::Integer(99),]);
    }

    #[test]
    fn test_whitespace_handling() {
        let input = "  42  \n\t  99  \r\n  ";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(tokens, vec![Token::Integer(42), Token::Integer(99),]);
    }

    #[test]
    fn test_complex_expression() {
        let input = "(+ 1 (* 2 3))";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::Plus,
                Token::Integer(1),
                Token::LeftParen,
                Token::Star,
                Token::Integer(2),
                Token::Integer(3),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_function_definition() {
        let input = r#"(fn add (x y) (+ x y))"#;
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::Fn,
                Token::Identifier("add".to_string()),
                Token::LeftParen,
                Token::Identifier("x".to_string()),
                Token::Identifier("y".to_string()),
                Token::RightParen,
                Token::LeftParen,
                Token::Plus,
                Token::Identifier("x".to_string()),
                Token::Identifier("y".to_string()),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_let_binding() {
        let input = r#"(let x 42)"#;
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::Let,
                Token::Identifier("x".to_string()),
                Token::Integer(42),
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_conditional_expression() {
        let input = "(if (> x 0) x (- x))";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::If,
                Token::LeftParen,
                Token::Greater,
                Token::Identifier("x".to_string()),
                Token::Integer(0),
                Token::RightParen,
                Token::Identifier("x".to_string()),
                Token::LeftParen,
                Token::Minus,
                Token::Identifier("x".to_string()),
                Token::RightParen,
                Token::RightParen,
            ]
        );
    }

    #[test]
    fn test_minus_vs_negative() {
        let input = "5 - -3";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Integer(5),
                Token::Minus,
                Token::Minus,
                Token::Integer(3),
            ]
        );
    }

    #[test]
    fn test_empty_input() {
        let input = "";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn test_only_comments() {
        let input = "// just a comment\n// another one";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn test_iterator_usage() {
        let input = "1 2 3";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next(), Some(Ok(Token::Integer(1))));
        assert_eq!(lexer.next(), Some(Ok(Token::Integer(2))));
        assert_eq!(lexer.next(), Some(Ok(Token::Integer(3))));
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn test_lambda_operator() {
        let input = "=> = == x => y";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::Lambda,
                Token::Equal,
                Token::EqualEqual,
                Token::Identifier("x".to_string()),
                Token::Lambda,
                Token::Identifier("y".to_string()),
            ]
        );
    }

    #[test]
    fn test_logical_operators() {
        let input = "(and true false) (or x y)";
        let mut lexer = Lexer::new(input);
        let (tokens, errors) = lexer.collect_all();

        assert_eq!(errors.len(), 0);
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::And,
                Token::Boolean(true),
                Token::Boolean(false),
                Token::RightParen,
                Token::LeftParen,
                Token::Or,
                Token::Identifier("x".to_string()),
                Token::Identifier("y".to_string()),
                Token::RightParen,
            ]
        );
    }
}
