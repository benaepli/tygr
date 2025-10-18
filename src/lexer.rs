pub mod format;

use crate::parser::Span;
use phf_macros::phf_map;
use std::fmt;
use std::iter::Peekable;
use std::str::Chars;
use thiserror::Error;

/// A token represents a single meaningful unit in the source code with its position.
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    fn new(kind: TokenKind, span: Span) -> Self {
        Token { kind, span }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// The kind of token.
#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    LeftParen,
    RightParen,

    Plus,
    Minus,
    Star,
    Slash,
    Caret,

    PlusDot,
    MinusDot,
    StarDot,
    SlashDot,

    Identifier(String),
    String(String),
    Float(f64),
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

    EqualEqualDot,
    BangEqualDot,
    GreaterEqualDot,
    LessEqualDot,
    GreaterDot,
    LessDot,

    EqualEqualB,
    BangEqualB,

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

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::PlusDot => write!(f, "+."),
            TokenKind::MinusDot => write!(f, "-."),
            TokenKind::StarDot => write!(f, "*."),
            TokenKind::SlashDot => write!(f, "/."),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::Equal => write!(f, "="),
            TokenKind::Lambda => write!(f, "\\"),
            TokenKind::Less => write!(f, "<"),
            TokenKind::Greater => write!(f, ">"),

            TokenKind::EqualEqual => write!(f, "=="),
            TokenKind::BangEqual => write!(f, "!="),
            TokenKind::LessEqual => write!(f, "<="),
            TokenKind::GreaterEqual => write!(f, ">="),

            TokenKind::EqualEqualDot => write!(f, "==."),
            TokenKind::BangEqualDot => write!(f, "!=."),
            TokenKind::GreaterEqualDot => write!(f, ">=."),
            TokenKind::LessEqualDot => write!(f, "<=."),
            TokenKind::GreaterDot => write!(f, ">."),
            TokenKind::LessDot => write!(f, "<."),

            TokenKind::EqualEqualB => write!(f, "==b"),
            TokenKind::BangEqualB => write!(f, "!=b"),

            TokenKind::Identifier(s) => write!(f, "{}", s),
            TokenKind::String(s) => write!(f, "\"{}\"", s),
            TokenKind::Float(d) => write!(f, "{}", d),
            TokenKind::Integer(i) => write!(f, "{}", i),
            TokenKind::Boolean(b) => write!(f, "{}", b),

            TokenKind::And => write!(f, "and"),
            TokenKind::Or => write!(f, "or"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Then => write!(f, "then"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::Fn => write!(f, "fn"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::In => write!(f, "in"),
            TokenKind::Fix => write!(f, "fix"),
        }
    }
}

static KEYWORDS: phf::Map<&'static str, TokenKind> = phf_map! {
    "if" => TokenKind::If,
    "then" => TokenKind::Then,
    "else" => TokenKind::Else,
    "fn" => TokenKind::Fn,
    "let" => TokenKind::Let,
    "fix" => TokenKind::Fix,
    "true" => TokenKind::Boolean(true),
    "false" => TokenKind::Boolean(false),
    "in" => TokenKind::In,
    "and" => TokenKind::And,
    "or" => TokenKind::Or,
};

fn is_special_char(ch: char) -> bool {
    matches!(
        ch,
        '(' | ')' | '+' | '-' | '*' | '/' | '^' | '!' | '>' | '<' | '=' | '"' | '~'
    )
}

/// Errors that can occur during lexical analysis.
#[derive(Error, Debug, PartialEq, Clone)]
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

    fn next_or(&mut self, expected: char, result: TokenKind, default: TokenKind) -> TokenKind {
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

    fn parse_string(&mut self, start: usize) -> Result<TokenKind, LexError> {
        let mut value = String::new();

        loop {
            let ch = self
                .input
                .next()
                .ok_or(LexError::UnterminatedString(start))?;
            self.position += 1;
            match ch {
                '"' => return Ok(TokenKind::String(value)),
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

    fn parse_number(&mut self, start: usize, first: char) -> Result<TokenKind, LexError> {
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
                .map(TokenKind::Float)
                .map_err(|_| LexError::UnexpectedChar(start))
        } else {
            num_str
                .parse()
                .map(TokenKind::Integer)
                .map_err(|_| LexError::UnexpectedChar(start))
        }
    }

    fn parse_identifier(&mut self, first: char) -> TokenKind {
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
            .unwrap_or_else(|| TokenKind::Identifier(result))
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
            '(' => Ok(TokenKind::LeftParen),
            ')' => Ok(TokenKind::RightParen),

            '+' => Ok(self.next_or('.', TokenKind::PlusDot, TokenKind::Plus)),
            '-' => Ok(self.next_or('.', TokenKind::MinusDot, TokenKind::Minus)),
            '*' => Ok(self.next_or('.', TokenKind::StarDot, TokenKind::Star)),

            '/' if self.input.peek() == Some(&'/') => {
                self.skip_line_comment();
                return self.next();
            }
            '/' => Ok(self.next_or('.', TokenKind::SlashDot, TokenKind::Slash)),

            '^' => Ok(TokenKind::Caret),

            '!' => {
                if self.match_next('=') {
                    if self.match_next('b') {
                        Ok(TokenKind::BangEqualB)
                    } else if self.match_next('.') {
                        Ok(TokenKind::BangEqualDot)
                    } else {
                        Ok(TokenKind::BangEqual)
                    }
                } else {
                    Ok(TokenKind::Bang)
                }
            }
            '=' => {
                if self.match_next('>') {
                    Ok(TokenKind::Lambda)
                } else if self.match_next('=') {
                    if self.match_next('b') {
                        Ok(TokenKind::EqualEqualB)
                    } else if self.match_next('.') {
                        Ok(TokenKind::EqualEqualDot)
                    } else {
                        Ok(TokenKind::EqualEqual)
                    }
                } else {
                    Ok(TokenKind::Equal)
                }
            }
            '>' => {
                if self.match_next('=') {
                    Ok(self.next_or('.', TokenKind::GreaterEqualDot, TokenKind::GreaterEqual))
                } else if self.match_next('.') {
                    Ok(TokenKind::GreaterDot)
                } else {
                    Ok(TokenKind::Greater)
                }
            }
            '<' => {
                if self.match_next('=') {
                    Ok(self.next_or('.', TokenKind::LessEqualDot, TokenKind::LessEqual))
                } else if self.match_next('.') {
                    Ok(TokenKind::LessDot)
                } else {
                    Ok(TokenKind::Less)
                }
            }

            '"' => self.parse_string(start),

            '0'..='9' => self.parse_number(start, ch),

            ch => Ok(self.parse_identifier(ch)),
        };

        let end = self.position;
        Some(result.map(|kind| Token::new(kind, Span { context: (), start, end })))
    }
}