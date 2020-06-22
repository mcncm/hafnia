use crate::errors;
use crate::token::Lexeme::{Eof, Ident, Nat};
use crate::token::{Lexeme, Location, Token, Unsigned};
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::fmt;
use std::iter::Peekable;
use std::path::Path;
use std::str::Chars;
use std::vec::Vec;

lazy_static! {
    #[rustfmt::skip]
    static ref KEYWORDS: HashMap<&'static str, Lexeme> = {
        let mut m = HashMap::new();
        m.insert("if",    Lexeme::If);
        m.insert("else",  Lexeme::Else);
        m.insert("for",   Lexeme::For);
        m.insert("let",   Lexeme::Let);
        m.insert("fn",    Lexeme::Fn);
        m.insert("print", Lexeme::Print);
        m.insert("true",  Lexeme::True);
        m.insert("false", Lexeme::False);
        m
    };
    static ref SCTOKENS: HashMap<char, Lexeme> = {
        let mut m = HashMap::new();
        m.insert('+', Lexeme::Plus);
        m.insert('*', Lexeme::Star);
        m.insert(',', Lexeme::Comma);
        m.insert('!', Lexeme::Bang);
        m.insert('?', Lexeme::QuestionMark);
        m.insert(';', Lexeme::Semicolon);
        m.insert('[', Lexeme::LBracket);
        m.insert(']', Lexeme::RBracket);
        m.insert('(', Lexeme::LParen);
        m.insert(')', Lexeme::RParen);
        m.insert('{', Lexeme::LBrace);
        m.insert('}', Lexeme::RBrace);
        m
    };
    static ref TCTOKENS: HashMap<(char, char), Lexeme> = {
        let mut m = HashMap::new();
        m.insert(('.', '.'), Lexeme::StopStop);
        m.insert(('=', '='), Lexeme::EqualEqual);
        m.insert(('~', '='), Lexeme::TildeEqual);
        m
    };
}

#[derive(Debug)]
pub struct ScanError {
    loc: Location,
    msg: &'static str,
    chars: String,
}

impl fmt::Display for ScanError {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Scanning error in '{}' [{}]: {}",
              self.chars, self.loc, self.msg
        )
    }
}

impl errors::Error for ScanError {}

pub struct SourceObject<'a> {
    pub code: Peekable<Chars<'a>>,
    // TODO: should replace this with a &Path or &PathBuf, but this leads to a lot
    // of lifetime wrangling I don't want to deal with right now.
    pub file: Option<String>,
}

impl<'a> SourceObject<'a> {
    pub fn from_src(src: &'a str) -> Self {
        Self {
            code: src.chars().peekable(),
            file: None,
        }
    }
}

struct ScanHead<'a> {
    src: SourceObject<'a>,
    pub pos: usize,  // absolute position in source
    pub line: usize, // line number in source
    pub col: usize,  // column number in source
}

impl<'a> ScanHead<'a> {
    fn new(src: SourceObject<'a>) -> Self {
        ScanHead {
            src,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn loc(&self) -> Location {
        Location {
            pos: self.pos,
            line: self.line,
            col: self.col,
            file: self.src.file.as_ref().cloned(),
        }
    }

    fn next_raw_char(&mut self) -> Option<char> {
        let next = self.src.code.next();
        if let Some(ch) = next {
            self.pos += 1;
            self.col += 1;
            if ch == '\n' {
                self.line += 1;
                self.col = 1;
            }
        }
        next
    }

    fn advance_to(&mut self, target: char) {
        for ch in self {
            if ch == target {
                break;
            }
        }
    }

    pub fn advance_to_newline(&mut self) {
        self.advance_to('\n');
    }

    fn peek(&mut self) -> Option<&char> {
        self.src.code.peek()
    }
}

impl<'a> Iterator for ScanHead<'a> {
    type Item = char;

    // Advance the scan head to the next character, filtering whitespace.
    fn next(&mut self) -> Option<char> {
        while let Some(ch) = self.next_raw_char() {
            if !ch.is_ascii_whitespace() {
                return Some(ch);
            }
        }
        None
    }
}

pub struct Scanner<'a> {
    // Scanner data
    scan_head: ScanHead<'a>,
    token_buf: Vec<char>,
    tokens: Vec<Token>,
    errors: Vec<Box<dyn errors::Error>>,
}

// Adds a lexed token to a Scanner's `tokens` vector.
macro_rules! push_token {
    ($self:ident, $tok:ident$(($($arg:expr),*))?) => {
        $self.tokens.push(Token {
            lexeme: $tok$(($($arg),+))?,
            loc: $self.scan_head.loc(),
        });
        $self.token_buf.clear();
    };
}

impl<'a> Scanner<'a> {
    pub fn new(src: SourceObject<'a>) -> Self {
        Scanner {
            scan_head: ScanHead::new(src),
            token_buf: vec![],
            tokens: vec![],
            errors: vec![],
        }
    }

    fn next_char(&mut self) -> Option<char> {
        self.scan_head.next().map(|ch| {
            self.token_buf.push(ch);
            ch
        })
    }

    // abort this token; advance to the next whitespace character and empty the
    // token buffer.
    fn scrub_token(&mut self, msg: &'static str) {
        let loc = self.synchronize_to_whitespace();
        self.errors.push(Box::new(ScanError {
            loc,
            msg,
            chars: self.token_buf.iter().collect(),
        }));
        self.token_buf.clear();
    }

    // Advance the scan head to the next whitespace character, and return
    // position before advancing.
    pub fn synchronize_to_whitespace(&mut self) -> Location {
        let loc = self.scan_head.loc();
        while let Some(ch) = self.scan_head.peek() {
            if !ch.is_ascii_whitespace() {
                self.next_char();
            } else {
                break;
            }
        }
        loc
    }

    pub fn lex(mut self) -> Result<Vec<Token>, Vec<Box<dyn errors::Error>>> {
        // This macro adds a token to the `tokens` vector, consuming
        // all the characters in the Scanner's `token_buf`.

        while let Some(ch) = self.next_char() {
            // Greedily check for two-character tokens
            if let Some(&following) = self.scan_head.peek() {
                if let Some(lexeme) = TCTOKENS.get(&(ch, following)) {
                    let lexeme = lexeme.clone();
                    push_token!(self, lexeme);
                    // Consume the second character and loop again.
                    self.scan_head.next_raw_char();
                    continue;
                }
            }
            // Single-character tokens
            if let Some(lexeme) = SCTOKENS.get(&ch) {
                let lexeme = lexeme.clone();
                push_token!(self, lexeme);
            }
            // Otherwise, may be beginning a number
            else if ch.is_ascii_digit() {
                self.consume_nat();
            }
            // Or it could be a keyword or identifier
            else if ch.is_alphabetic() {
                self.consume_ident();
            }
        }

        // Finally, add the end-of-file sentinel
        push_token!(self, Eof);

        if self.errors.is_empty() {
            Ok(self.tokens)
        } else {
            Err(self.errors)
        }
    }

    /// Either completes a `Nat` token ands adds it to the Scanner's `tokens`
    /// vector, or adds an error. `Nat`s must consist solely of ascii digits.
    fn consume_nat(&mut self) {
        while let Some(ch) = self.scan_head.peek() {
            if ch.is_ascii_digit() {
                self.next_char();
            } else if ch.is_ascii_alphabetic() {
                self.scrub_token("Numeric tokens may not contain alphabetic characters.");
                return;
            } else {
                break;
            }
        }

        // Shouldn't fail except for numbers larger than an `Unsigned`!
        let value: Result<Unsigned, _> = self.token_buf.iter().collect::<String>().parse();
        if let Ok(value) = value {
            push_token!(self, Nat(value));
        } else {
            self.scrub_token("Failed to parse numeric token.");
        }
    }

    /// Either completes an identifier or keyword and adds it to the Scanner's
    /// `tokens` vector, or adds an error. Idents must begin with an alphabetic
    /// character, and may be followed by alphabetic and numeric characters.
    fn consume_ident(&mut self) {
        while let Some(ch) = self.scan_head.peek() {
            if ch.is_ascii_alphanumeric() {
                self.next_char();
            } else {
                break;
            }
        }

        let ident: String = self.token_buf.iter().collect();
        if let Some(keyword) = KEYWORDS.get(ident.as_str()) {
            let keyword = keyword.clone();
            push_token!(self, keyword);
        } else {
            push_token!(self, Ident(ident));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests sample code against a sequence of token types, not including an
    /// Eof. In more human-readable form, the syntax looks like:
    ///
    ///   lex_test("4 + 8;"; Int(4), Plus, Int(8), Semicolon);
    ///
    macro_rules! lex_test {
        ($code:expr $(; $($tok:ident$(($($arg:expr),+))?),* )?) => {
            let mut expected_tokens = vec![];
            $(
                $(
                    expected_tokens.push(Lexeme::$tok $(($($arg),+))?);
                )*
            )?
            expected_tokens.push(Lexeme::Eof);

            let src = SourceObject {
                code: $code.chars().peekable(),
                file: None,
            };

            let scanner = Scanner::new(src);
            let tokens = scanner.lex().unwrap();

            let token_pairs = tokens
                .into_iter()
                .map(|token| token.lexeme)
                .zip(expected_tokens);

            for (token, expected_token) in token_pairs {
                assert_eq!(token, expected_token);
            }
        };
    }

    // Basic tests

    #[test]
    #[should_panic]
    fn lex_test_works() {
        lex_test!("&"; Star);
    }

    #[test]
    #[rustfmt::skip]
    fn single_character_tokens() {
        lex_test!("+ * , ! ? ; [ ] ( ) { }";
                  Plus,  Star, Comma, Bang, QuestionMark, Semicolon,
                  LBracket, RBracket, LParen, RParen, LBrace, RBrace);
    }

    #[test]
    fn two_character_tokens() {
        lex_test!(".. == ~="; StopStop, EqualEqual, TildeEqual);
    }

    #[test]
    fn whitespace() {
        lex_test!("+    +\n+\t\t\t+"; Plus, Plus, Plus, Plus);
    }

    // Numeric tests

    #[test]
    fn numbers_simple() {
        lex_test!("12 + 3 * 0"; Nat(12), Plus, Nat(3), Star, Nat(0));
    }

    #[test]
    fn numbers_equality() {
        lex_test!("1 == 1"; Nat(1), EqualEqual, Nat(1));
    }

    #[test]
    fn numbers_equality_no_whitespace() {
        lex_test!("2==2"; Nat(2), EqualEqual, Nat(2));
    }
    #[test]
    fn numbers_inequality() {
        lex_test!("3 ~= 3"; Nat(3), TildeEqual, Nat(3));
    }

    #[test]
    fn numbers_no_whitespace() {
        lex_test!("12*3"; Nat(12), Star, Nat(3));
    }

    // These `should_panic` tests are insufficiently sensitive: they don't in
    // any way validate the origin or nature of the error.

    #[test]
    #[should_panic]
    fn invalid_number_1() {
        lex_test!("123if234"; Nat(123), If, Nat(234));
    }

    #[test]
    #[should_panic]
    fn invalid_number_2() {
        lex_test!("123else"; Nat(123), Else);
    }

    #[test]
    #[should_panic]
    #[allow(overflowing_literals)]
    fn large_number() {
        lex_test!("1111111111111111111111111111111";
                  Nat(1111111111111111111111111111111)
        );
    }

    // Identifier-related tests

    #[test]
    fn ident_simple() {
        lex_test!("ihtfp"; Ident(String::from("ihtfp")));
    }

    #[test]
    fn ident_trailing_numbers() {
        lex_test!("foo1"; Ident(String::from("foo1")));
    }

    #[test]
    #[should_panic]
    fn ident_leading_numbers() {
        lex_test!("99luft_ballons"; Ident(String::from("99luft_ballons")));
    }

    #[test]
    #[rustfmt::skip]
    fn ident_no_whitespace() {
        lex_test!("zip!zap!";
                  Ident(String::from("zip")), Bang,
                  Ident(String::from("zap")), Bang);
    }

    #[test]
    #[rustfmt::skip]
    fn ident_keywords() {
        lex_test!("if else for let fn print true false";
                  If, Else, For, Let, Fn, Print, True, False);
    }
}
