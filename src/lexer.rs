use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;
use std::vec::Vec;

use crate::token::TokenType::{Eof, Nat};
use crate::token::{Location, Token, TokenType, Unsigned};

use lazy_static::lazy_static;

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, TokenType> = {
        let mut m = HashMap::new();
        m.insert("if", TokenType::If);
        m.insert("else", TokenType::Else);
        m.insert("for", TokenType::For);
        m.insert("let", TokenType::Let);
        m.insert("fn", TokenType::Fn);
        m.insert("print", TokenType::Print);
        m
    };
    static ref SCTOKENS: HashMap<char, TokenType> = {
        let mut m = HashMap::new();
        m.insert('+', TokenType::Plus);
        m.insert('*', TokenType::Star);
        m.insert(',', TokenType::Comma);
        m.insert('!', TokenType::Bang);
        m.insert('?', TokenType::QuestionMark);
        m.insert(';', TokenType::Semicolon);
        m.insert('[', TokenType::LBracket);
        m.insert(']', TokenType::RBracket);
        m.insert('(', TokenType::LParen);
        m.insert(')', TokenType::RParen);
        m.insert('{', TokenType::LBrace);
        m.insert('}', TokenType::RBrace);
        m
    };
}

#[derive(Debug)]
struct LexError {
    loc: Location,
    msg: &'static str,
    chars: String,
}

struct ScanHead<'a> {
    code: Peekable<Chars<'a>>,
    pub pos: usize,  // absolute position in source
    pub line: usize, // line number in source
    pub col: usize,  // column number in source
}

impl<'a> ScanHead<'a> {
    fn new(source: &'a str) -> Self {
        ScanHead {
            code: source.chars().peekable(),
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
        }
    }

    fn next_raw_char(&mut self) -> Option<char> {
        let next = self.code.next();
        if let Some(ch) = next {
            self.pos += 1;
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

    // Advance the scan head to the next whitespace character, and return
    // position before advancing.
    pub fn advance_to_whitespace(&mut self) -> Location {
        let loc = self.loc();
        while let Some(ch) = self.next_raw_char() {
            if !ch.is_ascii_whitespace() {
                break;
            }
        }
        loc
    }

    fn peek(&mut self) -> Option<&char> {
        self.code.peek()
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

struct Lexer<'a> {
    // Lexer data
    scan_head: ScanHead<'a>,
    token_buf: Vec<char>,
    tokens: Vec<Token>,
    errors: Vec<LexError>,
}

// Adds a lexed token to a Lexer's `tokens` vector.
macro_rules! push_token {
    ($self:ident, $tok:ident$(($($arg:expr),*))?) => {
        $self.tokens.push(Token {
            token_type: $tok$(($($arg),+))?,
            loc: $self.scan_head.loc(),
        });
        $self.token_buf.clear();
    };
}

impl<'a> Lexer<'a> {
    fn new(code: &'a str) -> Self {
        Lexer {
            scan_head: ScanHead::new(code),
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
        let loc = self.scan_head.advance_to_whitespace();
        self.token_buf.clear();
        self.errors.push(LexError {
            loc,
            msg,
            chars: self.token_buf.iter().collect(),
        });
    }

    fn lex(mut self) -> Result<Vec<Token>, Vec<LexError>> {
        // This macro adds a token to the `tokens` vector, consuming
        // all the characters in the Lexer's `token_buf`.

        while let Some(ch) = self.next_char() {
            // Single-character tokens
            if let Some(token_type) = SCTOKENS.get(&ch) {
                let token_type = token_type.clone();
                push_token!(self, token_type);
            }

            // Otherwise, may be beginning a number
            if ch.is_ascii_digit() {
                self.consume_nat();
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

    fn consume_nat(&mut self) {
        while let Some(ch) = self.scan_head.peek() {
            if ch.is_ascii_digit() {
                self.next_char();
            } else if ch.is_ascii_alphabetic() {
                self.scrub_token("Numeric tokens may not contain alphabetic characters.");
            } else {
                break;
            }
        }

        // Shouldn't fail, except possibly for very long numbers!
        let value: Result<Unsigned, _> = self.token_buf.iter().collect::<String>().parse();
        if let Ok(value) = value {
            push_token!(self, Nat(value));
        } else {
            self.scrub_token("Failed to parse numeric token.");
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
                    expected_tokens.push(TokenType::$tok $(($($arg),+))?);
                )*
            )?
            expected_tokens.push(TokenType::Eof);

            let lexer = Lexer::new($code);
            let tokens = lexer.lex().unwrap();

            let token_pairs = tokens
                .into_iter()
                .map(|token| token.token_type)
                .zip(expected_tokens);

            for (token, expected_token) in token_pairs {
                assert_eq!(token, expected_token);
            }
        };
    }

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
    fn whitespace() {
        lex_test!("+    +\n+\t\t\t+"; Plus, Plus, Plus, Plus);
    }

    #[test]
    fn simple_numbers() {
        lex_test!("12 + 3"; Nat(12), Plus, Nat(3));
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
    #[allow(overflowing_literals)]
    fn large_number() {
        lex_test!("1111111111111111111111111111111";
                  Nat(1111111111111111111111111111111)
        );
    }
}
