use std::collections::HashMap;
use std::str::Chars;
use std::vec::Vec;

use crate::token::TokenType::Eof;
use crate::token::{Location, Token, TokenType};

use lazy_static::lazy_static;

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, TokenType> = {
        let mut m = HashMap::new();
        m.insert("if", TokenType::If);
        m.insert("else", TokenType::Else);
        m.insert("for", TokenType::For);
        m.insert("fn", TokenType::Fn);
        m.insert("reg", TokenType::Reg);
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
    message: String,
}

struct Lexer<'a> {
    code: Chars<'a>,
    token_buf: Vec<char>,

    // Lexer location
    pos: usize,  // absolute position in source
    line: usize, // line number in source
    col: usize,  // column number in source

    // Lexer state
    in_comment: bool,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Lexer {
        Lexer {
            code: source.chars(),
            token_buf: vec![],
            in_comment: false,
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
            len: self.token_buf.len(),
        }
    }

    // Advance the scan head by one character and return it.
    fn next_raw_char(&mut self) -> Option<char> {
        let next = self.code.next();
        if let Some(ch) = next {
            self.token_buf.push(ch);
            self.pos += 1;
            if ch == '\n' {
                self.line += 1;
                self.col = 1;
                self.in_comment = false;
            }
        }
        next
    }

    // Advance the scan head to the next character, filtering whitespace and
    // ignoring comments.
    fn next_char(&mut self) -> Option<char> {
        while let Some(ch) = self.next_raw_char() {
            if !ch.is_ascii_whitespace() & !self.in_comment {
                return Some(ch);
            }
        }
        None
    }

    fn lex(&mut self) -> Result<Vec<Token>, Vec<LexError>> {
        let mut tokens = vec![];

        // This macro adds a token to the `tokens` vector, consuming
        // all the characters in the Lexer's `token_buf`.
        macro_rules! push_token {
            ($tok:ident$(($($arg:expr),*))?) => {
                tokens.push(Token {
                    token_type: $tok$(($($arg),+))?,
                    loc: self.loc(),
                });
                self.token_buf.clear();
            };
        }

        while let Some(ch) = self.next_char() {
            // Single-character tokens
            if let Some(token_type) = SCTOKENS.get(&ch) {
                let token_type = token_type.clone();
                push_token!(token_type);
            }
        }
        // Finally, add the end-of-file sentinel
        push_token!(Eof);
        Ok(tokens)
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

            let mut lexer = Lexer::new($code);
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
    fn lex_single_character_tokens() {
        lex_test!("+ * , ! ? ; [ ] ( ) { }";
                  Plus,  Star, Comma, Bang, QuestionMark, Semicolon,
                  LBracket, RBracket, LParen, RParen, LBrace, RBrace);
    }

    #[test]
    #[rustfmt::skip]
    fn lex_whitespace() {
        lex_test!("+    +\n+\t\t\t+"; Plus, Plus, Plus, Plus);
    }
}
