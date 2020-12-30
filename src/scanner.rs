use crate::source::{Span, SrcId, SrcObject, SrcPoint};
use crate::token::Lexeme::{Ident, Nat};
use crate::{
    cavy_errors::ErrorBuf,
    token::{Lexeme, Token, Unsigned},
};
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::iter::Peekable;
use std::path::{Path, PathBuf};
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
        m.insert("in",    Lexeme::In);
        m.insert("fn",    Lexeme::Fn);
        m.insert("print", Lexeme::Print);
        m.insert("true",  Lexeme::True);
        m.insert("false", Lexeme::False);
        m.insert("bool",  Lexeme::Bool);
        m.insert("u4",    Lexeme::U4);
        m.insert("u8",    Lexeme::U8);
        m.insert("u16",   Lexeme::U16);
        m.insert("u32",   Lexeme::U32);
        m
    };
    static ref SCTOKENS: HashMap<char, Lexeme> = {
        let mut m = HashMap::new();
        m.insert('+', Lexeme::Plus);
        m.insert('-', Lexeme::Minus);
        m.insert('*', Lexeme::Star);
        m.insert('%', Lexeme::Percent);
        m.insert('~', Lexeme::Tilde);
        m.insert('=', Lexeme::Equal);
        m.insert(',', Lexeme::Comma);
        m.insert('!', Lexeme::Bang);
        m.insert('?', Lexeme::Question);
        m.insert(';', Lexeme::Semicolon);
        m.insert(':', Lexeme::Colon);
        m.insert('[', Lexeme::LBracket);
        m.insert(']', Lexeme::RBracket);
        m.insert('(', Lexeme::LParen);
        m.insert(')', Lexeme::RParen);
        m.insert('{', Lexeme::LBrace);
        m.insert('}', Lexeme::RBrace);
        m.insert('<', Lexeme::LAngle);
        m.insert('>', Lexeme::RAngle);
        m
    };
    static ref TCTOKENS: HashMap<(char, char), Lexeme> = {
        let mut m = HashMap::new();
        m.insert(('.', '.'), Lexeme::DotDot);
        m.insert(('=', '='), Lexeme::EqualEqual);
        m.insert(('~', '='), Lexeme::TildeEqual);
        m.insert(('-', '>'), Lexeme::MinusRAngle);
        m
    };
}

/// Characters that are allowed in identifiers
fn is_ident_char(ch: char) -> bool {
    ch.is_alphanumeric() | (ch == '_')
}

struct ScanHead<'src> {
    /// The source code, borrowed immutably from the SrcObject
    src: Peekable<Chars<'src>>,
    /// The newlines from the SrcObject, to be filled in as the ScanHead passes
    /// over them.
    newlines: &'src mut Vec<usize>,
    pub pos: usize,  // absolute position in source
    pub line: usize, // line number in source
    pub col: usize,  // column number in source
}

impl<'src> ScanHead<'src> {
    fn new(src: Peekable<Chars<'src>>, newlines: &'src mut Vec<usize>) -> Self {
        Self {
            src,
            newlines,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn loc(&self) -> SrcPoint {
        SrcPoint {
            pos: self.pos,
            line: self.line,
            col: self.col,
        }
    }

    /// Advance to the next source character, not ignoring whitespace. If there
    /// is a character, return it.
    fn next_raw_char(&mut self) -> Option<char> {
        let next = self.src.next();
        if let Some(ch) = next {
            self.pos += 1;
            self.col += 1;
            if ch == '\n' {
                self.newlines.push(self.pos);
                self.line += 1;
                self.col = 1;
            }
        }
        next
    }

    /// Advance the scan head to the next occurrence of a specific (raw)
    /// character, not ignoring whitespace.
    fn advance_to(&mut self, target: char) {
        while let Some(ch) = self.next_raw_char() {
            if ch == target {
                break;
            }
        }
    }

    /// Advance until reaching a newline character. This might not work if
    /// newlines are `\r\n`.
    pub fn advance_to_newline(&mut self) {
        self.advance_to('\n');
    }

    /// Advance until the next raw character is not a whitespace character
    fn advance_to_non_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_ascii_whitespace() {
                self.next_raw_char();
            } else {
                break;
            }
        }
    }

    /// Noke that this isn't an implementation of Peekable; the return type is
    /// different from that of `next`. This is probably a flaw.
    fn peek(&mut self) -> Option<&char> {
        self.src.peek()
    }
}

impl<'src> Iterator for ScanHead<'src> {
    type Item = (SrcPoint, char);

    // Advance the scan head to the next character, filtering whitespace.
    fn next(&mut self) -> Option<(SrcPoint, char)> {
        while let (pt, Some(ch)) = (self.loc(), self.next_raw_char()) {
            if !ch.is_ascii_whitespace() {
                return Some((pt, ch));
            }
        }
        None
    }
}

pub struct TokenBuf {
    /// The point of the first char in the currenly buffer
    start: SrcPoint,
    /// The current point in the current buffer. Note that this is not always in
    /// a "valid" state: at the beginning of parsing, both `start` and `point`
    /// are the zero point, but there are no characters in the buffer. Only when
    /// the first character is pushed does that state become valid. However, it
    /// should never result in an incorrect span ending up in the AST.
    point: SrcPoint,
    // NOTE this doesn't need to be a Vec<char>; it could just be a pointer
    // pair, if you replace the source code iterator with a simple &str.
    chars: Vec<char>,
}

impl TokenBuf {
    fn new() -> Self {
        Self {
            start: SrcPoint::default(),
            // Again, this state is invalid at program start--but it's not a problem!
            point: SrcPoint::default(),
            chars: vec![],
        }
    }

    fn push(&mut self, ch: (SrcPoint, char)) {
        self.point = ch.0;
        self.chars.push(ch.1);
    }

    fn digest(&mut self) -> String {
        self.chars.iter().collect()
    }

    fn clear(&mut self) {
        self.chars.clear();
    }
}

pub struct Scanner<'src> {
    // Scanner data
    scan_head: ScanHead<'src>,
    src_id: SrcId,
    token_buf: TokenBuf,
    tokens: Vec<Token>,
    errors: ErrorBuf,
}

// Adds a lexed token to a Scanner's `tokens` vector.
macro_rules! push_token {
    ($self:ident, $tok:ident$(($($arg:expr),*))?) => {
        let span = $self.token_span();
        $self.tokens.push(Token {
            lexeme: $tok$(($($arg),+))?,
            span,
        });
        $self.scan_head.advance_to_non_whitespace();
        $self.token_buf.clear();
    };
}

impl<'s> Scanner<'s> {
    pub fn new(src: &'s mut SrcObject) -> Self {
        Scanner {
            scan_head: ScanHead::new(src.code.chars().peekable(), &mut src.newlines),
            src_id: src.id,
            token_buf: TokenBuf::new(),
            tokens: vec![],
            errors: ErrorBuf::new(),
        }
    }

    /// Get a single-character Span at the current point
    fn loc_span(&self) -> Span {
        let pt = self.scan_head.loc();
        Span {
            start: pt,
            end: pt,
            src_id: self.src_id,
        }
    }

    /// The current Span between from token start to the current point
    fn token_span(&self) -> Span {
        Span {
            start: self.token_buf.start,
            end: self.token_buf.point,
            src_id: self.src_id,
        }
    }

    fn next_char(&mut self) -> Option<char> {
        self.scan_head.next().map(|(pt, ch)| {
            self.token_buf.push((pt, ch));
            ch
        })
    }

    /// Advance the scan head to the next whitespace character, and return
    /// position before advancing.
    pub fn synchronize_to_whitespace(&mut self) -> SrcPoint {
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

    /// Advance the scan head to the next non-alphanumeric character, and return
    /// position before advancing. Here, 'alphanumeric' is understood as an
    /// 'identifier' character, which includes `_`.
    pub fn synchronize_to_non_alphanum(&mut self) -> SrcPoint {
        let loc = self.scan_head.loc();
        while let Some(ch) = self.scan_head.peek() {
            if is_ident_char(*ch) {
                self.next_char();
            } else {
                break;
            }
        }
        loc
    }

    /// This method, which consumes the `Scanner`, produces either a vector of
    /// tokens or of representable errors that the caller is expected, in one
    /// way or another, to display to the user.
    pub fn tokenize(mut self) -> Result<Vec<Token>, ErrorBuf> {
        let mut ch;
        loop {
            // The invariant for this loop is that we're beginning a new token
            // on each iteration. However, there's no way to add an assertion
            // for this condition while using `while let` syntax. This is
            // probably fine for now.
            self.token_buf.start = self.scan_head.loc();
            if let Some(next_ch) = self.next_char() {
                ch = next_ch;
            } else {
                break;
            }

            // Greedily check for two-character tokens
            if let Some(&following) = self.scan_head.peek() {
                if let Some(lexeme) = TCTOKENS.get(&(ch, following)) {
                    let lexeme = lexeme.clone();
                    push_token!(self, lexeme);
                    // Consume the second character and loop again.
                    self.scan_head.next_raw_char();
                    continue;
                } else if (ch, following) == ('/', '/') {
                    // In a comment: proceed to the next line
                    self.token_buf.clear(); // The buffer has a '/' in it.
                    self.scan_head.advance_to_newline();
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
            // Or it could be a keyword or identifier. Identifiers must start
            // with an alphabetic character, but can contain alphanumeric
            // characters and underscores.
            else if ch.is_alphabetic() {
                self.consume_ident();
            }
        }

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
            } else if is_ident_char(*ch) {
                self.errors.push(Box::new(errors::NonDigitInNumber {
                    span: self.loc_span(),
                }));
                self.synchronize_to_non_alphanum();
                self.token_buf.clear();
                return;
            } else {
                break;
            }
        }

        // Shouldn't fail except for numbers larger than an `Unsigned`!
        let value: Result<Unsigned, _> = self.token_buf.digest().parse();
        if let Ok(value) = value {
            push_token!(self, Nat(value));
        } else {
            self.errors.push(Box::new(errors::UnparsableNumber {
                span: self.token_span(),
            }));
            self.token_buf.clear();
        }
    }

    /// Either completes an identifier or keyword and adds it to the Scanner's
    /// `tokens` vector, or adds an error. Idents must begin with an alphabetic
    /// character, and may be followed by alphabetic and numeric characters.
    fn consume_ident(&mut self) {
        while let Some(ch) = self.scan_head.peek() {
            if is_ident_char(*ch) {
                self.next_char();
            } else {
                break;
            }
        }

        let ident: String = self.token_buf.digest();
        if let Some(keyword) = KEYWORDS.get(ident.as_str()) {
            let keyword = keyword.clone();
            push_token!(self, keyword);
        } else {
            push_token!(self, Ident(ident));
        }
    }
}

mod errors {
    use crate::cavy_errors::Diagnostic;
    use crate::source::Span;
    use cavy_macros::Diagnostic;
    // This will become redundant when diagnostics only implement `Diagnostic`
    use std::error::Error;

    #[derive(Diagnostic)]
    pub struct NonDigitInNumber {
        #[msg = "numeric literals may only contain digits"]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    pub struct UnparsableNumber {
        #[msg = "unparsable number"]
        pub span: Span,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests sample code against a sequence of token types. In more
    /// human-readable form, the syntax looks like:
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

            let mut src = SrcObject::from($code);
            let scanner = Scanner::new(&mut src);
            let tokens = scanner.tokenize().unwrap();

            assert_eq!(tokens.len(), expected_tokens.len(), "expected same number of tokens.");

            let token_pairs = tokens
                .into_iter()
                .map(|token| token.lexeme)
                .zip(expected_tokens);

            for (token, expected_token) in token_pairs {
                assert_eq!(token, expected_token, "tokens are not the same.");
            }
        };
    }

    fn check_span(token: &Token, start: usize, end: usize) {
        assert_eq!(token.span.start.pos, start);
        assert_eq!(token.span.end.pos, end);
    }

    //////////////////////////////////
    // Basic tests: token detection //
    //////////////////////////////////

    #[test]
    #[should_panic]
    fn lex_test_works() {
        lex_test!("!"; Star);
    }

    #[test]
    #[rustfmt::skip]
    fn single_character_tokens() {
        lex_test!("+ * ~ , ! ? ; [ ] ( ) { }";
                  Plus, Star, Tilde, Comma, Bang, Question, Semicolon,
                  LBracket, RBracket, LParen, RParen, LBrace, RBrace);
    }

    #[test]
    fn two_character_tokens() {
        lex_test!(".. == ~="; DotDot, EqualEqual, TildeEqual);
    }

    #[test]
    fn whitespace() {
        lex_test!("+    +\n+\t\t\t+"; Plus, Plus, Plus, Plus);
    }

    ///////////////////
    // Numeric tests //
    ///////////////////

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

    //////////////////////////////
    // Identifier-related tests //
    //////////////////////////////

    #[test]
    fn ident_simple() {
        lex_test!("ihtfp"; Ident(String::from("ihtfp")));
    }

    #[test]
    fn ident_trailing_numbers() {
        lex_test!("foo1"; Ident(String::from("foo1")));
    }

    #[test]
    fn ident_underscore() {
        lex_test!("foo_bar"; Ident(String::from("foo_bar")));
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

    ///////////
    // Spans //
    ///////////

    #[test]
    fn spans_correct() {
        let mut src = SrcObject::from("fn hello()");
        let scanner = Scanner::new(&mut src);
        let tokens = scanner.tokenize().unwrap();
        assert_eq!(tokens.len(), 4);
        check_span(&tokens[0], 0, 1);
        check_span(&tokens[1], 3, 7);
        check_span(&tokens[2], 8, 8);
        check_span(&tokens[3], 9, 9);
    }

    //////////////
    // Comments //
    //////////////

    #[test]
    #[allow(unused_mut)]
    fn empty_comment() {
        lex_test!("// I do nothing!"; );
    }

    #[test]
    fn comment_on_own_line() {
        lex_test!("// now do other stuff\n1 + 2";
                  Nat(1), Plus, Nat(2)
        );
    }
}
