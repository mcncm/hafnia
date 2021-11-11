use crate::{
    cavy_errors::ErrorBuf,
    context::{Context, SymbolId, SymbolInterner},
    num::Uint,
    source::{Span, SrcId, SrcObject, SrcPoint, SrcStore},
    token::{
        Delim,
        Lexeme::{self, Ident, Nat, Tick},
        Token, Unsigned,
    },
};
use std::{
    collections::HashMap,
    fmt,
    iter::Peekable,
    path::{Path, PathBuf},
    str::Chars,
    vec::Vec,
};

/// Main entry point for scanning
pub fn tokenize(src_id: SrcId, ctx: &mut Context) -> Result<Vec<Token>, ErrorBuf> {
    Scanner::new(src_id, ctx).tokenize()
}

fn keyword(kw: &str) -> Option<Lexeme> {
    let lexeme = match kw {
        "if" => Lexeme::If,
        "match" => Lexeme::Match,
        "else" => Lexeme::Else,
        "for" => Lexeme::For,
        "let" => Lexeme::Let,
        "mut" => Lexeme::Mut,
        "in" => Lexeme::In,
        "fn" => Lexeme::Fn,
        "Fn" => Lexeme::FFn,
        "struct" => Lexeme::Struct,
        "enum" => Lexeme::Enum,
        "type" => Lexeme::Type,
        "impl" => Lexeme::Impl,
        "io" => Lexeme::Io,
        "true" => Lexeme::True,
        "false" => Lexeme::False,
        "unsafe" => Lexeme::Unsafe,
        "assert" => Lexeme::Assert,
        "drop" => Lexeme::Drop,
        _ => return None,
    };
    Some(lexeme)
}

fn sctokens(ch: char) -> Option<Lexeme> {
    let lexeme = match ch {
        '+' => Lexeme::Plus,
        '-' => Lexeme::Minus,
        '*' => Lexeme::Star,
        '%' => Lexeme::Percent,
        '~' => Lexeme::Tilde,
        '=' => Lexeme::Equal,
        ',' => Lexeme::Comma,
        '.' => Lexeme::Dot,
        '!' => Lexeme::Bang,
        '$' => Lexeme::Dollar,
        '?' => Lexeme::Question,
        ';' => Lexeme::Semicolon,
        ':' => Lexeme::Colon,
        '[' => Lexeme::LDelim(Delim::Bracket),
        ']' => Lexeme::RDelim(Delim::Bracket),
        '(' => Lexeme::LDelim(Delim::Paren),
        ')' => Lexeme::RDelim(Delim::Paren),
        '{' => Lexeme::LDelim(Delim::Brace),
        '}' => Lexeme::RDelim(Delim::Brace),
        '<' => Lexeme::LAngle,
        '>' => Lexeme::RAngle,
        '#' => Lexeme::Octothorpe,
        '&' => Lexeme::Ampersand,
        '^' => Lexeme::Carot,
        _ => return None,
    };
    Some(lexeme)
}

fn tctokens(chars: (char, char)) -> Option<Lexeme> {
    let lexeme = match chars {
        ('.', '.') => Lexeme::DotDot,
        ('=', '=') => Lexeme::EqualEqual,
        ('~', '=') => Lexeme::TildeEqual,
        ('&', '=') => Lexeme::AmpEqual,
        ('|', '=') => Lexeme::VertEqual,
        ('^', '=') => Lexeme::CarotEqual,
        ('-', '>') => Lexeme::MinusRAngle,
        ('<', '-') => Lexeme::LAngleMinus,
        ('=', '>') => Lexeme::EqualRAngle,
        (':', ':') => Lexeme::ColonColon,
        ('|', '|') => Lexeme::VertVert,
        ('&', '&') => Lexeme::AmpAmp,
        _ => return None,
    };
    Some(lexeme)
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
    pub pos: usize, // absolute position in source
}

impl<'src> ScanHead<'src> {
    fn new(src: Peekable<Chars<'src>>, newlines: &'src mut Vec<usize>) -> Self {
        Self {
            src,
            newlines,
            pos: 0,
        }
    }

    /// Advance to the next source character, not ignoring whitespace. If there
    /// is a character, return it.
    fn next_raw_char(&mut self) -> Option<char> {
        let next = self.src.next();
        if let Some(ch) = next {
            if ch == '\n' {
                self.newlines.push(self.pos);
            }
            self.pos += 1;
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

    fn finish_block_comment(&mut self) {
        loop {
            match self.next_raw_char() {
                Some('/') => {
                    if let Some('*') = self.peek() {
                        self.next_raw_char();
                        self.finish_block_comment();
                    }
                }
                Some('*') => {
                    if let Some('/') = self.peek() {
                        self.next_raw_char();
                        break;
                    }
                }
                None => break,
                _ => {}
            }
        }
    }
}

impl<'src> Iterator for ScanHead<'src> {
    type Item = (SrcPoint, char);

    // Advance the scan head to the next character, filtering whitespace.
    fn next(&mut self) -> Option<(SrcPoint, char)> {
        while let (pt, Some(ch)) = (self.pos, self.next_raw_char()) {
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
    chars: String,
}

impl TokenBuf {
    fn new() -> Self {
        Self {
            start: SrcPoint::default(),
            // Again, this state is invalid at program start--but it's not a problem!
            point: SrcPoint::default(),
            chars: String::new(),
        }
    }

    fn push(&mut self, ch: (SrcPoint, char)) {
        self.point = ch.0;
        self.chars.push(ch.1);
    }

    fn digest(&mut self) -> String {
        std::mem::replace(&mut self.chars, String::new())
    }

    fn clear(&mut self) {
        self.chars.clear();
    }
}

pub struct Scanner<'s> {
    // Scanner data
    scan_head: ScanHead<'s>,
    src_id: SrcId,
    symbols: &'s mut SymbolInterner,
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

impl<'s, 'c> Scanner<'s> {
    pub fn new(src_id: SrcId, ctx: &'s mut Context<'c>) -> Self {
        let src = &mut ctx.srcs[src_id];
        let symbols = &mut ctx.symbols;
        Scanner {
            scan_head: ScanHead::new(src.code.chars().peekable(), &mut src.newlines),
            src_id,
            symbols,
            token_buf: TokenBuf::new(),
            tokens: vec![],
            errors: ErrorBuf::new(),
        }
    }

    /// Get a single-character Span at the current point
    fn loc_span(&self) -> Span {
        let pt = self.scan_head.pos;
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
        let loc = self.scan_head.pos;
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
        let loc = self.scan_head.pos;
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
            self.token_buf.start = self.scan_head.pos;
            if let Some(next_ch) = self.next_char() {
                ch = next_ch;
            } else {
                break;
            }

            // Greedily check for two-character tokens
            if let Some(&following) = self.scan_head.peek() {
                if let Some(lexeme) = tctokens((ch, following)) {
                    // Consume the second character *first* to make sure the
                    // source span is right.
                    self.next_char();
                    let lexeme = lexeme.clone();
                    push_token!(self, lexeme);
                    continue;
                } else if (ch, following) == ('/', '/') {
                    // In a comment: proceed to the next line
                    self.scan_head.advance_to_newline();
                    self.token_buf.clear();
                    continue;
                } else if (ch, following) == ('/', '*') {
                    self.scan_head.next_raw_char();
                    self.token_buf.clear();
                    self.scan_head.finish_block_comment();
                    continue;
                } else if ch == '\'' && is_ident_char(following) {
                    // Or this could be a lifetime token!
                    self.consume_lifetime();
                    continue;
                }
            }
            // Single-character tokens
            if let Some(lexeme) = sctokens(ch) {
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
    /// vector, or adds an error. `Nat`s must consist solely of ascii digits
    /// followed by an optional size specifier.
    fn consume_nat(&mut self) {
        let sz = None;
        while let Some(ch) = self.scan_head.peek() {
            if ch.is_ascii_digit() {
                self.next_char();
            } else if is_ident_char(*ch) {
                self.errors.push(errors::NonDigitInNumber {
                    span: self.loc_span(),
                });
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
            push_token!(self, Nat(value, sz));
        } else {
            self.errors.push(errors::UnparsableNumber {
                span: self.token_span(),
            });
            self.token_buf.clear();
        }
    }

    /// Either completes an identifier or keyword and adds it to the Scanner's
    /// `tokens` vector, or adds an error. Idents must begin with an alphabetic
    /// character, and may be followed by alphabetic and numeric characters.
    fn consume_ident(&mut self) {
        self.consume_ident_chars();
        if let Some(kw) = keyword(&self.token_buf.chars) {
            self.token_buf.clear();
            push_token!(self, kw);
        } else {
            let ident = self.digest_symbol();
            push_token!(self, Ident(ident));
        }
    }

    /// We already know that a lifetime is next, but haven't eaten any of the
    /// characters yet.
    fn consume_lifetime(&mut self) {
        self.token_buf.clear();
        self.consume_ident_chars();
        let lt = self.digest_symbol();
        push_token!(self, Tick(lt));
    }

    /// Produce a symbol from the characters currently in the token buffer
    fn digest_symbol(&mut self) -> SymbolId {
        let string = self.token_buf.digest();
        self.symbols.intern(string)
    }

    /// Eat identifier characters for long as you find them
    fn consume_ident_chars(&mut self) {
        while let Some(ch) = self.scan_head.peek() {
            if is_ident_char(*ch) {
                self.next_char();
            } else {
                break;
            }
        }
    }
}

mod errors {
    use crate::cavy_errors::Diagnostic;
    use crate::source::Span;
    use cavy_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[msg = "numeric literals may only contain digits"]
    pub struct NonDigitInNumber {
        #[span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[msg = "unparsable number"]
    pub struct UnparsableNumber {
        #[span]
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

            default_context!(ctx);
            let id = ctx.srcs.insert(SrcObject::from($code));
            let tokens = Scanner::new(id, &mut ctx).tokenize().unwrap();

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
        assert_eq!(token.span.start, start);
        assert_eq!(token.span.end, end);
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
        use crate::token::Delim::*;
        lex_test!("+ * ~ , . ! ? ; [ ] ( ) { }";
                  Plus, Star, Tilde, Comma, Dot, Bang, Question, Semicolon,
                  LDelim(Bracket), RDelim(Bracket),
                  LDelim(Paren), RDelim(Paren),
                  LDelim(Brace), RDelim(Brace));
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
        lex_test!("12 + 3 * 0"; Nat(12, None), Plus, Nat(3, None), Star, Nat(0, None));
    }

    #[test]
    fn numbers_equality() {
        lex_test!("1 == 1"; Nat(1, None), EqualEqual, Nat(1, None));
    }

    #[test]
    fn numbers_equality_no_whitespace() {
        lex_test!("2==2"; Nat(2, None), EqualEqual, Nat(2, None));
    }
    #[test]
    fn numbers_inequality() {
        lex_test!("3 ~= 3"; Nat(3, None), TildeEqual, Nat(3, None));
    }

    #[test]
    fn numbers_no_whitespace() {
        lex_test!("12*3"; Nat(12, None), Star, Nat(3, None));
    }

    // These `should_panic` tests are insufficiently sensitive: they don't in
    // any way validate the origin or nature of the error.

    #[test]
    #[should_panic]
    fn invalid_number_1() {
        lex_test!("123if234"; Nat(123, None), If, Nat(234, None));
    }

    #[test]
    #[should_panic]
    fn invalid_number_2() {
        lex_test!("123else"; Nat(123, None), Else);
    }

    #[test]
    #[should_panic]
    #[allow(overflowing_literals)]
    fn large_number() {
        lex_test!("1111111111111111111111111111111";
                  Nat(1111111111111111111111111111111, None)
        );
    }

    #[test]
    #[rustfmt::skip]
    fn ident_keywords() {
        lex_test!("if else for let fn true false";
                  If, Else, For, Let, Fn, True, False);
    }

    ///////////
    // Spans //
    ///////////

    #[test]
    fn spans_correct() {
        default_context!(ctx);
        let id = ctx.srcs.insert(SrcObject::from("fn hello()"));
        let scanner = Scanner::new(id, &mut ctx);
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
                  Nat(1, None), Plus, Nat(2, None)
        );
    }
}
