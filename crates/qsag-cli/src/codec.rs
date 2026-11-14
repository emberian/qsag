//! Hex and a minimal strict JSON reader/writer. Output is deterministic: object members are
//! written in insertion order with no insignificant whitespace variation.

use crate::cli::CliError;

pub fn to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0F) as usize] as char);
    }
    out
}

/// Strict hex: even length, `[0-9a-fA-F]` only. Surrounding ASCII whitespace is ignored.
pub fn from_hex(text: &str) -> Result<crate::cli::ZeroizingBuf, CliError> {
    let text = text.trim();
    if !text.len().is_multiple_of(2) {
        return Err(CliError::input("hex string has odd length"));
    }
    let nibble = |c: u8| match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        _ => Err(CliError::input("hex string contains a non-hex character")),
    };
    let mut decoded = crate::cli::ZeroizingBuf(Vec::with_capacity(text.len() / 2));
    for pair in text.as_bytes().as_chunks::<2>().0 {
        decoded.0.push(nibble(pair[0])? << 4 | nibble(pair[1])?);
    }
    Ok(decoded)
}

pub fn from_hex_exact<const N: usize>(text: &str, what: &str) -> Result<[u8; N], CliError> {
    <[u8; N]>::try_from(from_hex(text)?.0.as_slice())
        .map_err(|_| CliError::input(format!("{what} must be exactly {N} bytes of hex")))
}

pub fn from_hex_secret32(text: &str, what: &str) -> Result<crate::cli::Secret32, CliError> {
    let decoded = from_hex(text)?;
    if decoded.len() != 32 {
        return Err(CliError::input(format!(
            "{what} must be exactly 32 bytes of hex"
        )));
    }
    let mut secret = crate::cli::Secret32([0u8; 32]);
    secret.0.copy_from_slice(&decoded);
    Ok(secret)
}

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// Kept as its source digits so 64-bit and larger integers survive unchanged.
    Number(String),
    Str(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

// Wipe owned strings recursively, including partially parsed secret containers.
impl Drop for Json {
    fn drop(&mut self) {
        if let Self::Str(s) | Self::Number(s) = self {
            let _wipe = crate::cli::ZeroizingBuf(std::mem::take(s).into_bytes());
        }
    }
}

impl Json {
    pub fn object(members: Vec<(&str, Json)>) -> Json {
        Json::Object(
            members
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
        )
    }
    pub fn str(text: impl Into<String>) -> Json {
        Json::Str(text.into())
    }
    pub fn hex(bytes: &[u8]) -> Json {
        Json::Str(to_hex(bytes))
    }
    pub fn num(value: impl std::fmt::Display) -> Json {
        Json::Number(value.to_string())
    }

    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Object(members) => members.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Array(items) => Some(items),
            _ => None,
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Json::Number(n) => n.parse().ok(),
            _ => None,
        }
    }

    /// Required string member of an object.
    pub fn field_str(&self, key: &str) -> Result<&str, CliError> {
        self.get(key)
            .and_then(Json::as_str)
            .ok_or_else(|| CliError::input(format!("missing or non-string field \"{key}\"")))
    }
    pub fn field_u64(&self, key: &str) -> Result<u64, CliError> {
        self.get(key)
            .and_then(Json::as_u64)
            .ok_or_else(|| CliError::input(format!("missing or non-integer field \"{key}\"")))
    }
    pub fn field_hex(&self, key: &str) -> Result<crate::cli::ZeroizingBuf, CliError> {
        from_hex(self.field_str(key)?)
    }

    pub fn write(&self, out: &mut String, indent: usize) {
        let pad = |out: &mut String, depth: usize| {
            out.push('\n');
            out.extend(std::iter::repeat_n(' ', depth * 2));
        };
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Number(n) => out.push_str(n),
            Json::Str(s) => write_string(out, s),
            Json::Array(items) if items.is_empty() => out.push_str("[]"),
            Json::Array(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    pad(out, indent + 1);
                    item.write(out, indent + 1);
                }
                pad(out, indent);
                out.push(']');
            }
            Json::Object(members) if members.is_empty() => out.push_str("{}"),
            Json::Object(members) => {
                out.push('{');
                for (i, (key, value)) in members.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    pad(out, indent + 1);
                    write_string(out, key);
                    out.push_str(": ");
                    value.write(out, indent + 1);
                }
                pad(out, indent);
                out.push('}');
            }
        }
    }

    fn encoded_len(&self, indent: usize) -> usize {
        let pad_len = |depth: usize| 1 + depth * 2;
        match self {
            Json::Null => 4,
            Json::Bool(b) => if *b { 4 } else { 5 },
            Json::Number(n) => n.len(),
            Json::Str(s) => escaped_string_len(s),
            Json::Array(items) if items.is_empty() => 2,
            Json::Array(items) => {
                let mut total = 1;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        total += 1;
                    }
                    total += pad_len(indent + 1) + item.encoded_len(indent + 1);
                }
                total + pad_len(indent) + 1
            }
            Json::Object(members) if members.is_empty() => 2,
            Json::Object(members) => {
                let mut total = 1;
                for (i, (key, value)) in members.iter().enumerate() {
                    if i > 0 {
                        total += 1;
                    }
                    total += pad_len(indent + 1)
                        + escaped_string_len(key)
                        + 2
                        + value.encoded_len(indent + 1);
                }
                total + pad_len(indent) + 1
            }
        }
    }

    pub fn to_pretty(&self) -> String {
        let exact = self.encoded_len(0) + 1;
        let mut out = String::with_capacity(exact);
        self.write(&mut out, 0);
        out.push('\n');
        debug_assert_eq!(out.len(), exact);
        out
    }

    pub fn parse(text: &str) -> Result<Json, CliError> {
        let mut parser = Parser {
            bytes: text.as_bytes(),
            pos: 0,
            depth: 0,
        };
        let value = parser.value()?;
        parser.skip_ws();
        if parser.pos != parser.bytes.len() {
            return Err(parser.error("trailing data after JSON value"));
        }
        Ok(value)
    }
}

fn escaped_string_len(s: &str) -> usize {
    let mut len = 2;
    for c in s.chars() {
        len += match c {
            '"' | '\\' | '\n' | '\r' | '\t' => 2,
            c if (c as u32) < 0x20 => 6,
            c => c.len_utf8(),
        };
    }
    len
}

fn write_string(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

struct Parser<'a> {
    bytes: &'a [u8],
    pos: usize,
    depth: usize,
}

impl Parser<'_> {
    const MAX_DEPTH: usize = 32;

    fn error(&self, what: &str) -> CliError {
        CliError::input(format!("invalid JSON at byte {}: {what}", self.pos))
    }
    fn skip_ws(&mut self) {
        while matches!(self.bytes.get(self.pos), Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.pos += 1;
        }
    }
    fn expect(&mut self, byte: u8) -> Result<(), CliError> {
        if self.bytes.get(self.pos) == Some(&byte) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.error(&format!("expected '{}'", byte as char)))
        }
    }
    fn literal(&mut self, word: &str, value: Json) -> Result<Json, CliError> {
        if self.bytes[self.pos..].starts_with(word.as_bytes()) {
            self.pos += word.len();
            Ok(value)
        } else {
            Err(self.error("unknown literal"))
        }
    }
    fn value(&mut self) -> Result<Json, CliError> {
        self.skip_ws();
        match self.bytes.get(self.pos).copied() {
            Some(b'{') => self.nested(|p| p.object()),
            Some(b'[') => self.nested(|p| p.array()),
            Some(b'"') => self.string().map(Json::Str),
            Some(b't') => self.literal("true", Json::Bool(true)),
            Some(b'f') => self.literal("false", Json::Bool(false)),
            Some(b'n') => self.literal("null", Json::Null),
            Some(b'-' | b'0'..=b'9') => self.number(),
            _ => Err(self.error("expected a value")),
        }
    }
    fn nested(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<Json, CliError>,
    ) -> Result<Json, CliError> {
        if self.depth >= Self::MAX_DEPTH {
            return Err(self.error("nesting too deep"));
        }
        self.depth += 1;
        let value = f(self);
        self.depth -= 1;
        value
    }
    fn object(&mut self) -> Result<Json, CliError> {
        self.expect(b'{')?;
        let mut members: Vec<(String, Json)> = Vec::new();
        self.skip_ws();
        if self.bytes.get(self.pos) == Some(&b'}') {
            self.pos += 1;
            return Ok(Json::Object(members));
        }
        loop {
            self.skip_ws();
            let key = self.string()?;
            if members.iter().any(|(k, _)| *k == key) {
                return Err(self.error("duplicate object key"));
            }
            self.skip_ws();
            self.expect(b':')?;
            members.push((key, self.value()?));
            self.skip_ws();
            match self.bytes.get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(Json::Object(members));
                }
                _ => return Err(self.error("expected ',' or '}'")),
            }
        }
    }
    fn array(&mut self) -> Result<Json, CliError> {
        self.expect(b'[')?;
        let mut items = Vec::new();
        self.skip_ws();
        if self.bytes.get(self.pos) == Some(&b']') {
            self.pos += 1;
            return Ok(Json::Array(items));
        }
        loop {
            items.push(self.value()?);
            self.skip_ws();
            match self.bytes.get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(Json::Array(items));
                }
                _ => return Err(self.error("expected ',' or ']'")),
            }
        }
    }
    fn string(&mut self) -> Result<String, CliError> {
        self.expect(b'"')?;
        // Scan forward to the closing quote so secret-bearing strings allocate their
        // bounded capacity once and never leave unwiped reallocation remnants.
        let mut scan = self.pos;
        let mut max_decoded_len = 0usize;
        loop {
            let b = *self
                .bytes
                .get(scan)
                .ok_or_else(|| self.error("unterminated string"))?;
            scan += 1;
            match b {
                b'"' => break,
                b'\\' => {
                    let esc = *self
                        .bytes
                        .get(scan)
                        .ok_or_else(|| self.error("unterminated escape"))?;
                    scan += 1;
                    if esc == b'u' {
                        scan = scan.saturating_add(4);
                        max_decoded_len += 4;
                    } else {
                        max_decoded_len += 1;
                    }
                }
                _ => max_decoded_len += 1,
            }
        }
        let mut out = crate::cli::ZeroizingBuf(Vec::with_capacity(max_decoded_len));
        loop {
            let byte = *self
                .bytes
                .get(self.pos)
                .ok_or_else(|| self.error("unterminated string"))?;
            self.pos += 1;
            match byte {
                b'"' => break,
                b'\\' => {
                    let escape = *self
                        .bytes
                        .get(self.pos)
                        .ok_or_else(|| self.error("unterminated escape"))?;
                    self.pos += 1;
                    match escape {
                        b'"' | b'\\' | b'/' => out.0.push(escape),
                        b'n' => out.0.push(b'\n'),
                        b'r' => out.0.push(b'\r'),
                        b't' => out.0.push(b'\t'),
                        b'u' => {
                            let digits = self
                                .bytes
                                .get(self.pos..self.pos + 4)
                                .and_then(|d| std::str::from_utf8(d).ok())
                                .and_then(|d| u32::from_str_radix(d, 16).ok())
                                .and_then(char::from_u32)
                                .ok_or_else(|| self.error("invalid \\u escape"))?;
                            self.pos += 4;
                            out.0
                                .extend_from_slice(digits.encode_utf8(&mut [0; 4]).as_bytes());
                        }
                        _ => return Err(self.error("unsupported escape")),
                    }
                }
                0..=0x1F => return Err(self.error("control character in string")),
                other => out.0.push(other),
            }
        }
        std::str::from_utf8(&out.0)
            .map(str::to_owned)
            .map_err(|_| self.error("string is not UTF-8"))
    }
    fn number(&mut self) -> Result<Json, CliError> {
        let start = self.pos;
        while matches!(
            self.bytes.get(self.pos),
            Some(b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9')
        ) {
            self.pos += 1;
        }
        let text = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| self.error("invalid number"))?;
        let digits = text.strip_prefix('-').unwrap_or(text);
        if digits.is_empty()
            || !digits.bytes().all(|b| b.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return Err(self.error("only canonical integers are supported"));
        }
        Ok(Json::Number(text.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_roundtrip_and_rejections() {
        assert_eq!(from_hex(" 00ffA5\n").unwrap().0, vec![0, 255, 0xA5]);
        assert_eq!(to_hex(&[0, 255, 0xA5]), "00ffa5");
        assert!(from_hex("abc").is_err());
        assert!(from_hex("zz").is_err());
        assert!(from_hex_exact::<2>("00", "x").is_err());
    }

    #[test]
    fn json_roundtrip_is_deterministic_and_strict() {
        let value = Json::object(vec![
            ("b", Json::num(18446744073709551615u64)),
            (
                "a",
                Json::Array(vec![Json::Bool(true), Json::Null, Json::str("x\"\n")]),
            ),
            ("empty", Json::Object(Vec::new())),
        ]);
        let text = value.to_pretty();
        assert_eq!(Json::parse(&text).unwrap(), value);
        assert_eq!(Json::parse(&text).unwrap().to_pretty(), text);
        assert_eq!(value.field_u64("b").unwrap(), u64::MAX);
        for bad in [
            "{\"a\":1,\"a\":2}",
            "{\"a\":01}",
            "[1,]",
            "{} x",
            "\"\\q\"",
            "1.5",
            "",
        ] {
            assert!(Json::parse(bad).is_err(), "{bad}");
        }
        let deep = "[".repeat(40) + &"]".repeat(40);
        assert!(Json::parse(&deep).is_err());
    }
}
