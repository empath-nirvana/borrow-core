// AWFY Json in miniature, the same input as awfy/json.bc: parse into an owned tree (arrays as
// Vec<Json>, objects as Vec<(String, Json)>), print it back, count the values. Answer 12.
rs::counting!();

enum Json { Null, Bool(bool), Num(i32), Str(String), Arr(Vec<Json>), Obj(Vec<(String, Json)>) }

struct P<'a> { s: &'a [u8], i: usize }

impl<'a> P<'a> {
    fn peek(&self) -> u8 { *self.s.get(self.i).unwrap_or(&0) }
    fn ws(&mut self) { while matches!(self.peek(), b' ' | b'\n' | b'\t' | b'\r') { self.i += 1 } }
    fn string(&mut self) -> String {
        self.i += 1;
        let st = self.i;
        while self.peek() != b'"' { self.i += 1 }
        let r = String::from_utf8_lossy(&self.s[st..self.i]).into_owned();
        self.i += 1;
        r
    }
    fn value(&mut self) -> Result<Json, usize> {
        self.ws();
        match self.peek() {
            b'{' => {
                self.i += 1;
                let mut m = Vec::new();
                self.ws();
                if self.peek() == b'}' { self.i += 1; return Ok(Json::Obj(m)) }
                loop {
                    self.ws();
                    let k = self.string();
                    self.ws();
                    self.i += 1; // ':'
                    let v = self.value()?;
                    m.push((k, v));
                    self.ws();
                    match self.peek() { b',' => self.i += 1, b'}' => { self.i += 1; return Ok(Json::Obj(m)) } _ => return Err(self.i) }
                }
            }
            b'[' => {
                self.i += 1;
                let mut a = Vec::new();
                self.ws();
                if self.peek() == b']' { self.i += 1; return Ok(Json::Arr(a)) }
                loop {
                    a.push(self.value()?);
                    self.ws();
                    match self.peek() { b',' => self.i += 1, b']' => { self.i += 1; return Ok(Json::Arr(a)) } _ => return Err(self.i) }
                }
            }
            b'"' => Ok(Json::Str(self.string())),
            b't' => { self.i += 4; Ok(Json::Bool(true)) }
            b'f' => { self.i += 5; Ok(Json::Bool(false)) }
            b'n' => { self.i += 4; Ok(Json::Null) }
            b'-' | b'0'..=b'9' => {
                let neg = self.peek() == b'-';
                if neg { self.i += 1 }
                let mut v = 0i32;
                while self.peek().is_ascii_digit() { v = v * 10 + (self.peek() - b'0') as i32; self.i += 1 }
                Ok(Json::Num(if neg { -v } else { v }))
            }
            _ => Err(self.i),
        }
    }
}

fn print(o: &mut String, j: &Json) -> i32 {
    use std::fmt::Write;
    match j {
        Json::Null => { o.push_str("null"); 1 }
        Json::Bool(b) => { o.push_str(if *b { "true" } else { "false" }); 1 }
        Json::Num(n) => { write!(o, "{}", n).unwrap(); 1 }
        Json::Str(s) => { o.push('"'); o.push_str(s); o.push('"'); 1 }
        Json::Arr(a) => {
            o.push('[');
            let mut c = 1;
            for (i, v) in a.iter().enumerate() { if i > 0 { o.push(',') } c += print(o, v) }
            o.push(']');
            c
        }
        Json::Obj(m) => {
            o.push('{');
            let mut c = 1;
            for (i, (k, v)) in m.iter().enumerate() {
                if i > 0 { o.push(',') }
                o.push('"'); o.push_str(k); o.push_str("\":");
                c += print(o, v)
            }
            o.push('}');
            c
        }
    }
}

fn main() {
    let s0 = rs::snap();
    let src = "{ \"a\": [1, true, null], \"b\": {\"c\": \"hi\", \"d\": [10, -20, 30]}, \"e\": false }";
    let mut p = P { s: src.as_bytes(), i: 0 };
    let j = p.value().unwrap();
    let mut o = String::with_capacity(16);
    let c = print(&mut o, &j);
    rs::report(s0);
    println!("{}", o);
    println!("{}", c);
}
