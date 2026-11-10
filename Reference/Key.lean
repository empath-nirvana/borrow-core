import Reference.Driver

/-!
# Reference — the key of a golden

`bcc interp --key`: a sha256 over what decides the source stage's output on a program, so that a
golden (a corpus `<name>.out`, a book block's `-- answer:`) recorded under a key need not be
re-verified while the key is the same (scripts/source-stage.sh). The key covers

* the interpreter digest (`scripts/interp-digest.sh`: the source of the interpreter, the machine
  and this file), given by the caller;
* the fuel (`runFuel`);
* the standard input and the arguments' stream the run is given;
* the run itself (`sourceRunOf`): how its value is read, and the closed term the interpreter runs,
  every library definition it reaches included, written out constructor by constructor
  (`Expr.keyBytes`). Its surface spelling, binder names and comments are not in it.

A program that does not check has the error as its key's run: the stage prints it.
-/

namespace Backend.Key
open BoCa

/-! ### SHA-256 (FIPS 180-4) -/

/-- The round constants. -/
def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def sha256H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message padded to a multiple of 64 bytes: `0x80`, zeros, the bit length (big-endian). -/
def sha256Pad (m : ByteArray) : ByteArray := Id.run do
  let zeros := (119 - m.size % 64) % 64
  let mut b := m.push 0x80
  for _ in [0:zeros] do b := b.push 0
  let bits := (m.size * 8 : Nat)
  for i in [0:8] do b := b.push (bits >>> (8 * (7 - i))).toUInt8
  return b

/-- One 64-byte block at offset `o` of `m` into the state `h`. -/
def sha256Block (m : ByteArray) (o : Nat) (h : Array UInt32) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    let j := o + 4 * t
    w := w.push ((m[j]!.toUInt32 <<< 24) ||| (m[j + 1]!.toUInt32 <<< 16) |||
      (m[j + 2]!.toUInt32 <<< 8) ||| m[j + 3]!.toUInt32)
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + S1 + ch + sha256K[t]! + w[t]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
    h[7]! + hh]

/-- The lowercase hex digits of `x`, eight of them. -/
def hex32 (x : UInt32) : String :=
  String.ofList ((List.range 8).map fun i =>
    let d := ((x >>> (4 * (7 - i).toUInt32)) &&& 0xf).toNat
    if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d))

/-- The sha256 of `m`, in hex. -/
def sha256Hex (m : ByteArray) : String := Id.run do
  let b := sha256Pad m
  let mut h := sha256H0
  for i in [0:b.size / 64] do h := sha256Block b (64 * i) h
  return String.join (h.toList.map hex32)

/-! ### The key -/

/-- `s`'s bytes, then a newline. -/
def line (acc : ByteArray) (s : String) : ByteArray := (acc ++ s.toUTF8).push 10

/-- `bs`, preceded by its length. -/
def sized (acc : ByteArray) (bs : List UInt8) : ByteArray :=
  line acc (toString bs.length) ++ ⟨bs.toArray⟩

/-- The term, constructor by constructor in prefix order: a tag byte for each former (each a
different byte), a de Bruijn index or a location in decimal and a primitive by its derived `Repr`,
each ended by `;` (which no such `Repr` contains): a prefix code, so two terms have the same
bytes only if they are equal. -/
def Expr.keyBytes (acc : ByteArray) : Expr → ByteArray
  | .var i => (acc.push 'v'.toUInt8 ++ (toString i).toUTF8).push ';'.toUInt8
  | .unit => acc.push 'u'.toUInt8
  | .pair a b => Expr.keyBytes (Expr.keyBytes (acc.push 'p'.toUInt8) a) b
  | .inj₁ a => Expr.keyBytes (acc.push '1'.toUInt8) a
  | .inj₂ a => Expr.keyBytes (acc.push '2'.toUInt8) a
  | .lam a => Expr.keyBytes (acc.push 'f'.toUInt8) a
  | .loc ℓ => (acc.push 'l'.toUInt8 ++ (toString ℓ).toUTF8).push ';'.toUInt8
  | .prim p => (acc.push 'o'.toUInt8 ++ (reprStr p).toUTF8).push ';'.toUInt8
  | .seq a b => Expr.keyBytes (Expr.keyBytes (acc.push 's'.toUInt8) a) b
  | .letpair a b => Expr.keyBytes (Expr.keyBytes (acc.push 'd'.toUInt8) a) b
  | .case a b c => Expr.keyBytes (Expr.keyBytes (Expr.keyBytes (acc.push 'c'.toUInt8) a) b) c
  | .app f a => Expr.keyBytes (Expr.keyBytes (acc.push 'a'.toUInt8) f) a

/-- The bytes the key hashes, for the interpreter digest `digest` and the source stage on
`file`, checked (`k`), with `input` and `args` (as `interpSourceStage` takes them). -/
def keyBytes (digest file : String) (k : Except String CheckedProg) (input args : List UInt8) :
    ByteArray :=
  let acc := line .empty "bcc source-stage key 1"
  let acc := line acc s!"digest {digest}"
  let acc := line acc s!"fuel {runFuel}"
  let acc := sized (line acc "input") input
  let acc := sized (line acc "args") args
  match k >>= fun k => sourceRunOf file k input args with
  | .error e => line (line acc "error") e
  | .ok (.plain e) => Expr.keyBytes (line acc "run plain") e
  | .ok (.io e loops exits) => Expr.keyBytes (line acc s!"run io loops {loops} exits {exits}") e

/-- The key: the sha256 of `keyBytes`, in hex. -/
def key (digest file : String) (k : Except String CheckedProg) (input args : List UInt8) :
    String :=
  sha256Hex (keyBytes digest file k input args)

end Backend.Key
