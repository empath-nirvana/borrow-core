import Backend.Flat.Syntax

/-!
# Backend — the flat IR's runtime functions

Deep copy, deep drop, the printer and the array operations, as flat-IR functions over the
representation of `Backend/Flat/Syntax.lean`. Cells are shared by a copy and left alone by a drop: a location is
copied as a word, and cells are freed only by `free`. The printer writes the text of
`Backend.PV.render`.

They occupy the first function indices of every program, in the order of `runtimeFns`.
-/

namespace Backend.Flat

def fCopy : Nat := 0
def fDrop : Nat := 1
def fCopyEnv : Nat := 2
def fDropEnv : Nat := 3
def fPrint : Nat := 4
def fPrintAtom : Nat := 5
def fPrintDec : Nat := 6
def fArrTab : Nat := 7
def fArrInit : Nat := 8
def fArrTabLoop : Nat := 9
def fArrIdx : Nat := 10
def fArrDrop : Nat := 11
def fArrDropLoop : Nat := 12
def fReadByte : Nat := 13
def fWriteByte : Nat := 14
def fDrive : Nat := 15

/-- `copy w`: locals `w`, `h`, `t`, `n`. -/
def copyFn : Fn where
  name := "copy"
  params := 1
  locals := 3
  body :=
    let w := Exp.loc 0; let h := Exp.loc 1; let t := Exp.loc 2; let n := Exp.loc 3
    [ .ite (isImm w) [.ret w] [],
      .set 1 (.load w 0),
      .switch (kindOf h)
        [ [.trap],
          -- pair
          [ .set 2 (.alloc (.c64 3)), .store t 0 h,
            .store t 1 (.call fCopy [.load w 1]), .store t 2 (.call fCopy [.load w 2]), .ret t ],
          -- inj₁, inj₂
          [ .set 2 (.alloc (.c64 2)), .store t 0 h, .store t 1 (.call fCopy [.load w 1]), .ret t ],
          [ .set 2 (.alloc (.c64 2)), .store t 0 h, .store t 1 (.call fCopy [.load w 1]), .ret t ],
          -- closure: the code index, then each captured value
          [ .set 3 (shr64 h (.c64 8)), .set 2 (.alloc (add64 n (.c64 2))), .store t 0 h,
            .store t 1 (.load w 1), .eval (.call fCopyEnv [w, t, .c64 0, n]), .ret t ],
          -- i64
          [ .set 2 (.alloc (.c64 2)), .store t 0 h, .store t 1 (.load w 1), .ret t ],
          -- cell: shared
          [ .ret w ],
          [ .trap ] ],
      .trap ]

/-- `copyEnv src dst i n`: copy captured values `i … n-1` of closure `src` into `dst`. -/
def copyEnvFn : Fn where
  name := "copy_env"
  params := 4
  locals := 0
  body :=
    let src := Exp.loc 0; let dst := Exp.loc 1; let i := Exp.loc 2; let n := Exp.loc 3
    [ .ite (ltu64 i n)
        [ .store (envAddr dst i) 2 (.call fCopy [.load (envAddr src i) 2]),
          .tailCall fCopyEnv [src, dst, add64 i (.c64 1), n] ] [],
      .ret (.c64 0) ]

/-- `drop w`: locals `w`, `h`. -/
def dropFn : Fn where
  name := "drop"
  params := 1
  locals := 1
  body :=
    let w := Exp.loc 0; let h := Exp.loc 1
    [ .ite (isImm w) [.ret (.c64 0)] [],
      .set 1 (.load w 0),
      .switch (kindOf h)
        [ [.trap],
          [ .eval (.call fDrop [.load w 1]), .eval (.call fDrop [.load w 2]), .free w, .ret (.c64 0) ],
          [ .eval (.call fDrop [.load w 1]), .free w, .ret (.c64 0) ],
          [ .eval (.call fDrop [.load w 1]), .free w, .ret (.c64 0) ],
          [ .eval (.call fDropEnv [w, .c64 0, shr64 h (.c64 8)]), .free w, .ret (.c64 0) ],
          [ .free w, .ret (.c64 0) ],
          [ .ret (.c64 0) ],
          [ .trap ] ],
      .trap ]

/-- `dropEnv w i n`: drop captured values `i … n-1` of closure `w`. -/
def dropEnvFn : Fn where
  name := "drop_env"
  params := 3
  locals := 0
  body :=
    let w := Exp.loc 0; let i := Exp.loc 1; let n := Exp.loc 2
    [ .ite (ltu64 i n)
        [ .eval (.call fDrop [.load (envAddr w i) 2]),
          .tailCall fDropEnv [w, add64 i (.c64 1), n] ] [],
      .ret (.c64 0) ]

/-- `print w`: locals `w`, `h`. -/
def printFn : Fn where
  name := "print"
  params := 1
  locals := 1
  body :=
    let w := Exp.loc 0; let h := Exp.loc 1
    [ .ite (isImm w)
        [ .ite (eq64 w (.c64 unitW)) (outStr "()" ++ [.ret (.c64 0)])
            (outStr "i32[" ++ [.eval (.call fPrintDec [shr64 w (.c64 32)])] ++ outStr "]" ++
              [.ret (.c64 0)]) ] [],
      .set 1 (.load w 0),
      .switch (kindOf h)
        [ [.trap],
          outStr "(" ++ [.eval (.call fPrint [.load w 1])] ++ outStr ", " ++
            [.eval (.call fPrint [.load w 2])] ++ outStr ")" ++ [.ret (.c64 0)],
          outStr "inl " ++ [.eval (.call fPrintAtom [.load w 1]), .ret (.c64 0)],
          outStr "inr " ++ [.eval (.call fPrintAtom [.load w 1]), .ret (.c64 0)],
          outStr "<fun>" ++ [.ret (.c64 0)],
          outStr "i64[" ++ [.eval (.call fPrintDec [.load w 1])] ++ outStr "]" ++ [.ret (.c64 0)],
          outStr "<loc>" ++ [.ret (.c64 0)],
          [.trap] ],
      .trap ]

/-- `printAtom w`: an injection in parentheses, anything else as `print`. -/
def printAtomFn : Fn where
  name := "print_atom"
  params := 1
  locals := 1
  body :=
    let w := Exp.loc 0; let h := Exp.loc 1
    [ .ite (isImm w) [.tailCall fPrint [w]] [],
      .set 1 (.load w 0),
      .ite (or32 (eq64 h (.c64 hInj₁)) (eq64 h (.c64 hInj₂)))
        (outStr "(" ++ [.eval (.call fPrint [w])] ++ outStr ")" ++ [.ret (.c64 0)]) [],
      .tailCall fPrint [w] ]

/-- `printDec n`: `n` in unsigned decimal. -/
def printDecFn : Fn where
  name := "print_dec"
  params := 1
  locals := 0
  body :=
    let n := Exp.loc 0
    [ .ite (.op (.rel .w64 .ge_u) [n, .c64 10])
        [.eval (.call fPrintDec [.op (.div .w64 .div_u) [n, .c64 10]])] [],
      .out (add64 (.c64 48) (.op (.div .w64 .rem_u) [n, .c64 10])),
      .ret (.c64 0) ]

/-! ### Arrays  `[spec §9]`

An array of `n` elements is one range of `max n 1` slots of two words each: a cell header and
the contents. Slot `i` is at `base + 16·i`, and is an ordinary cell object, so its address is
the element's location and `load`, `store`, a copy and a drop treat it as any cell. The array
value is the pair `(base, i32[n])`. An empty array keeps one slot, so the base is an object. -/

/-- The address of slot `i`. -/
def slotAddr (b i : Exp) : Exp := add64 b (shl64 i (.c64 4))

/-- `i32[i]` from a 64-bit `i` below `2³²`. -/
def boxIdx (i : Exp) : Exp := or64 (shl64 i (.c64 32)) (.c64 3)

/-- `array_tab p`, `p = (i32[c], f)`: `len(c)` slots filled by `f i` in order. Locals `p`,
`n`, `f`, `b`, `s` (the slot count), `t`. -/
def arrTabFn : Fn where
  name := "array_tab"
  params := 1
  locals := 5
  body :=
    let p := Exp.loc 0; let n := Exp.loc 1; let f := Exp.loc 2; let b := Exp.loc 3
    let s := Exp.loc 4
    [ .set 1 (shr64 (.load p 1) (.c64 32)), .set 2 (.load p 2), .free p,
      .ite (ltu64 n (.c64 0x80000000)) [] [.set 1 (.c64 0)],
      .set 4 n, .ite (eq64 n (.c64 0)) [.set 4 (.c64 1)] [],
      .set 3 (.alloc (shl64 s (.c64 1))),
      .eval (.call fArrInit [b, .c64 0, s]),
      .eval (.call fArrTabLoop [b, f, .c64 0, n]),
      .eval (.call fDrop [f]) ] ++
    mkObj 5 hPair [b, boxIdx n] ++ [.ret (.loc 5)]

/-- `arrInit b i s`: slots `i … s-1` become cells holding `()`. -/
def arrInitFn : Fn where
  name := "array_init"
  params := 3
  locals := 0
  body :=
    let b := Exp.loc 0; let i := Exp.loc 1; let s := Exp.loc 2
    [ .ite (ltu64 i s)
        [ .store (slotAddr b i) 0 (.c64 hCell), .store (slotAddr b i) 1 (.c64 unitW),
          .tailCall fArrInit [b, add64 i (.c64 1), s] ] [],
      .ret (.c64 0) ]

/-- `arrTabLoop b f i n`: slot `i` gets a copy of `f` applied to `i32[i]`, for `i < n`. -/
def arrTabLoopFn : Fn where
  name := "array_tab_loop"
  params := 4
  locals := 2
  body :=
    let b := Exp.loc 0; let f := Exp.loc 1; let i := Exp.loc 2; let n := Exp.loc 3
    let fc := Exp.loc 4
    [ .ite (ltu64 i n)
        [ .set 4 (.call fCopy [f]),
          .set 5 (.callInd (.load fc 1) [fc, boxIdx i]),
          .store (slotAddr b i) 1 (.loc 5),
          .tailCall fArrTabLoop [b, f, add64 i (.c64 1), n] ] [],
      .ret (.c64 0) ]

/-- `array_idx p`, `p = ((b, i32[n]), i32[i])`: `inl` of slot `i` when `i < n` unsigned, else
`inr ()`. Locals `p`, `q`, `w`, `b`, `n`, `t`. -/
def arrIdxFn : Fn where
  name := "array_idx"
  params := 1
  locals := 5
  body :=
    let p := Exp.loc 0; let q := Exp.loc 1; let w := Exp.loc 2; let b := Exp.loc 3
    let n := Exp.loc 4
    [ .set 1 (.load p 1), .set 2 (.load p 2), .free p,
      .set 3 (.load q 1), .set 4 (shr64 (.load q 2) (.c64 32)), .free q,
      .ite (ltu64 (shr64 w (.c64 32)) n)
        (mkObj 5 hInj₁ [slotAddr b (shr64 w (.c64 32))] ++ [.ret (.loc 5)])
        (mkObj 5 hInj₂ [.c64 unitW] ++ [.ret (.loc 5)]) ]

/-- `array_drop p`, `p = (f, (b, i32[n]))`: each element to a copy of `f`, in order, then the
range freed. Locals `p`, `f`, `q`, `b`, `n`. -/
def arrDropFn : Fn where
  name := "array_drop"
  params := 1
  locals := 4
  body :=
    let p := Exp.loc 0; let f := Exp.loc 1; let q := Exp.loc 2; let b := Exp.loc 3
    let n := Exp.loc 4
    [ .set 1 (.load p 1), .set 2 (.load p 2), .free p,
      .set 3 (.load q 1), .set 4 (shr64 (.load q 2) (.c64 32)), .free q,
      .eval (.call fArrDropLoop [b, f, .c64 0, n]),
      .eval (.call fDrop [f]), .free b, .ret (.c64 unitW) ]

/-- `arrDropLoop b f i n`: slot `i`'s contents, moved out, to a copy of `f`, for `i < n`. -/
def arrDropLoopFn : Fn where
  name := "array_drop_loop"
  params := 4
  locals := 1
  body :=
    let b := Exp.loc 0; let f := Exp.loc 1; let i := Exp.loc 2; let n := Exp.loc 3
    let fc := Exp.loc 4
    [ .ite (ltu64 i n)
        [ .set 4 (.call fCopy [f]),
          .eval (.call fDrop [.callInd (.load fc 1) [fc, .load (slotAddr b i) 1]]),
          .tailCall fArrDropLoop [b, f, add64 i (.c64 1), n] ] [],
      .ret (.c64 0) ]

/-! ### Standard I/O  `[spec §11]`

A capability is a cell whose content is `i32[fd]`, the stream's file descriptor. -/

/-- `read_byte m`: `(m, inl i32[b])` with the next byte of the stream in the cell `m`, or
`(m, inr ())` at its end. Locals `m`, `b`, `r`, `t`. -/
def readByteFn : Fn where
  name := "read_byte"
  params := 1
  locals := 3
  body :=
    let m := Exp.loc 0; let b := Exp.loc 1
    [ .set 1 (.getc (shr64 (.load m 1) (.c64 32))),
      .ite (eq64 b (.c64 0xFFFFFFFFFFFFFFFF))
        (mkObj 2 hInj₂ [.c64 unitW]) (mkObj 2 hInj₁ [box32 (wrap b)]) ] ++
    mkObj 3 hPair [m, .loc 2] ++ [.ret (.loc 3)]

/-- `write_byte p`, `p = (m, i32[b])`: the low byte of `b` to the stream in the cell `m`; the
result is `m`. Locals `p`, `m`, `w`. -/
def writeByteFn : Fn where
  name := "write_byte"
  params := 1
  locals := 2
  body :=
    let p := Exp.loc 0; let m := Exp.loc 1; let w := Exp.loc 2
    [ .set 1 (.load p 1), .set 2 (.load p 2), .free p,
      .putc (shr64 (.load m 1) (.c64 32)) (shr64 w (.c64 32)), .ret m ]

/-- `drive d`: observe the loop `d` until it finishes, calling it on `inl ()`; it answers
`inl r` to finish with `r` or `inr d'` to go on with `d'` (SPEC §11). Locals `d`, `t`, `r`. -/
def driveFn : Fn where
  name := "drive"
  params := 1
  locals := 2
  body :=
    let d := Exp.loc 0; let r := Exp.loc 2
    mkObj 1 hInj₁ [.c64 unitW] ++
    [ .set 2 (.callInd (.load d 1) [d, .loc 1]),
      .ite (eq64 (.load r 0) (.c64 hInj₁))
        [.set 1 (.load r 1), .free r, .ret (.loc 1)]
        [.set 0 (.load r 1), .free r, .tailCall fDrive [d]] ]

def runtimeFns : List Fn :=
  [copyFn, dropFn, copyEnvFn, dropEnvFn, printFn, printAtomFn, printDecFn,
   arrTabFn, arrInitFn, arrTabLoopFn, arrIdxFn, arrDropFn, arrDropLoopFn,
   readByteFn, writeByteFn, driveFn]

end Backend.Flat
