import Backend.Flat.Syntax

/-!
# Backend — the flat IR's runtime functions

Deep copy, deep drop and the printer, as flat-IR functions over the representation of
`Backend/Flat/Syntax.lean`. Cells are shared by a copy and left alone by a drop: a location is
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

def runtimeFns : List Fn :=
  [copyFn, dropFn, copyEnvFn, dropEnvFn, printFn, printAtomFn, printDecFn]

end Backend.Flat
