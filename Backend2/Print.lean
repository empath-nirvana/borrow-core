import Backend2.Syntax

/-!
# Backend2 — the LIR, printed

`bcc lir <file>` prints the program's LIR: each function with its parameters' types, each code
with its kind and functions, then `main`.
-/

namespace Backend2
open BoCa

def ppOp : Op → String
  | .host op => s!"host[{reprStr op}]"
  | .divLit op => s!"divLit[{reprStr op}]"
  | .io k => s!"io[{reprStr k}]"
  | .idx c => if c then "idx" else "idx!"
  | .split c => if c then "split" else "split!"
  | .litByte => "litByte"
  | .litView c => s!"litView[{c}]"
  | .staticCell k => s!"static[{k}]"
  | .alloc => "alloc" | .allocLent => "allocLent" | .free => "free" | .release => "release" | .swap => "swap" | .lend => "lend" | .relend => "relend"
  | .load => "load" | .take => "take" | .put => "put" | .newArr => "newArr"
  | .slotPut => "slotPut" | .slotTake => "slotTake" | .freeArr => "freeArr" | .size => "size"
  | .len => "len" | .emptyFam => "emptyFam" | .replace => "replace" | .swapSlots => "swapSlots"
  | .tab fi => s!"tab[f{fi}]" | .tabLit fi => s!"tabLit[f{fi}]"
  | .roll => "roll" | .unroll => "unroll" | .clampLen => "clampLen" | .cntLt => "cntLt" | .cntSucc => "cntSucc" | .cntPred => "cntPred"

def v (x : Var) : String := s!"x{x}"

def vs (xs : List Var) : String := ", ".intercalate (xs.map v)

def ind (d : Nat) : String := String.ofList (List.replicate (2 * d) ' ')

/-- A term, one binding a line. -/
def Tm.pp (ty : Var → String) : Nat → Tm → List String
  | d, .var x => [ind d ++ v x]
  | d, .unit => [ind d ++ "()"]
  | d, .lit c => [ind d ++ reprStr c]
  | d, .pair a b => [ind d ++ s!"({v a}, {v b})"]
  | d, .inj r a => [ind d ++ s!"{if r then "inr" else "inl"} {v a}"]
  | d, .clos c env => [ind d ++ s!"clos c{c} [{vs env}]"]
  | d, .app f a => [ind d ++ s!"{v f} {v a}"]
  | d, .app0 f => [ind d ++ s!"{v f} ()"]
  | d, .sel f j => [ind d ++ s!"{v f}.{j}"]
  | d, .call fn as => [ind d ++ s!"f{fn}({vs as})"]
  | d, .prim op as => [ind d ++ s!"{ppOp op}({vs as})"]
  | d, .letv x e b => (ind d ++ s!"let {v x} : {ty x} =") :: Tm.pp ty (d + 1) e ++ Tm.pp ty d b
  | d, .letpair x y p b => (ind d ++ s!"let ({v x}, {v y}) = {v p}") :: Tm.pp ty d b
  | d, .case s x b₁ y b₂ =>
    [ind d ++ s!"case {v s}", ind d ++ s!"| inl {v x} ->"] ++ Tm.pp ty (d + 1) b₁ ++
      [ind d ++ s!"| inr {v y} ->"] ++ Tm.pp ty (d + 1) b₂
  | d, .absurd s => [ind d ++ s!"absurd {v s}"]
  | d, .copy x x' b => (ind d ++ s!"copy {v x} -> {v x'}") :: Tm.pp ty d b
  | d, .drop x b => (ind d ++ s!"drop {v x}") :: Tm.pp ty d b

def Prog.pp (p : Prog) : List String :=
  let ty := fun x => (p.ty[x]?.map LTy.pp).getD "?"
  let fns := p.fns.toList.zipIdx.flatMap fun (f, i) =>
    s!"f{i} {f.name}({", ".intercalate (f.params.map fun x => s!"{v x} : {ty x}")}) : {f.ret} =" ::
      Tm.pp ty 1 f.body
  let codes := p.codes.toList.zipIdx.map fun (c, i) =>
    s!"c{i} {reprStr c.kind} [{", ".intercalate (c.fns.map (s!"f{·}"))}] : {c.ty}"
  codes ++ fns ++ [s!"main : {p.mainTy} ="] ++ Tm.pp ty 1 p.main

end Backend2
