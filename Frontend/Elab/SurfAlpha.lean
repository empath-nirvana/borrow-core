import Frontend.Syntax

/-!
# Frontend — Elab — surface types up to the names of their binders  `[spec §3]`

The surface counterpart of `tyEqV` (`Frontend/Check/TyEq.lean`), for the comparisons the
elaborator makes before a type is elaborated: two surface types are one type when they are equal
once every binder is renamed by its depth and spans are dropped. The binders are the lifetime
binders `all 'x < @.` (`VTy.all`, `CTy.all`) and the type binders `mu X.` and `nu X.`; an occurrence
is renamed to its innermost binder's name, and a name no binder binds is kept.

* `VTy.canon`, `CTy.canon`: the renaming.
* `VTy.alphaEq`, `alphaEqs`: equality up to it.
-/

namespace Frontend

/-- The canonical name of the binder at depth `d`: no surface name starts with `%`. -/
def canonName (d : Nat) : String := "%" ++ toString d

/-- A lifetime with its variables renamed by `ρ`. -/
def Life.canon (ρ : List (String × String)) : Life → Life
  | .var s x => .var s ((ρ.lookup x).getD x)
  | .top s => .top s
  | .dom s => .dom s
  | .meet s a b => .meet s (a.canon ρ) (b.canon ρ)
  | .join s a b => .join s (a.canon ρ) (b.canon ρ)

mutual
/-- `A` with each binder renamed by its depth `d`; `ρ` the lifetime binders passed, `τ` the type
binders. -/
def VTy.canon (ρ τ : List (String × String)) (d : Nat) : VTy → VTy
  | .unit s => .unit s
  | .zero s => .zero s
  | .tensor s A B => .tensor s (A.canon ρ τ d) (B.canon ρ τ d)
  | .sum s A B => .sum s (A.canon ρ τ d) (B.canon ρ τ d)
  | .thunk s C => .thunk s (C.canon ρ τ d)
  | .ref s A => .ref s (A.canon ρ τ d)
  | .imm s a A => .imm s (a.canon ρ) (A.canon ρ τ d)
  | .mut s a A => .mut s (a.canon ρ) (A.canon ρ τ d)
  | .box s a A => .box s (a.canon ρ) (A.canon ρ τ d)
  | .bang s A => .bang s (A.canon ρ τ d)
  | .unk s => .unk s
  | .int s w => .int s w
  | .handle s o => .handle s o
  | .mu s X A => .mu s { X with name := canonName d } (A.canon ρ ((X.name, canonName d) :: τ) (d + 1))
  | .name s n => .name s ((τ.lookup n).getD n)
  | .lolli s A B => .lolli s (A.canon ρ τ d) (B.canon ρ τ d)
  | .all s x b A =>
      .all s { x with name := canonName d } (b.canon ρ) (A.canon ((x.name, canonName d) :: ρ) τ (d + 1))
  | .block s σ => .block s (σ.canon ρ τ d)
  | .val s σ => .val s (σ.canon ρ τ d)
  | .fam s m a σ => .fam s m (a.canon ρ) (σ.canon ρ τ d)
  | .view s a A => .view s (a.canon ρ) (A.canon ρ τ d)
  | .array s A => .array s (A.canon ρ τ d)
  | .arrayImm s a A => .arrayImm s (a.canon ρ) (A.canon ρ τ d)
  | .arrayMut s a A => .arrayMut s (a.canon ρ) (A.canon ρ τ d)
  | .sized s D S A => .sized s (D.canon ρ τ d) (S.canon ρ τ d) (A.canon ρ τ d)
  | .app s G A => .app s (G.canon ρ τ d) (A.canon ρ τ d)
  | .lapp s G a => .lapp s (G.canon ρ τ d) (a.canon ρ)
  | .rowed s G r => .rowed s (G.canon ρ τ d) (r.canon ρ τ d)

/-- `C` with each binder renamed by its depth. -/
def CTy.canon (ρ τ : List (String × String)) (d : Nat) : CTy → CTy
  | .ret s A => .ret s (A.canon ρ τ d)
  | .arr s A C => .arr s (A.canon ρ τ d) (C.canon ρ τ d)
  | .amp s C D => .amp s (C.canon ρ τ d) (D.canon ρ τ d)
  | .top s => .top s
  | .all s x b C =>
      .all s { x with name := canonName d } (b.canon ρ) (C.canon ((x.name, canonName d) :: ρ) τ (d + 1))
  | .nu s X C => .nu s { X with name := canonName d } (C.canon ρ ((X.name, canonName d) :: τ) (d + 1))
  | .name s n => .name s ((τ.lookup n).getD n)
  | .delay s A => .delay s (A.canon ρ τ d)
  | .stream s A => .stream s (A.canon ρ τ d)
  | .iter s A R R' => .iter s (A.canon ρ τ d) (R.canon ρ τ d) (R'.canon ρ τ d)
  | .loop s A B => .loop s (A.canon ρ τ d) (B.canon ρ τ d)
  | .pull s A B R => .pull s (A.canon ρ τ d) (B.canon ρ τ d) (R.canon ρ τ d)
  | .eff s r A => .eff s (r.canon ρ τ d) (A.canon ρ τ d)

/-- A row with each binder renamed by its depth. -/
def Row.canon (ρ τ : List (String × String)) (d : Nat) : Row → Row
  | .nil => .nil
  | .cons n i q A B f r => .cons n i q (A.canon ρ τ d) (B.canon ρ τ d) (f.canon ρ τ d) (r.canon ρ τ d)
  | .top => .top

/-- A shape with each binder renamed by its depth. -/
def Shape.canon (ρ τ : List (String × String)) (d : Nat) : Shape → Shape
  | .leaf s A => .leaf s (A.canon ρ τ d)
  | .node s σ σ' => .node s (σ.canon ρ τ d) (σ'.canon ρ τ d)
  | .name s n => .name s n
end

/-- Two surface types are one up to the names of their binders and their spans. -/
def VTy.alphaEq (A B : VTy) : Bool := (A.canon [] [] 0).strip == (B.canon [] [] 0).strip

/-- Two lists of surface types, position by position, each up to the names of their binders. -/
def alphaEqs : List VTy → List VTy → Bool
  | [], [] => true
  | A :: As, B :: Bs => A.alphaEq B && alphaEqs As Bs
  | _, _ => false

end Frontend
