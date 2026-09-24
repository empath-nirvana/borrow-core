import Paper.S1_Syntax.Definitions

/-!
# Support — Lifetimes — Terms

`[about ours]`.  Lifetime terms and contexts: the order and lattice operations on `Life`, lookup and extension of contexts, well-formedness, fresh variables and printing.
-/

noncomputable section

namespace BoCa.Lifetime

/-- Structural depth; used only to size the search budget in §6. -/
def Life.depth : Life → Nat
  | .var _    => 1
  | .top      => 1
  | .join a b => 1 + max a.depth b.depth
  | .meet a b => 1 + max a.depth b.depth

def varName (x : LifeVar) : String :=
  if x < 26 then "'" ++ (Char.ofNat (97 + x)).toString else "'v" ++ toString x

def Life.pp : Life → String
  | .var x    => varName x
  | .top      => "⊤"
  | .join a b => "(" ++ a.pp ++ " ⊔ " ++ b.pp ++ ")"
  | .meet a b => "(" ++ a.pp ++ " ⊓ " ++ b.pp ++ ")"

end BoCa.Lifetime

namespace BoCa.Lifetime.SLife

/-- `⊤ ≜ 0` — the longest lifetime. -/
def top : Nat := 0

/-- `⊔ ≜ min` — the join is the *longer* of the two. -/
def join (α β : Nat) : Nat := min α β

/-- `⊓ ≜ max` — the meet is the *shorter* of the two. -/
def meet (α β : Nat) : Nat := max α β

/-- `α ⊏ β` — "α is outlived by β": β is strictly longer.  The carrier's strict
    `⊏̇ ≜ >` ([CONF] Fig. 11, p. 415:12). -/
def Lt (α β : Nat) : Prop := β < α

/-- `α ⊑ β` — the lattice order of [CONF] Fig. 11's carrier, whose strict part
    is `Lt`. -/
def Le (α β : Nat) : Prop := β ≤ α

end BoCa.Lifetime.SLife

namespace BoCa.Lifetime

/-- Association-list lookup, innermost binding wins. -/
def assocFind {β : Type} (x : LifeVar) : List (LifeVar × β) → Option β
  | []           => none
  | (y, v) :: t  => if y = x then some v else assocFind x t

end BoCa.Lifetime

namespace BoCa.Lifetime.LifeCtx

def find? (Δ : LifeCtx) (x : LifeVar) : Option Life := assocFind x Δ.entries

/-- `Δ, ('a ⊏ @b)`. -/
def extend (Δ : LifeCtx) (x : LifeVar) (u : Life) : LifeCtx := ⟨(x, u) :: Δ.entries⟩

def dom (Δ : LifeCtx) : List LifeVar := Δ.entries.map Prod.fst

def pp (Δ : LifeCtx) : String :=
  "[" ++ String.intercalate ", "
    (Δ.entries.map (fun e => varName e.1 ++ " ⊏ " ++ e.2.pp)) ++ "]"

end BoCa.Lifetime.LifeCtx

namespace BoCa.Lifetime

/-- `Δ ⊨ @a`, decided.  The semantic definition ([TR] p. 3) is
    `Δ ⊨ @a ≜ ∀δ ∈ ⟦Δ⟧. @aδ defined`; this is the decidable check that every
    variable of `@a` is bound by `Δ`.  It implies the semantic judgment
    (`LifeCtx.defines_of_wf`) and differs from it only when `⟦Δ⟧ = ∅`. -/
def Life.wf (Δ : LifeCtx) : Life → Bool
  | .var x    => (Δ.find? x).isSome
  | .top      => true
  | .join a b => a.wf Δ && b.wf Δ
  | .meet a b => a.wf Δ && b.wf Δ

/-- Decidable well-scopedness, as a Bool so that the tests can print it. -/
def okB : List (LifeVar × Life) → Bool
  | []          => true
  | (x, u) :: t => (assocFind x t).isNone && Life.wf ⟨t⟩ u && okB t

/-- One past the largest variable in `dom(Δ)`. -/
def freshOfL : List (LifeVar × Life) → LifeVar
  | []          => 0
  | (x, _) :: t => max (x + 1) (freshOfL t)

end BoCa.Lifetime

end
