import ProbeD1.Piece

/-!
# ProbeD1 — W's relation, the future-world quantifier placed by `Placement` (DESIGN §2.4)

One `mutual` block, structural on the type, the stack an index (as `vRLk`), the placement a fixed
parameter. The three placements are the candidates for W's one relation that statement 0 compares;
W is the one that survives, and the cuts order chooses if more than one does (`Placement.rank`).

| placement | `U` | `⊸` | `∀` | the stop's share | the callback's own lend |
|---|---|---|---|---|---|
| `cbpv` (OQ-8 option 2) | futures | resources only | resources only | futures | at `U`, at every future, one level into the type |
| `binder0` (OQ-8 option 3, `vRLk`) | the stack itself (`RelendableS`) | resources only | resources only | the stack itself (`OpenS`) | at `∀`, at the stack itself |
| `binder` (OQ-8 option 3, §17.6) | futures | futures | futures | futures | at `∀`, at every future |

**One quantifier.** Every clause reaches a stack other than its own only through `FutQ` (W's
order `Fut`, or the stack itself, by the placement's flag) followed, at the clause that makes the
callback's own lend, by `OwnPush` at the type it reads. The own lend is the outermost `∀`'s
instance read as the lend the instance names; it is named by the type, so it is relative to it,
as `vRLk`'s extension is (`e'.x = x ∨ ¬ CFree e'.x C`).

Every clause carries the table guard (`guardW`) where it receives a resource from outside, as
`vRLa`/`vRLk` do. Every former not listed is read as `vRLs` reads it: the components at the
relation, the leaves at the kernel's `vC` at the reading substitution `extS δ σ αs`.

`binder0` is `vRLk` (`borrow-callbacks:experiments/GhostEnd/GhostEnd/Extend.lean`) with two changes
at `∀`: the extension is the callback's own lend only (one entry, named by the binder, at the
instance's lifetime), and that entry meets `OwnOK` (below the callback's resource, its variable and
place new to the stack). `vRLk`'s `∀` clause reads its body at the entry's lifetime for every
instance `α`, so its `allI` row would owe the body at lifetimes that do not meet the bound.

Definitions only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS stratS ReLend RelendableS bodyS OpenS rowTab TabAtS)

/-- Where the future-world quantifier sits (OQ-8). -/
inductive Placement
  /-- At `U`, the share and `KapRel` (OQ-8 option 2, the audit's). -/
  | cbpv
  /-- At `∀` only, as `vRLk` (#287; OQ-8 option 3 as built). -/
  | binder0
  /-- At `U`, the share, `⊸` and `∀` (OQ-8 option 3, §17.6). -/
  | binder
  deriving DecidableEq, Repr

namespace Placement

/-- The `U` clause quantifies over the stack's futures. -/
def uFut : Placement → Bool
  | .binder0 => false
  | _ => true

/-- The `U` clause makes the callback's own lend. -/
def uOwn : Placement → Bool
  | .cbpv => true
  | _ => false

/-- The `∀` clause makes the callback's own lend. -/
def allOwn : Placement → Bool
  | .cbpv => false
  | _ => true

/-- `⊸` and `∀` quantify over the stack's futures. -/
def bindFut : Placement → Bool
  | .binder => true
  | _ => false

/-- The stop's share quantifies over the kept stack's futures. -/
def shareFut : Placement → Bool
  | .binder0 => false
  | _ => true

end Placement

/-- **The `U` clause over futures**: the resource splits into the views it dropped and a part
strictly above the outermost lend that, at every `Ext`-future of the list, every re-lend, and every
future of the stack the clause quantifies over (`FutQ`: all of them when `fut`, the stack itself
otherwise; the inserted entries not read by the type), handed the views, is in `P` at that stack;
and, when `own`, also at the stack the callback's own lend gives there (`OwnPush`: one entry at
depth `0` named by the type's outermost `∀`, at a lifetime meeting its bound). -/
def RelendU (fut own : Bool) (δ : LSub) (σ : LStack) (C : CTy)
    (P : LStack → List Life → List SRec → WProp) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ =>
    ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ [] σ ds αs ls ρn ∧ stratS αs ρz ∧
      ∀ ls', Ext ls ls' ρz → ∀ αs', ReLend αs' αs →
        ∀ σ' αs'', FutQ fut δ ρz (σ, αs') (σ', αs'') → FutAvoids C σ σ' →
          (vwS δ [] σ ds αs' ls' ─⋆ P σ' αs'' ls') ρz ∧
          (own = true → ∀ (e : LEnt) (a : Life), OwnPush δ C ρz (σ', αs'') e a →
            (vwS δ [] σ ds αs' ls' ─⋆ P (e :: σ') (a :: αs'') ls') ρz)

mutual
/-- **W's value relation** at the placement `p`, the stack `σ`, the lends at `αs`. -/
def vRL (p : Placement) : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardW σ αs
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRL p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendableS δ [] σ (fun αs' ls' => cRL p σ δ C αs' ls' (forceE C (.val f))) αs ls)
  | σ, δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRL p σ δ A αs ls v₁ ⋆ vRL p σ δ B αs ls v₂
  | σ, δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRL p σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRL p σ δ B αs ls v₂)
  | σ, δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRL p σ δ A αs ls v ρ
  | σ, δ, .box a A, αs, ls, v => atLife (extS δ σ αs) a fun α => box α (vRL p σ δ A αs ls v)
  | σ, δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRL p σ δ A αs ls v'
  | σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ _ A => A
/-- **W's computation relation.** At `F_Σ R` GhostEnd's piece, its share over futures when
`p.shareFut`. At `⊸` and `∀` the clause holds at every `Ext`-future of the list and every future of
the stack when `p.bindFut`, at the index itself otherwise; at `∀` it holds also at the own lend
there when `p.allOwn`. -/
def cRL (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  | σ, δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRL p σ δ B αs ls'' v
  | σ, δ, .eff n i q A B C, αs, ls, e =>
      if p.shareFut then
        bodySF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRet p σ' δ C αs' ls v)
          (OpenSF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRet p σ' δ C αs' ls v))
          σ αs ls e
      else
        bodyS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRet p σ δ C αs' ls v)
          (OpenS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRet p σ δ C αs' ls v)) αs ls e
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQ p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRL p σ' δ A αs' ls' v ─⋆ guardW σ' αs' (cRL p σ' δ C αs' ls' (.app e (.val v)))) ρ
  | σ, δ, .amp C D, αs, ls, e => fun ρ =>
      cRL p σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRL p σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, _, .top, _, _, _ => fun _ => True
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQ p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α⌝ ─⋆
          guardW σ' αs' (cRL p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPush δ (.all x c C) ρ (σ', αs') en α →
          guardW (en :: σ') (α :: αs')
            (cRL p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ _ C => C
/-- The answer relation of `F_Σ R`: `vRL R`. -/
def effRet (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Val → WProp
  | σ, δ, .ret A, αs => fun ls v => vRL p σ δ A αs ls v
  | σ, δ, .eff _ _ _ _ _ C, αs => effRet p σ δ C αs
  | _, _, _, _ => fun _ _ _ => False
termination_by structural _ _ C => C
end

/-- `⊛_{x ∈ dom(Γ)} vRL(Γ(x))`. -/
def gSepRL (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRL p σ δ s.ty αs ls v ⋆ gSepRL p σ δ αs ls Γ γ else gSepRL p σ δ αs ls Γ γ

/-- `𝒢⟦Γ⟧` at W. -/
def gRL (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy)
    (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRL p σ δ αs ls Γ γ

end ProbeD1

end
