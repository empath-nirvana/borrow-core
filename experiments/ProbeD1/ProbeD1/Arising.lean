import ProbeD1.Rules

/-!
# ProbeD1 — the arising check (DESIGN §11)

A refutation of a statement of this probe is an obstruction only at a configuration that arises
and with values that arise. Arising tests are directional: an over-approximation of what arises is
sound for proving and unsound for refuting. So the check a refutation must pass is reachability,
not a pointwise property of one configuration.

* **`Arises c`**: the configuration is reached from the nil index, whose arising set is `TW`'s
  (Core's settled one), by the transitions W's semantics makes: a run of a term the probe's rules
  derive (`ProbeRules`), its captured values arising, ending as `wpG`'s run ends (`RunEnd`: the
  machine's run, `↭` on the local part, a tagged `TW` world at the end, the stack fixed); a part
  of the local resource taken, the rest joining the frame; a lend opened by a lend row (`LendMut`:
  `TW.mutFold`'s step, 6.65's start; `LendImm`: `TW.immFrame`'s step, 6.64's start), its entry
  pushed below the callback's resource (6.112's `И`); a handler installed (`hideS`). Each
  transition is a step of W's semantics, so `Arises` under-approximates what arises.
* **`ArisesV c v`**: the value is the answer of such a run, the run exhibited with its derivation,
  or the place a lend row hands its callback. `ArisesVal v`: it arises at some configuration, as a
  run's captured values must.
* **`ArisesAt`** is the pointwise consequence: the world `TW`'s, the stack consistent with it, the
  local part consistent with the table. Statement 1 proves `Arises ⊆ ArisesAt` (`ArisesSound`). It
  is a necessary condition, used to exclude a witness, never to admit one.

Definitions only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Alloc ARun)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE TabAtS)

/-- **The pointwise consequence of arising at W's index**: the world `fρ = ρf ● ρ` a tagged `TW`
world at the records, the stack in shape, every 6.64 entry among `TW`'s records, every 6.65
entry's place a `mut` cell of the world, and the local part `ρ` consistent with the stack's table
(the stack's run invariant, statement 1). -/
def ArisesAt (σ : LStack) (αs : List Life) (ls : List SRec) (ps : List FrameRec)
    (ρf ρ fρ : WRes) : Prop :=
  TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    StackOK σ αs ∧ (∀ e ∈ σ, ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = e.l) ∧
    (∀ e ∈ σ, e.k = .mut → ∃ ψ : CellU BoCa.Loc Val, fρ.get e.l = some ψ ∧ ψ.kind = Kind.mut) ∧
    TabAtS σ αs ρ

/-- **A configuration of W**: the world, its frame part and its local part, the open 6.64 frames,
the records, the stack and its lifetimes. -/
structure Cfg where
  fρ : WRes
  ρf : WRes
  ρ : WRes
  ps : List FrameRec
  ls : List SRec
  σ : LStack
  αs : List Life

/-- **A run at the stack**, from `c`, of the term `e`, ending at `c'` with the term `t`: `wpG`'s run
(`Core/EffDefs.lean`), the stack and its lifetimes fixed, the garbage joining the frame. -/
def RunEnd (c : Cfg) (e : Expr) (c' : Cfg) (t : Expr) : Prop :=
  c'.σ = c.σ ∧ c'.αs = c.αs ∧
  ∃ (A : Alloc) (k k' : Nat) (μ μ' : Heap) (ρp fρ' π : WRes),
    ResU.Hash c'.ρ c.ρf ∧ ResU.CompS c.ρf c'.ρ fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower c.fρ μ ∧
    ResU.CompS fρ' ρp c'.fρ ∧ ResU.Lower c'.fρ μ' ∧ ARun (ℍ := ℍ) A k μ e k' μ' t ∧
    ResU.CompS c'.ρ ρp π ∧ ResU.UpdV c.ρ π ∧ NoOwn ρp ∧
    TW c'.fρ c'.ps (rsOf c'.ls) ∧ Tagged c'.fρ c'.ps c'.ls ∧
    (∀ p, p ∈ c'.ps ↔ p ∈ c.ps) ∧ (∀ x, x ∈ c'.ls ↔ x ∈ c.ls) ∧
    ResU.CompS c.ρf ρp c'.ρf

/-- **A 6.65 lend opened** (`withbor` (2)'s start): the local part holds the owner `ℓ ↦ v` with
its payload `ρp` and the callback's resource `ρc`; the world folds the owner into
`ℓ ↦ mut(α, v, ρp)` (`TW.mutFold`'s premises), the entry's view; the entry is pushed at `α`, below
the innermost lend and below `ρc` (6.112's `И`), its variable and place new to the stack; the local
part becomes the view beside `ρc`. -/
def LendMut (c c' : Cfg) (e : LEnt) : Prop :=
  e.k = .mut ∧ c'.σ = e :: c.σ ∧ c'.ps = c.ps ∧ c'.ls = c.ls ∧ c'.ρf = c.ρf ∧
    e.x ∉ c.σ.map LEnt.x ∧ e.l ∉ c.σ.map LEnt.l ∧
    ∃ (α : Life) (v : Val) (ρp X ρc Z : WRes) (hstr : ρp.InStratum α)
      (P : Val → SPropS BoCa.Loc Val α) (hw : P v ⟨ρp, hstr⟩),
      c'.αs = α :: c.αs ∧ List.IsChain (· < ·) (α :: c.αs) ∧ ρc.InStratum α ∧
      ResU.CompS (ResU.single e.l (CellU.ownOf v)) ρp X ∧ ResU.CompS X ρc c.ρ ∧
      ResU.CompS X Z c.fρ ∧
      ResU.CompS (ResU.single e.l (CellU.mutOf α v ρp hstr P hw)) Z c'.fρ ∧ ResU.Valid c'.fρ ∧
      ResU.CompS (ResU.single e.l (CellU.mutOf α v ρp hstr P hw)) ρc c'.ρ ∧
      ResU.Hash c'.ρf c'.ρ ∧ ResU.CompS c'.ρf c'.ρ c'.fρ ∧ Tagged c'.fρ c'.ps c'.ls ∧
      ∃ δ : LSub, vwE δ e true α c.ls (ResU.single e.l (CellU.mutOf α v ρp hstr P hw))

/-- **A 6.64 lend opened** (`withbor` (1)'s start): the world turns the owner `ℓ ↦ v` with its
payload `R` into `ℓ ↦ imm({α}, v, R)` and records the frame and its lineage (`TW.immFrame`'s
premises); the entry, of kind `imm v`, is pushed at `α`, below the innermost lend and below the
callback's resource `ρc`, its variable and place new to the stack; the local part becomes the cell
beside `ρc`. -/
def LendImm (c c' : Cfg) (e : LEnt) : Prop :=
  c'.σ = e :: c.σ ∧ c'.ρf = c.ρf ∧ e.x ∉ c.σ.map LEnt.x ∧ e.l ∉ c.σ.map LEnt.l ∧
    ∃ (α : Life) (v : Val) (R X ρc Z : WRes) (δ : LSub)
      (h : R.InStratum (LSet.singleton α).join) (ds : List FrameRec),
      e.k = .imm v ∧ c'.αs = α :: c.αs ∧ List.IsChain (· < ·) (α :: c.αs) ∧ ρc.InStratum α ∧
      AdmWf e.T δ ∧ ResU.CompS (ResU.single e.l (CellU.ownOf v)) R X ∧ ResU.CompS X ρc c.ρ ∧
      ResU.CompS X Z c.fρ ∧ vShape e.T δ v R ∧
      ResU.CompS (ResU.single e.l (CellU.immOf (LSet.singleton α) v R h)) Z c'.fρ ∧
      ResU.Valid c'.fρ ∧ (∀ d, d ∈ ds ↔ Desc ⟨e.l, v, R, e.T, δ⟩ d) ∧
      c'.ps = ⟨e.l, v, R, e.T, δ⟩ :: c.ps ∧
      rsOf c'.ls = ⟨e.l, v, R, e.T, δ⟩ :: (ds ++ rsOf c.ls) ∧
      ResU.CompS (ResU.single e.l (CellU.immOf (LSet.singleton α) v R h)) ρc c'.ρ ∧
      ResU.Hash c'.ρf c'.ρ ∧ ResU.CompS c'.ρf c'.ρ c'.fρ ∧ Tagged c'.fρ c'.ps c'.ls

mutual
/-- **The configurations that arise at W** (DESIGN §11 item 2): reachability from the nil index by
the transitions of W's semantics. -/
inductive Arises : Cfg → Prop where
  /-- Core's arising set at the nil index: a tagged `TW` world, the local part a part of it. -/
  | nil {fρ ρf ρ : WRes} {ps : List FrameRec} {ls : List SRec} :
      TW fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
      Arises ⟨fρ, ρf, ρ, ps, ls, [], []⟩
  /-- A run, at the stack, of a term the probe's rules derive, its captured values arising. -/
  | run {c c' : Cfg} {Δ : LifeCtx} {Γ : Ctx VTy} {e₀ : Expr} {j : Jdg} {γ : List Val}
      {t : Expr} :
      Arises c → ProbeRules Δ Γ e₀ j → (∀ w ∈ γ, ArisesVal w) →
      RunEnd (ℍ := ℍ) c (substAll γ e₀) c' t → Arises c'
  /-- A part of the local resource, the rest joining the frame. -/
  | part {c : Cfg} {ρ₁ ρ₂ ρf' : WRes} :
      Arises c → ResU.CompS ρ₁ ρ₂ c.ρ → ResU.CompS c.ρf ρ₂ ρf' → ResU.Hash ρf' ρ₁ →
      Arises ⟨c.fρ, ρf', ρ₁, c.ps, c.ls, c.σ, c.αs⟩
  /-- A 6.65 lend opened. -/
  | lendMut {c c' : Cfg} {e : LEnt} : Arises c → LendMut c c' e → Arises c'
  /-- A 6.64 lend opened. -/
  | lendImm {c c' : Cfg} {e : LEnt} : Arises c → LendImm c c' e → Arises c'
  /-- A handler of the names `N` installed around the computation. -/
  | hide {c : Cfg} (N : UInt32 → Bool) :
      Arises c → Arises ⟨c.fρ, c.ρf, c.ρ, c.ps, c.ls, hideS N c.σ, c.αs⟩
/-- **The values that arise at a configuration** (DESIGN §11 item 3): the answer of a run of a
term the probe's rules derive, the derivation exhibited; or the place a lend row hands its
callback. -/
inductive ArisesV : Cfg → Val → Prop where
  | ret {c c' : Cfg} {Δ : LifeCtx} {Γ : Ctx VTy} {e₀ : Expr} {j : Jdg} {γ : List Val}
      {v : Val} :
      Arises c → ProbeRules Δ Γ e₀ j → (∀ w ∈ γ, ArisesVal w) →
      RunEnd (ℍ := ℍ) c (substAll γ e₀) c' (.val v) → ArisesV c' v
  | view {c c' : Cfg} {e : LEnt} :
      Arises c → (LendMut c c' e ∨ LendImm c c' e) → ArisesV c' (.loc e.l)
/-- A value that arises at some configuration: what a run may capture. -/
inductive ArisesVal : Val → Prop where
  | at {c : Cfg} {v : Val} : ArisesV c v → ArisesVal v
end

/-- **`Arises` reaches past the nil index**: some configuration with an open lend arises. Its
proof is a world with an owned cell and a 6.65 lend of it. -/
def ArisesNonVacuous : Prop := ∃ c : Cfg, Arises (ℍ := ℍ) c ∧ c.σ ≠ []

end ProbeD1

end
