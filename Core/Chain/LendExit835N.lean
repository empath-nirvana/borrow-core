import Core.Chain.SI.ErwpK

/-!
# Posts across a lend's exit, at the Kripke stop  `[spec §19, §27]`

`docs/new-core/scope-835-lendexit.md`. After `vN_local`, a lend's callback result is a value at the
lender's location typing `Θ`. If `U` read its futures along `ExtP` at the world's floor, that value
would be one at the lend's floor `α` only, and the lender would post at the lower floor. A stop the
lender makes afterwards would then owe its continuation along `ExtP α`. A handler around the lender
reading `κ` at `U` at its own floor `lo > α` asks for more than that.

**The order of an entry outside `Sched`** (`KW.OwedR`). Under the restriction (`Restrict835N.lean`,
(S1)) no lend's callback performs a resuming operation outside `Sched`. So a stop at such a name has
no lend frame between the `perform` and its handler, and the Mut Frame's fold, the one producer that
needs `ExtP` (`Kappa835N.not_extRFoldTransfer`), never builds it. Its entry may owe the continuation
along `ExtR` at the continuation's share, at every valid location typing and every consistent view:
`KW.OwedR`. That is the order `vN`'s `U` clause reads today (`Goal791N.vN`, `.thunk`). It reads no
floor, so the floor of the world the stop was made at, and the floor the stop chose, do not change
what is owed (`contShareK_owedR_lo`), and the obligation has `U`'s quantifiers at every floor
(`contShareK_owedR_U`). `vN` at `U` is `KapRelR`, the same quantifiers (`vN_thunk_iff_kapRelR`).

**Configurations** (each hypothesis discharged):

* `flooredExit`: at the empty world, a key's lifetime `β` with `α < β ≤ lo`. The stuck `κ = ()`
  meets the obligation along `ExtP α` (`kapRelP_floor_world`: no `Mut` answer at `β` exists in any
  public extension at `α`), and fails `U` read along `ExtP lo` (`Public835N.not_kapRelP_world`). So
  if `U` reads a floor, a handler at `lo` cannot read at `U` a `κ` stopped at the lowered floor `α`.
* `not_kapRelR_world`: the same `κ` fails the order outside `Sched`, at the same world and share.
  `ExtR` reaches the world with the key at `β` whatever the floor.
* `owedR_not_owed`: the order of a stop under a live lend (`KW.Owed` at the lend's floor) owes fewer
  worlds than `KW.OwedR`. So a stop at a `Sched` name is still not readable at `U`; the restriction
  stays where it is.
* `not_owed_post_lower` and `not_tabLe_post_lower`: `KW.Owed`'s floor bound is not carried along a
  post that lowers the floor, so a table whose `Sched` entries owe along `KW.Owed` at the world is
  not `TableK.Le` along such a post (`erwpK_shift`'s `hTV`). With `U` floor-free a post has no need to
  lower the floor.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont performE raiseE opPayload)

/-! ### The order of an entry outside `Sched` -/

/-- **The worlds a stop outside `Sched` owes its continuation at**: `ExtR` at the share, a valid
location typing and every view consistent with the share. It reads no floor. -/
def KW.OwedR (x y : KW) (ρ : WRes) : Prop :=
  x.Θ.ExtR y.Θ ρ ∧ y.Θ.OK ∧ ConsistentX y.c ρ

theorem KW.owedR_self {x : KW} (hΘ : x.Θ.OK) {ρ : WRes} (hc : ConsistentX x.c ρ) :
    x.OwedR x ρ :=
  ⟨LocTy.extR_refl _ _, hΘ, hc⟩

/-- A handler that resumes in place, at a post's world, resumes at an owed world. -/
theorem KW.owedR_of_post {x y : KW} (hxy : x.Post y) (hΘ : x.Θ.OK) {ρ : WRes}
    (hc : ConsistentX x.c ρ) : x.OwedR y ρ := by
  obtain ⟨hΘy, hcy, -⟩ := hxy
  refine ⟨?_, hΘy ▸ hΘ, hcy ▸ hc⟩
  rw [hΘy]; exact LocTy.extR_refl _ _

theorem KW.OwedR.trans {x y z : KW} {ρ : WRes} (h₁ : x.OwedR y ρ) (h₂ : y.OwedR z ρ) :
    x.OwedR z ρ :=
  ⟨h₁.1.trans h₂.1, h₂.2.1, h₂.2.2⟩

/-- **The order under a live lend is a sub-order**: a world a `Sched` stop owes is one an entry
outside `Sched` would owe. -/
theorem KW.Owed.owedR {x y : KW} {f : Life} {ρ : WRes} (h : x.Owed f y ρ) : x.OwedR y ρ :=
  ⟨h.1.extR, h.2.1, h.2.2.1⟩

/-- **`OwedR` reads no floor**: the stop's world at any floor owes the same worlds. -/
theorem KW.owedR_floor (x : KW) (lo : Life) (y : KW) (ρ : WRes) :
    (⟨x.Θ, x.c, lo⟩ : KW).OwedR y ρ ↔ x.OwedR y ρ :=
  Iff.rfl

/-- **A stop at an entry owing along `OwedR` is a stop at every floor bound**: neither the floor
the world had when the stop was made nor the floor the stop chose is read. -/
theorem contShareK_owedR_lo {x : KW} {en : OpEntK KW} (hwk : ∀ f y ρ, en.wk f y ρ ↔ x.OwedR y ρ)
    (lo lo' : Life) {k : Nat} {ls : List SRec} {K : Kont} {Ψ : ContK KW} {ρ : WRes}
    (h : contShareK en lo k ls K Ψ ρ) : contShareK en lo' k ls K Ψ ρ := by
  obtain ⟨hu, f, -, hc⟩ := h
  exact ⟨hu, lo', le_rfl, fun y hy => hc y ((hwk f y ρ).mpr ((hwk lo' y ρ).mp hy))⟩

/-- **E10's world step at the Kripke stop**: a stop at an entry owing along `OwedR` owes its
continuation at every location typing `ExtR` reaches at the share, every view consistent with the
share and every floor, which are the futures `vN`'s `U` clause reads. -/
theorem contShareK_owedR_U {x : KW} {en : OpEntK KW} (hwk : ∀ f y ρ, en.wk f y ρ ↔ x.OwedR y ρ)
    {lo : Life} {k : Nat} {ls : List SRec} {K : Kont} {Ψ : ContK KW} {ρ : WRes}
    (h : contShareK en lo k ls K Ψ ρ) :
    ∀ Θ' : LocTy, x.Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ fl : Life, ∀ ls',
      en.wc ls ls' ρ →
      (∀ k', k' < k → ∀ w : Val,
        (en.PB ⟨Θ', c, fl⟩ k' ls' w ─⋆ Ψ ⟨Θ', c, fl⟩ k' ls' (K.plug (.val w))) ρ) ∧
      (en.q ≠ .lin → cancelOKK en ⟨Θ', c, fl⟩ k ls' K ρ) := by
  obtain ⟨-, f, -, hc⟩ := h
  intro Θ' hE hOK c hcc fl ls' hw
  exact hc ⟨Θ', c, fl⟩ ((hwk f _ ρ).mpr ⟨hE, hOK, hcc⟩) ls' hw

namespace LendExit835N
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Fig16.LogRel.Core.Chain.SI.Public835N
open BoCa.Lifetime (LSub LifeVar)

/-- **`κ` owed along `ExtR`**: at every extension of the stop's world along `ExtR` at the share,
every view consistent with the share and every record list, `κ` is in `𝒞⟦C⟧`. -/
def KapRelR (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (κ : Val) (ρ : WRes) : Prop :=
  ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls,
    cN (ℍ := ℍ) C δ Θ' c n ls (forceE C κ.1) ρ

/-- **`U` at `vN` is `KapRelR`.** -/
theorem vN_thunk_iff_kapRelR (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (κ : Val) (ρ : WRes) :
    vN (ℍ := ℍ) (.thunk C) δ Θ n κ ρ ↔ KapRelR (ℍ := ℍ) C δ Θ n κ ρ :=
  Iff.rfl

/-- **A public extension of the empty world at `α` holds no `Mut` value at a lifetime above `α`**:
such a value is at a key at or above its lifetime, and `ExtP α` adds no key above `α`. -/
theorem not_bMut_extP (x : LifeVar) (δ : LSub) {α β : Life} (hαβ : α < β) {Θ' : LocTy}
    {ρ : WRes} (hE : LocTy.empty.ExtP α Θ' ρ) {k : Nat} {w : Val} {σ : WRes} :
    ¬ vN (ℍ := ℍ) (bMut x) (δ.extend x β) Θ' k w σ := by
  rintro ⟨a, ha, b, hab, ⟨l, _, _, _, _, _, _, _, hl, _⟩, -⟩
  rw [interp_ext_self] at ha
  cases Option.some.inj ha
  rw [hE.2.1 l b (lt_of_lt_of_le hαβ hab)] at hl
  simp at hl

/-- **The obligation at the lowered floor `α` holds of the stuck `κ`** at the empty world, when the
answer type's lifetime `β` is above `α`. -/
theorem kapRelP_floor_world (x : LifeVar) (δ : LSub) {α β : Life} (hαβ : α < β) (κ : Val)
    (ρ : WRes) : KapRelP (ℍ := ℍ) α (kTyC x) (δ.extend x β) LocTy.empty 1 κ ρ := by
  intro Θ' hE _ c _ ls
  exact ⟨fun _ _ _ _ _ _ _ hv _ => absurd hv (not_bMut_extP x δ hαβ hE), trivial⟩

/-- **The floored reading after a lend's exit.** The stop at the empty world, at the lowered floor
`α`, owes the stuck `κ = ()` nothing along `ExtP α`; `U` read along `ExtP lo`, at the floor
`lo ≥ β > α` of a handler around the lender, reaches the world with a key at `β`, where `κ` fails. -/
theorem flooredExit (x : LifeVar) (δ : LSub) {N α β b lo : Life} (hNβ : N < β) (hαβ : α < β)
    (hβ : β ≤ lo) {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some β) :
    α < lo ∧ KapRelP (ℍ := ℍ) α (kTyC x) (δ.extend x β) LocTy.empty 1 Val.unit (ρb m b) ∧
      ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x β) LocTy.empty 1 Val.unit (ρb m b) :=
  ⟨lt_of_lt_of_le hαβ hβ, kapRelP_floor_world x δ hαβ _ _,
    not_kapRelP_world x δ hNβ hβ hml c hcm hcl⟩

/-- **The order outside `Sched` excludes the same `κ`**: `ExtR` reaches the world with the key at
`β` from the empty world at every floor, where `κ = ()` fails. -/
theorem not_kapRelR_world (x : LifeVar) (δ : LSub) {N β b : Life} (hNβ : N < β) {m l' : Loc}
    (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b) (hcl : c l' = some β) :
    ¬ KapRelR (ℍ := ℍ) (kTyC x) (δ.extend x β) LocTy.empty 1 Val.unit (ρb m b) := fun h =>
  not_kTy_at x δ hml c hcm hcl (h _ ((LocTy.extA_add (fun _ _ h => absurd rfl h) l' _).extR _)
    (Θ₁_ok x _ hNβ l') c (consistentX_single_mut (consistentX_empty c) hcm) [])

/-- **The configuration at concrete lifetimes**: the share's cell at `0` lent at the top lifetime,
the handler's floor and the key's lifetime `1`, the floor after the exit `2`, the key at `1`. -/
theorem flooredExit_inst :
    let α : Life := OrderDual.toDual 2
    let β : Life := OrderDual.toDual 1
    let b : Life := OrderDual.toDual 0
    let c : Loc → Option Life := fun y => if y = 0 then some b else if y = 1 then some β else none
    α < β ∧ KapRelP (ℍ := ℍ) α (kTyC 0) (LSub.empty.extend 0 β) LocTy.empty 1 Val.unit (ρb 0 b) ∧
      ¬ KapRelP (ℍ := ℍ) β (kTyC 0) (LSub.empty.extend 0 β) LocTy.empty 1 Val.unit (ρb 0 b) ∧
      ¬ KapRelR (ℍ := ℍ) (kTyC 0) (LSub.empty.extend 0 β) LocTy.empty 1 Val.unit (ρb 0 b) ∧
      ConsistentX c (ρb 0 b) := by
  intro α β b c
  have hαβ : α < β := OrderDual.toDual_lt_toDual.mpr (by decide)
  obtain ⟨-, h₁, h₂⟩ := flooredExit (ℍ := ℍ) 0 LSub.empty hαβ hαβ le_rfl (m := 0) (l' := 1)
    (by decide) c rfl rfl
  exact ⟨hαβ, h₁, h₂, not_kapRelR_world 0 LSub.empty hαβ (m := 0) (l' := 1) (by decide) c rfl rfl,
    consistentX_single_mut (consistentX_empty c) rfl⟩

/-- **A stop under a live lend owes fewer worlds than `OwedR`**: a key added above the lend's floor
`α` is an `ExtR` move and not an `ExtP α` one. -/
theorem owedR_not_owed {α β : Life} (hαβ : α < β) (c : Loc → Option Life) (lo : Life) :
    let G : Nat → Val → SPropS Loc Val β := fun _ _ _ => True
    let x : KW := ⟨LocTy.empty, c, lo⟩
    let y : KW := ⟨LocTy.empty.add 1 β G, c, lo⟩
    x.OwedR y PMap.empty ∧ ¬ x.Owed α y PMap.empty := by
  intro G x y
  have hG : DownFam β G := fun _ _ _ _ => trivial
  have hfr : y.Θ.Fresh α := LocTy.fresh_add (N := α) (fun _ _ h => absurd rfl h) le_rfl hαβ 1 G
  refine ⟨⟨(LocTy.extA_add (fun _ _ h => absurd rfl h) 1 G).extR _,
    ⟨LocTy.down_add LocTy.empty_down 1 hG, ⟨α, hfr⟩⟩, consistentX_empty c⟩, fun h => ?_⟩
  exact not_extP_foldConfig hαβ G _ h.1

/-- **`KW.Owed` is not carried along a post that lowers the floor**: the stop's own world is owed
at the higher floor, and not at the lower one. -/
theorem not_owed_post_lower {lo lo' : Life} (hlt : lo' < lo) (f : Life) (c : Loc → Option Life) :
    let x : KW := ⟨LocTy.empty, c, lo⟩
    let y : KW := ⟨LocTy.empty, c, lo'⟩
    x.Post y ∧ x.Owed f x PMap.empty ∧ ¬ y.Owed f x PMap.empty := by
  intro x y
  exact ⟨⟨rfl, rfl, hlt.le⟩, KW.owed_self LocTy.empty_ok f (consistentX_empty c),
    fun h => absurd h.2.2.2.1 (not_le.mpr hlt)⟩

/-- A `Sched` entry at the world `w`: resuming, linear, its order `KW.Owed` at `w`. -/
def schedEnt (w : KW) : OpEntK KW where
  q := .lin
  abort := false
  PA := fun _ _ _ _ => True
  PB := fun _ _ _ _ _ => True
  fin := none
  wc := fun _ _ _ => True
  wk := fun f z ρ => w.Owed f z ρ

/-- **A table of `Sched` entries owing along `KW.Owed` is not `Le` along a post that lowers the
floor**: the continuation that runs only at floors at most `lo'` is owed at the lower world's table
and not at the higher one's, which owes the stop's own world at `lo`. So `erwpK_shift`'s `hTV` fails
for such a table along `KW.Post`. -/
theorem not_tabLe_post_lower {lo lo' : Life} (hlt : lo' < lo) (c : Loc → Option Life)
    (n i : UInt32) (v : Val) :
    let x : KW := ⟨LocTy.empty, c, lo⟩
    let y : KW := ⟨LocTy.empty, c, lo'⟩
    x.Post y ∧ ¬ (opTableK lo' (fun _ _ => some (schedEnt y))).Le
      (opTableK lo (fun _ _ => some (schedEnt x))) := by
  intro x y
  refine ⟨⟨rfl, rfl, hlt.le⟩, fun hle => ?_⟩
  let Ψ : ContK KW := fun z _ _ _ _ => z.lo ≤ lo'
  have hy : opTableK lo' (fun _ _ => some (schedEnt y)) 1 []
      ((Kont.hole : Kont).plug (performE (.val (opPayload n i v)))) Ψ PMap.empty := by
    refine Or.inl ⟨Kont.hole, n, i, v, schedEnt y, pure_sep_mk ⟨rfl, rfl, rfl, rfl⟩
      ⟨PMap.empty, PMap.empty, compS_empty_left _, trivial, ?_⟩⟩
    unfold contShareK
    exact ⟨fun h => by simp [schedEnt] at h, lo', le_rfl,
      fun z hz _ _ => ⟨fun _ _ _ _ _ _ _ => hz.2.2.2.1, fun hq => absurd rfl hq⟩⟩
  rcases hle _ _ _ _ _ hy with ⟨K, n', i', v', en, hp⟩ | ⟨K, n', i', v', en, hp⟩
  · obtain ⟨⟨-, -, hT, -⟩, ρa, ρk, hc, -, -, f, -, hcont⟩ := pure_sep_iff.mp hp
    cases Option.some.inj hT
    have hck : ConsistentX c ρk := consistentX_right hc (consistentX_empty c) LogRel.valid_empty
    have h := ((hcont x (KW.owed_self LocTy.empty_ok f hck) [] trivial).1 0 (by decide) v
      PMap.empty ρk trivial (ResU.comp_empty_right ρk))
    exact absurd h (not_le.mpr hlt)
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    cases Option.some.inj hT
    cases ha

end LendExit835N

end BoCa.Fig16.LogRel.Core.Chain.SI

end
