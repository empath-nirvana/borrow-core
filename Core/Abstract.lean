import Core.LetDtorFiles
import Core.Inversions
import Core.Stdio
import Core.PinDerives

/-!
# Core — abstract types and their provider  `[spec §63]`

An abstract type `abs n A` (`VTy.abs`) is named `n` and represented by the value type `A`, whose
relation it has (`vCE_abs_eq_rep`). The judgment `CDerivesIn P` is indexed by a provider set `P`:
`P n` when the derivation is inside the provider of `n`. Two rules read `P`, the iso between
`abs n A` and its representation:

    absSeal   (hn : P n) : CDerivesIn P Δ Γ e (.val A)         → CDerivesIn P Δ Γ e (.val (abs n A))
    absUnseal (hn : P n) : CDerivesIn P Δ Γ e (.val (abs n A)) → CDerivesIn P Δ Γ e (.val A)

The pinned judgment `CDerivesPIn P` has the same two rules, gated the same way. `CDerives` and
`CDerivesP` are the two judgments inside every provider, so every theorem about them reads as
before, and `CDerivesIn.mono`/`CDerivesPIn.mono` embed a derivation at any provider set into
them: `fundamentalC`, `fundamentalC_pin`, the adequacy theorems and `resourceSafety` hold of
every client.

**Encapsulation, the headline.** Outside `n`'s provider (`¬ P n`):

* `CDerivesIn.var_abs_not_rep` (and `CDerivesPIn.var_abs_not_rep`): a variable of type
  `abs n A` is never read at `A`, for every representation `A` whose head is not, by `μ`-unrolling
  and seals `P` allows, `abs n A` again (`RepNotOver`; every `A` whose head is no abstract type,
  `RepNotOver.of_head`). This fails if the unseal is ungated: inside the provider the read is
  `absUnseal` (`file_rep_inside`).
* `CDerivesIn.var_abs_hnf` (and `CDerivesPIn.var_abs_hnf`), what it is a corollary of: every
  judgment that reads such a variable at a value type `T` reads it at a `T` whose head (`AHnf`:
  boxes stripped, `μ` unrolled, abstract types kept) is `abs n A` under abstract types of `P`
  (`Over`). It is never read at the representation, nor at any type whose head is not over
  `abs n A`. At a provider set with no name (`Outside`, every checked program's, pinned or not:
  `checkProgram_outside`) the head is `abs n A` itself (`var_abs_hnf_none`).
* `not_skipClose_outside`: **the skip-close destructor of #775 is refused as a term** outside
  `File`'s provider: `λf. burn f; ()` has no derivation at `File ⊸ F_{close} 1`. Inside the
  provider it types (`d_skipClose_inside`).

What is not proved: that no rule other than the provider's two mentions `abs` is a reading of
the rule set, not a theorem. `var_abs_hnf` covers every rule that reads a variable, and
`not_skipClose_outside` the one wrong destructor; a constant added at a type over `abs n A`
would be a new rule, outside both. Encapsulation is relative to the chosen provider set; for a
type provided by externs (`fileC` below), which externs may mention `abs n` is an obligation of
the trusted extern table, not of the kernel.

**Linearity.** An abstract type is never persistent, whatever its representation
(`abs_not_persistent`): a client neither copies nor drops one. Outside the provider every type a
client reads it at is linear (`CDerivesIn.var_abs_linear`, `CDerivesPIn.var_abs_linear`), so a
handle over `I32` is linear (`absI32_linear_outside`). Inside the provider it is its representation
and may be copied (`d_absCopy_inside`): a provider that wants its clients to copy or drop exposes an
operation that does it.

**Restrictions.** An abstract type has its representation's relation. It is never own-free
(`VTy.OwnFree`: an abort never abandons one), it has no derived destructor (`HasDtor`), and its
immutable reborrow is `Unk` (`VTy.immReborrow`). An
abstract type is in the fold class only when it is closed (`FoldP.P`): a fold does not recurse
through one.

**The escape.** A deliberate escape is a provider-supplied forget: an operation of `Fs`, handled in
`with_fs`'s clauses (inside the provider), that unseals and burns. No such operation exists in
`Fs`; adding one is a clause in `with_fs` and an entry of `Efs`, nothing in the kernel. There is
no `trust` form, in Core or in the checker.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Kont freeE performE)
open BoCa.Lifetime (LifeCtx LSub)
open BoCa.Fig16.LogRel.Core.LetDtor.Files
open BoCa.Fig16.LogRel.Core.Inversions (Hnf VView ValCls LamCls CtxLe)

/-! ### Provider sets -/

/-- **The provider set outside every provider**: a client of every abstract type. -/
abbrev Outside : Nat → Prop := fun _ => False

/-- `P` without the name `n`. -/
def ProvWithout (P : Nat → Prop) (n : Nat) : Nat → Prop := fun m => P m ∧ m ≠ n

/-- At `P` without `n`, the seal and the unseal at `n` have no instance: their premise is
`ProvWithout P n n`, which is false. -/
theorem ProvWithout.not_self (P : Nat → Prop) (n : Nat) : ¬ ProvWithout P n n := fun h => h.2 rfl

/-- **`P` without a name it does not hold is `P`.** -/
theorem ProvWithout.eq_of_not {P : Nat → Prop} {n : Nat} (hn : ¬ P n) : ProvWithout P n = P := by
  funext m
  exact propext ⟨fun h => h.1, fun h => ⟨h, fun e => hn (e ▸ h)⟩⟩

/-- A derivation at a provider set that excludes `n` is one at `ProvWithout P n`. This is its
hypothesis restated, since that set is `P` itself (`ProvWithout.eq_of_not`), and it holds of an
ungated unseal as well: what encapsulation says is `CDerivesIn.var_abs_not_rep`.  `[spec §63]` -/
theorem CDerivesIn.provWithout {P : Nat → Prop} {n : Nat} (hn : ¬ P n) {Δ : LifeCtx}
    {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) :
    CDerivesIn (ProvWithout P n) Δ Γ e j := by
  rw [ProvWithout.eq_of_not hn]; exact h

/-! ### The head of a type, abstract types kept -/

theorem Ctx.SoloP.getElem? {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    Γ[i]? = some ⟨A, true⟩ := by
  induction h with
  | here => rfl
  | there _ ih => exact ih
  | skip _ _ ih => exact ih

theorem _root_.BoCa.Ctx.Dead.not_live : ∀ {Γ : Ctx VTy} (_ : Ctx.Dead Γ) {i : Nat} {A : VTy},
    Γ[i]? ≠ some ⟨A, true⟩
  | _, .nil, _, _, h => by simp at h
  | _, .cons _, 0, _, h => by simp at h
  | _, .cons hd, _ + 1, _, h => hd.not_live (by simpa using h)

theorem CTy.effOf_inj_right : ∀ {S S' : Row} {A A' : VTy},
    CTy.effOf S A = CTy.effOf S' A' → A = A'
  | [], [], _, _, h => by simpa [CTy.effOf] using h
  | [], _ :: _, _, _, h => by simp [CTy.effOf] at h
  | _ :: _, [], _, _, h => by simp [CTy.effOf] at h
  | _ :: _, _ :: _, _, _, h => by
      simp only [CTy.effOf, CTy.eff.injEq] at h
      exact CTy.effOf_inj_right h.2.2.2.2.2.2.2

/-- The judgments at which a term is read at the value type `A`: `A` itself, and `F_Σ A`. -/
def Jdg.AtVal (j : Jdg) (A : VTy) : Prop := ∃ S : Row, j = .val A ∨ j = .comp (CTy.effOf S A)

/-- **The head of a value type, abstract types kept**: boxes stripped and `μ` unrolled, an
abstract type a head of its own. (`Inversions.Hnf` strips abstract types too: inside every
provider the iso keeps a type's head.) -/
inductive AHnf : VTy → VTy → Prop
  | box {a : Lifetime.Life} {A h : VTy} : AHnf A h → AHnf (.box a A) h
  | mu {A h : VTy} : AHnf (VTy.inst (.mu A) A) h → AHnf (.mu A) h
  | base {T : VTy} (hb : ∀ a A, T ≠ .box a A) (hm : ∀ A, T ≠ .mu A) : AHnf T T

theorem AHnf.self {T : VTy} (hb : ∀ a A, T ≠ .box a A := by intro _ _ h; cases h)
    (hm : ∀ A, T ≠ .mu A := by intro _ h; cases h) : AHnf T T := .base hb hm

theorem AHnf.eq_self {T h : VTy} (hh : AHnf T h) (hb : ∀ a A, T ≠ .box a A := by
    intro _ _ h; cases h) (hm : ∀ A, T ≠ .mu A := by intro _ h; cases h) : h = T := by
  cases hh with
  | box _ => exact absurd rfl (hb _ _)
  | mu _ => exact absurd rfl (hm _)
  | base => rfl

theorem AHnf.unique {T h h' : VTy} (hh : AHnf T h) (hh' : AHnf T h') : h = h' := by
  induction hh generalizing h' with
  | box _ ih => cases hh' with
    | box hh' => exact ih hh'
    | base hb _ => exact absurd rfl (hb _ _)
  | mu _ ih => cases hh' with
    | mu hh' => exact ih hh'
    | base _ hm => exact absurd rfl (hm _)
  | base hb hm => exact (hh'.eq_self hb hm).symm

/-- **`k` is a head over `a` by abstract types of `P`**: `a`, or `abs m k'` with `P m` and the
head of `k'` over `a`. Inside `m`'s provider, a value of `k'` may be sealed into `abs m k'`. -/
inductive Over (P : Nat → Prop) (a : VTy) : VTy → Prop
  | refl : Over P a a
  | abs {m : Nat} {k h : VTy} : P m → AHnf k h → Over P a h → Over P a (.abs m k)

/-- A head over an abstract type is an abstract type. -/
theorem Over.isAbs {P : Nat → Prop} {n : Nat} {A h : VTy} (ho : Over P (.abs n A) h) :
    ∃ m B, h = .abs m B := by
  cases ho with
  | refl => exact ⟨_, _, rfl⟩
  | abs _ _ _ => exact ⟨_, _, rfl⟩

/-- At a provider set with no name, a head over `a` is `a`. -/
theorem Over.eq_of_none {P : Nat → Prop} (hP : ∀ m, ¬ P m) {a h : VTy} (ho : Over P a h) :
    h = a := by
  cases ho with
  | refl => rfl
  | abs hm _ _ => exact absurd hm (hP _)

/-- A type whose head is `abs m B` has `B`'s head, abstract types stripped. -/
theorem AHnf.hnf_abs {T k : VTy} (hT : AHnf T k) {m : Nat} {B h : VTy} (hk : k = .abs m B)
    (hB : Hnf B h) : Hnf T h := by
  induction hT with
  | box _ ih => exact .box (ih hk)
  | mu _ ih => exact .mu (ih hk)
  | base => subst hk; exact .abs hB

/-- **A type whose head is over `abs n X` has `X`'s head**, abstract types stripped. -/
theorem Over.hnf {P : Nat → Prop} {n : Nat} {X hX : VTy} (hXh : Hnf X hX) {k : VTy}
    (ho : Over P (.abs n X) k) : ∀ {T : VTy}, AHnf T k → Hnf T hX := by
  induction ho with
  | refl => intro T hT; exact hT.hnf_abs rfl hXh
  | abs _ hk' _ ih => intro T hT; exact hT.hnf_abs rfl (ih hk')

/-! ### Encapsulation: outside its provider, an abstract type is never its representation -/

/-- **Outside its provider, a variable of an abstract type is read only at types over it**: at
every judgment that reads it at a value type `T`, `T`'s head (`AHnf`: boxes stripped, `μ` unrolled,
abstract types kept) is `abs n A` under abstract types of `P` (`Over`). So it is never read at its
representation `A`, nor at any type whose head is not over `abs n A`. The proof is an induction
over the whole rule set; the cases that read a variable at another judgment are `var`, `force`,
the `F`, `!`, `[]`, `⊑`, `μ`, `ν` and row-weakening rules, and the provider's two. At `¬ P n` the
unseal at `n` has no instance, and an unseal at another name `m` takes off only a seal at `m`.
`[spec §63]` -/
theorem CDerivesIn.var_abs_hnf {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) :
    ∀ {i : Nat} {T : VTy}, e = .var i → j.AtVal T → Γ[i]? = some ⟨.abs n A, true⟩ →
      ∃ k, AHnf T k ∧ Over P (.abs n A) k := by
  induction h with
  | var hs =>
      intro i T he hj hΓ
      cases he
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        rw [hs.getElem?] at hΓ
        cases hΓ
        exact ⟨_, AHnf.self, .refl⟩
      · cases hj
  | force hs =>
      intro i T he hj hΓ
      rename_i C
      cases C <;> simp only [forceE] at he <;> (try cases he) <;>
        (rw [hs.getElem?] at hΓ; cases hΓ)
  | ret _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · have hA := CTy.effOf_inj_right (S := []) (Jdg.comp.inj hj)
        subst hA
        exact ih he ⟨[], .inl rfl⟩ hΓ
  | ofRet _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj; exact ih he ⟨[], .inr rfl⟩ hΓ
      · cases hj
  | effSub _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · rw [← CTy.effOf_inj_right (Jdg.comp.inj hj)]
        exact ih he ⟨_, .inr rfl⟩ hΓ
  | nuIn _ _ _ =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · exact absurd (Jdg.comp.inj hj).symm (Inversions.effOf_ne_nu _ _ _)
  | nuOut hC _ _ =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · obtain ⟨C₁, C₂, hu⟩ := Inversions.unroll_amp hC
        have hj := Jdg.comp.inj hj
        rw [hu] at hj
        exact absurd hj.symm (Inversions.effOf_ne_amp _ _ _ _)
  | bangE _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain ⟨m, B, rfl⟩ := ho.isAbs
        cases h'.eq_self
      · cases hj
  | boxI _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨k, .box h', ho⟩
      · cases hj
  | boxE _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | box h' => exact ⟨k, h', ho⟩
        | base hb _ => exact absurd rfl (hb _ _)
      · cases hj
  | immSub _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain ⟨m, B, rfl⟩ := ho.isAbs
        cases h'.eq_self
      · cases hj
  | mutSub _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain ⟨m, B, rfl⟩ := ho.isAbs
        cases h'.eq_self
      · cases hj
  | roll _ _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨k, .mu h', ho⟩
      · cases hj
  | unroll _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | mu h' => exact ⟨k, h', ho⟩
        | base _ hm => exact absurd rfl (hm _)
      · cases hj
  | absSeal hm _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨_, AHnf.self, .abs hm h' ho⟩
      · cases hj
  | absUnseal hm _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain rfl := h'.eq_self
        cases ho with
        | refl => exact absurd hm hn
        | abs _ hk ho => exact ⟨_, hk, ho⟩
      · cases hj
  | _ => intro i T he hj _; first | cases he | (obtain ⟨S, hj | hj⟩ := hj <;> cases hj) | simp_all

/-- **At a provider set with no name, the head is the abstract type itself.**  `[spec §63]` -/
theorem CDerivesIn.var_abs_hnf_none {P : Nat → Prop} (hP : ∀ m, ¬ P m) {n : Nat} {A : VTy}
    {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) {i : Nat}
    {T : VTy} (he : e = .var i) (hj : j.AtVal T) (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) :
    AHnf T (.abs n A) := by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf (hP n) he hj hΓ
  rw [ho.eq_of_none hP] at hk
  exact hk

/-- **The representation is not, up to its head, its abstract type again**: no head of `A` is
over `abs n A` by abstract types of `P`. It holds at every `A` whose head is no abstract type
(`RepNotOver.of_head`), so at every record, sum, reference, borrow, opaque type and thunk. It
fails at a representation that unrolls to the abstract type itself, `μX. abs n X`, where reading
the variable at `A` is a `roll`, not an unseal (`var_abs_rep_mu`). -/
def RepNotOver (P : Nat → Prop) (n : Nat) (A : VTy) : Prop := ∀ h, AHnf A h → ¬ Over P (.abs n A) h

theorem RepNotOver.of_head {P : Nat → Prop} {n : Nat} {A h : VTy} (hh : AHnf A h)
    (hna : ∀ m B, h ≠ .abs m B) : RepNotOver P n A := fun h' hh' ho => by
  obtain rfl := hh.unique hh'
  obtain ⟨m, B, rfl⟩ := ho.isAbs
  exact hna m B rfl

/-- `μX. abs n X`: an abstract type that is its own representation, unrolled. -/
abbrev muAbs (n : Nat) : VTy := .mu (.abs n (.tvar 0))

/-- **`RepNotOver` is needed**: at `A = μX. abs n X`, outside every provider, a variable of
`abs n A` is read at `A`, by `roll`. No unseal is used: `abs n A` is `A` unrolled. -/
theorem var_abs_rep_mu (n : Nat) {Δ : LifeCtx} :
    CDerivesIn Outside Δ [⟨.abs n (muAbs n), true⟩] (.var 0) (.val (muAbs n)) :=
  .roll trivial (by simp [VTy.Cl]) (.var (.here .nil))

/-- **Outside its provider, a variable of an abstract type is never read at its
representation.** It fails if the unseal is ungated: inside the provider the read is `absUnseal`
(`file_rep_inside`).  `[spec §63]` -/
theorem CDerivesIn.var_abs_not_rep {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    (hA : RepNotOver P n A) {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat}
    (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) : ¬ CDerivesIn P Δ Γ (.var i) (.val A) := fun h => by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  exact hA k hk ho

/-- **Outside its provider, a variable of an abstract type is never a `Tok`**: `burn`, which takes
a `Tok`, does not take it.  `[spec §63]` -/
theorem CDerivesIn.var_abs_not_tok {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) :
    ¬ CDerivesIn P Δ Γ (.var i) (.val tokTy) := fun h => by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  obtain ⟨m, B, rfl⟩ := ho.isAbs
  cases hk.eq_self

/-! ### The pinned judgment -/

/-- **`var_abs_hnf` in the pinned judgment**: the relaxed lends conclude at no variable, and
`nilDead`'s context holds no live slot.  `[spec §29, §63]` -/
theorem CDerivesPIn.var_abs_hnf {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesPIn P Δ Γ e j) :
    ∀ {i : Nat} {T : VTy}, e = .var i → j.AtVal T → Γ[i]? = some ⟨.abs n A, true⟩ →
      ∃ k, AHnf T k ∧ Over P (.abs n A) k := by
  induction h with
  | var hs =>
      intro i T he hj hΓ
      cases he
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        rw [hs.getElem?] at hΓ
        cases hΓ
        exact ⟨_, AHnf.self, .refl⟩
      · cases hj
  | force hs =>
      intro i T he hj hΓ
      rename_i C
      cases C <;> simp only [forceE] at he <;> (try cases he) <;>
        (rw [hs.getElem?] at hΓ; cases hΓ)
  | nilDead hΓd _ _ => intro i T _ _ hΓ; exact absurd hΓ hΓd.not_live
  | ret _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · have hA := CTy.effOf_inj_right (S := []) (Jdg.comp.inj hj)
        subst hA
        exact ih he ⟨[], .inl rfl⟩ hΓ
  | ofRet _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj; exact ih he ⟨[], .inr rfl⟩ hΓ
      · cases hj
  | effSub _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · rw [← CTy.effOf_inj_right (Jdg.comp.inj hj)]
        exact ih he ⟨_, .inr rfl⟩ hΓ
  | nuIn _ _ _ =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · exact absurd (Jdg.comp.inj hj).symm (Inversions.effOf_ne_nu _ _ _)
  | nuOut hC _ _ =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · obtain ⟨C₁, C₂, hu⟩ := Inversions.unroll_amp hC
        have hj := Jdg.comp.inj hj
        rw [hu] at hj
        exact absurd hj.symm (Inversions.effOf_ne_amp _ _ _ _)
  | bangE _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain ⟨m, B, rfl⟩ := ho.isAbs
        cases h'.eq_self
      · cases hj
  | boxI _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨k, .box h', ho⟩
      · cases hj
  | boxE _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | box h' => exact ⟨k, h', ho⟩
        | base hb _ => exact absurd rfl (hb _ _)
      · cases hj
  | immSub _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain ⟨m, B, rfl⟩ := ho.isAbs
        cases h'.eq_self
      · cases hj
  | mutSub _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain ⟨m, B, rfl⟩ := ho.isAbs
        cases h'.eq_self
      · cases hj
  | roll _ _ _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨k, .mu h', ho⟩
      · cases hj
  | unroll _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | mu h' => exact ⟨k, h', ho⟩
        | base _ hm => exact absurd rfl (hm _)
      · cases hj
  | absSeal hm _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨_, AHnf.self, .abs hm h' ho⟩
      · cases hj
  | absUnseal hm _ ih =>
      intro i T he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        obtain rfl := h'.eq_self
        cases ho with
        | refl => exact absurd hm hn
        | abs _ hk ho => exact ⟨_, hk, ho⟩
      · cases hj
  | _ => intro i T he hj _; first | cases he | (obtain ⟨S, hj | hj⟩ := hj <;> cases hj) | simp_all

/-- **`var_abs_not_rep` in the pinned judgment.**  `[spec §29, §63]` -/
theorem CDerivesPIn.var_abs_not_rep {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    (hA : RepNotOver P n A) {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat}
    (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) : ¬ CDerivesPIn P Δ Γ (.var i) (.val A) := fun h => by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  exact hA k hk ho

/-- **`var_abs_not_tok` in the pinned judgment.**  `[spec §29, §63]` -/
theorem CDerivesPIn.var_abs_not_tok {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) :
    ¬ CDerivesPIn P Δ Γ (.var i) (.val tokTy) := fun h => by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  obtain ⟨m, B, rfl⟩ := ho.isAbs
  cases hk.eq_self

/-! ### Outside its provider, an abstract type is linear

`abs n A` is not persistent at any `A` (`VTy.persistent`), so no context split duplicates a slot
of it (`Ctx.SplitP.dup`) and no leaf drops one (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`). Outside the
provider that holds of every type a client reads such a value at: the provider's route to a copy,
reading it at a persistent representation, is the unseal. -/

/-- **An abstract type is never persistent**, whatever its representation.  `[spec §10, §63]` -/
theorem abs_not_persistent (n : Nat) (A : VTy) : ¬ (VTy.abs n A).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

/-- A type whose head, abstract types kept, is an abstract type is not persistent. -/
theorem AHnf.persistent_false_abs {T k : VTy} (hT : AHnf T k) {m : Nat} {B : VTy}
    (hk : k = .abs m B) : T.persistent = false := by
  induction hT with
  | box _ ih => simpa [VTy.persistent] using ih hk
  | mu _ ih =>
      rename_i A _ _
      have := ih hk
      rw [Inversions.persistent_inst_mu] at this
      simpa [VTy.persistent] using this
  | base => subst hk; rfl

/-- **Outside its provider, a value of an abstract type is read only at linear types**, at every
representation `A`, `I32` among them: every type a variable of `abs n A` is read at is not
persistent. So whatever a client binds it to, no split duplicates it and no leaf drops it: a client
neither copies nor drops an `abs n A` (no `dup` at `P` with `¬ P n`). It fails if `abs n A` is
persistent when `A` is (the read at `abs n I32` itself), and if the unseal is ungated: inside the
provider the variable is read at `A` (`abs_rep_inside`), and a persistent `A` is copied
(`d_absCopy_inside`). A provider that wants its clients to copy or drop exposes an operation that
does it.  `[spec §10, §63]` -/
theorem CDerivesIn.var_abs_linear {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {j : Jdg} {T : VTy} (h : CDerivesIn P Δ Γ (.var i) j)
    (hj : j.AtVal T) (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) : ¬ T.Persistent := by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf hn rfl hj hΓ
  obtain ⟨m, B, rfl⟩ := ho.isAbs
  simp [VTy.Persistent, hk.persistent_false_abs rfl]

/-- **`var_abs_linear` in the pinned judgment**, so for every checked program
(`checkProgram_outside`).  `[spec §29, §63]` -/
theorem CDerivesPIn.var_abs_linear {P : Nat → Prop} {n : Nat} {A : VTy} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {j : Jdg} {T : VTy} (h : CDerivesPIn P Δ Γ (.var i) j)
    (hj : j.AtVal T) (hΓ : Γ[i]? = some ⟨.abs n A, true⟩) : ¬ T.Persistent := by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf hn rfl hj hΓ
  obtain ⟨m, B, rfl⟩ := ho.isAbs
  simp [VTy.Persistent, hk.persistent_false_abs rfl]

/-- **A linear handle over `I32`**: outside its provider, a variable of `abs n I32` is read at no
persistent type, though `I32` is persistent.  `[spec §63]` -/
theorem absI32_linear_outside {P : Nat → Prop} {n : Nat} (hn : ¬ P n) {Δ : LifeCtx}
    {Γ : Ctx VTy} {j : Jdg} {T : VTy} (h : CDerivesIn P Δ (⟨.abs n I32, true⟩ :: Γ) (.var 0) j)
    (hj : j.AtVal T) : ¬ T.Persistent ∧ I32.Persistent :=
  ⟨h.var_abs_linear hn hj rfl, rfl⟩

/-- Inside its provider an abstract value is its representation, by the unseal: the read
`var_abs_linear` refuses when the representation is persistent. -/
theorem abs_rep_inside {P : Nat → Prop} {n : Nat} (hP : P n) (A : VTy) {Δ : LifeCtx}
    {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerivesIn P Δ (⟨.abs n A, true⟩ :: Γ) (.var 0) (.val A) :=
  .absUnseal hP (.var (.here hΓ))

/-- The provider's copy of a handle: `λx. y ← return x; return (y, y)`, with `x` unsealed to its
representation and each copy sealed again. -/
def absCopyB : Expr := bindE (.var 0) (.pair (.var 0) (.var 0))

/-- **Inside its provider a handle over a persistent representation is copied**, at
`abs n A ⊸ F (abs n A ⊗ abs n A)`: the operation a provider exposes to let its clients copy. The
duplication is of `y : A`, after the unseal.  `[spec §63]` -/
theorem d_absCopy_inside {P : Nat → Prop} {n : Nat} (hP : P n) {A : VTy} (hA : A.Persistent)
    {Δ : LifeCtx} :
    CDerivesIn P Δ [] (.val (.lam absCopyB))
      (.comp (.arr (.abs n A) (.ret (.tensor (.abs n A) (.abs n A))))) :=
  .lam (.bind (.left .nil) (.ret (abs_rep_inside hP A .nil))
    (.ret (.tensorI (.dup hA (.dead .nil)) (.absSeal hP (.var (.here (.cons .nil))))
      (.absSeal hP (.var (.here (.cons .nil)))))))

/-! ### `File` outside and inside `with_fs` -/

/-- **Outside `File`'s provider a `File` is never a `Tok`.**  `[spec §63]` -/
theorem file_not_tok_outside {Δ : LifeCtx} {Γ : Ctx VTy} :
    ¬ CDerivesIn Outside Δ (⟨File, true⟩ :: Γ) (.var 0) (.val tokTy) :=
  CDerivesIn.var_abs_not_tok (n := fileName) id rfl

/-- **Outside its provider, a file at any representation is never that representation.**
`[spec §63]` -/
theorem file_not_rep_outside {A : VTy} (hA : RepNotOver Outside fileName A) {Δ : LifeCtx}
    {Γ : Ctx VTy} : ¬ CDerivesIn Outside Δ (⟨absTy fileName A, true⟩ :: Γ) (.var 0) (.val A) :=
  CDerivesIn.var_abs_not_rep (n := fileName) id hA rfl

/-- Inside its provider a file is its representation, by the unseal: what
`file_not_rep_outside` refuses. -/
theorem file_rep_inside {P : Nat → Prop} (hP : P fileName) (A : VTy) {Δ : LifeCtx}
    {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerivesIn P Δ (⟨absTy fileName A, true⟩ :: Γ) (.var 0) (.val A) :=
  .absUnseal hP (.var (.here hΓ))

/-- Inside `File`'s provider a `File` is its `Tok`. -/
theorem file_tok_inside {P : Nat → Prop} (hP : P fileName) {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : Ctx.DeadP Γ) : CDerivesIn P Δ (⟨File, true⟩ :: Γ) (.var 0) (.val tokTy) :=
  file_rep_inside hP tokTy hΓ

/-! ### The skip-close destructor, refused as a term -/

/-- The wrong destructor of #775: `λf. u ← burn f; return ()`, which frees the handle's cell and
never performs `close`. -/
def skipCloseB : Expr := bindE (.app burnE (.var 0)) (.val .unit)

/-- **Inside `File`'s provider the wrong destructor types**, at the destructor's type: its one
step at `Tok` is the unseal of `f`. -/
theorem d_skipClose_inside {P : Nat → Prop} (hP : P fileName) {Δ : LifeCtx} (Γ : Ctx VTy)
    (hΓ : Ctx.Dead Γ) :
    CDerivesIn P Δ Γ (.val (.lam skipCloseB)) (.comp (.arr File (CTy.effOf SD .unit))) := by
  refine .lam (.bind (A := .unit) (.left (deadSplit hΓ))
    (.ret (appW (.absUnseal (n := fileName) hP (.var (by csolo))) (.tokBurn (by cdead)))) ?_)
  exact .effSub (RowLe.nil _) (.ret (.unitI (.drop rfl (by cdead))))

/-- `burn`'s body, `free c`. -/
abbrev burnBody : Expr := .app (.val (.prim .free)) (.var 0)

theorem burn_lam {M : Expr} (h : Expr.lam M = burnE) : M = burnBody := by
  cases h; rfl

/-- `free` is read at the views of its axiom's type `Ref A ⊸ A`. -/
theorem der_free {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    e = .val (.prim .free) → ∃ A, ValCls (.lolli (.ref A) A) j := by
  induction h with
  | free => intro _; exact ⟨_, ValCls.refl _⟩
  | thunkV hC _ ih =>
      intro he; obtain ⟨A, hc⟩ := ih he; rw [hc.comp_isRet] at hC; cases hC
  | bangThunkV _ hC _ ih =>
      intro he; obtain ⟨A, hc⟩ := ih he; rw [hc.comp_isRet] at hC; cases hC
  | ret _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.ret _)⟩
  | ofRet _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.ofRet _)⟩
  | effSub hle _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.effSub _ _ _ hle)⟩
  | nuIn hC _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.nuIn _ hC)⟩
  | nuOut hC _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.nuOut _ hC)⟩
  | bangE _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.bang _))⟩
  | boxI _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.boxI _ _))⟩
  | boxE _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.boxE _ _))⟩
  | absSeal _ _ ih =>
      intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.absSeal _ _))⟩
  | absUnseal _ _ ih =>
      intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.absUnseal _ _))⟩
  | immSub _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.immS _ _ _))⟩
  | mutSub _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.mutS _ _ _))⟩
  | roll _ _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.roll _))⟩
  | unroll _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (.val (.unroll _))⟩
  | force => intro he; rcases Inversions.forceE_var he with h | h <;> cases h
  | _ => intro he; cd_terms

/-- `burn`'s body at a dead binder has no derivation: it reads the binder. -/
theorem not_burnBody_dead {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} {j : Jdg}
    (h : CDerives Δ (⟨T, false⟩ :: Γ) burnBody j) : False := by
  obtain ⟨_, hT⟩ := Inversions.fv_live h 0 (by simp [Expr.HasVar, burnBody, Expr.val, Val.prim])
  simp at hT

/-- **`burn` is read at the views of its axiom's type**, or through its body under a live binder
at the type it is read at. -/
theorem der_burn {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    e = burnE → ValCls burnTy j ∨
      ∃ A D, CDerives Δ (⟨A, true⟩ :: Γ) burnBody (.comp D) ∧ LamCls Γ (.arr A D) j := by
  induction h with
  | tokBurn => intro _; exact .inl (ValCls.refl _)
  | lam h => intro he; obtain rfl := burn_lam he; exact .inr ⟨_, _, h, .inl rfl⟩
  | lamDead h => intro he; obtain rfl := burn_lam he; exact (not_burnBody_dead h).elim
  | allI _ _ _ h => intro he; obtain rfl := burn_lam he; exact (not_burnBody_dead h).elim
  | thunkF h => intro he; obtain rfl := burn_lam he; exact (not_burnBody_dead h).elim
  | bangThunkF _ h => intro he; obtain rfl := burn_lam he; exact (not_burnBody_dead h).elim
  | thunkV hC _ ih =>
      intro he
      rcases ih he with hc | ⟨A, D, hB, hc⟩
      · rw [hc.comp_isRet] at hC; cases hC
      · exact .inr ⟨A, D, hB, hc.thunkV hC⟩
  | bangThunkV hp hC _ ih =>
      intro he
      rcases ih he with hc | ⟨A, D, hB, hc⟩
      · rw [hc.comp_isRet] at hC; cases hC
      · exact .inr ⟨A, D, hB, hc.bangThunkV hC hp⟩
  | ret _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.ret _))
      · exact .inr ⟨A, D, hB, hc.step (.ret _) (Inversions.rigid_arr _ _)⟩
  | ofRet _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.ofRet _))
      · exact .inr ⟨A, D, hB, hc.step (.ofRet _) (Inversions.rigid_arr _ _)⟩
  | effSub hle _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.effSub _ _ _ hle))
      · exact .inr ⟨A, D, hB, hc.step (.effSub _ _ _ hle) (Inversions.rigid_arr _ _)⟩
  | nuIn hC _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.nuIn _ hC))
      · exact .inr ⟨A, D, hB, hc.step (.nuIn _ hC) (Inversions.rigid_arr _ _)⟩
  | nuOut hC _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.nuOut _ hC))
      · exact .inr ⟨A, D, hB, hc.step (.nuOut _ hC) (Inversions.rigid_arr _ _)⟩
  | bangE _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.bang _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.bang _)) (Inversions.rigid_arr _ _)⟩
  | boxI _ _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.boxI _ _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.boxI _ _)) (Inversions.rigid_arr _ _)⟩
  | boxE _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.boxE _ _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.boxE _ _)) (Inversions.rigid_arr _ _)⟩
  | absSeal _ _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.absSeal _ _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.absSeal _ _)) (Inversions.rigid_arr _ _)⟩
  | absUnseal _ _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.absUnseal _ _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.absUnseal _ _)) (Inversions.rigid_arr _ _)⟩
  | immSub _ _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.immS _ _ _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.immS _ _ _)) (Inversions.rigid_arr _ _)⟩
  | mutSub _ _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.mutS _ _ _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.mutS _ _ _)) (Inversions.rigid_arr _ _)⟩
  | roll _ _ _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.roll _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.roll _)) (Inversions.rigid_arr _ _)⟩
  | unroll _ ih =>
      intro he; rcases ih he with hc | ⟨A, D, hB, hc⟩
      · exact .inl (hc.step (.val (.unroll _)))
      · exact .inr ⟨A, D, hB, hc.step (.val (.unroll _)) (Inversions.rigid_arr _ _)⟩
  | force => intro he; rcases Inversions.forceE_var he with h | h <;> cases h
  | tokMint => intro he; simp [mintE, burnE] at he
  | reify => intro he; simp [reifyV, rkV, BoCa.BoLo.hndE, burnE, Expr.val, Val.lam] at he
  | _ => intro he; first | cd_terms | simp_all [burnE, Expr.val, Val.lam]

/-- **`burn`'s body takes a reference**: typed under a live binder `c : A`, `free c` reads `c` at a
`Ref X`, a view of `A`. -/
theorem burnBody_ref {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {D : CTy}
    (h : CDerives Δ (⟨A, true⟩ :: Γ) burnBody (.comp D)) : ∃ X, VView A (.ref X) := by
  obtain ⟨j₀, hb, -⟩ := Inversions.der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A', B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i', A', C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A', S, C, hN, -⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨X, hc⟩ := der_free hf rfl
    have := Inversions.vview_thunk hc
    simp only [CTy.arr.injEq, CTy.ret.injEq] at this
    obtain ⟨rfl, -⟩ := this
    exact ⟨X, (Inversions.varCls_of_le rfl (Inversions.splitP_le_left hs) hY).val⟩
  · obtain ⟨X, S, Y, he, -⟩ := der_free hf rfl
    exact absurd he.symm (Inversions.effOf_ne_arr _ _ _ _)
  · cases hN
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX, -, -⟩ <;> cases hX

/-- `File`'s head, abstract types stripped, is `Tok`. -/
theorem hnf_file : Hnf File tokTy := .abs (Inversions.hnf_self (T := tokTy) (fun _ _ h => by cases h) (fun _ h => by cases h))

/-- A type whose head is `Tok` has no view at a reference. -/
theorem tok_not_ref {A X : VTy} (hA : Hnf A tokTy) (hv : VView A (.ref X)) : False := by
  have := (hv.hnf_of hA (fun _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ _ h => by cases h)).eq_self (fun _ _ h => by cases h) (fun _ h => by cases h)
  cases this

/-- A slot of a context below `f : File, Γ`, live where a term reads it, is `f`. -/
theorem slot_file {P : Nat → Prop} {Δ : LifeCtx} {Γ Γ' : Ctx VTy} {j : Jdg}
    (hle : CtxLe Γ' (⟨File, true⟩ :: Γ)) (h : CDerivesIn P Δ Γ' (.var 0) j) :
    Γ'[0]? = some ⟨File, true⟩ := by
  obtain ⟨T, hT⟩ := Inversions.fv_live h.toCDerives 0 rfl
  have := hle 0 T hT
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
  subst this; exact hT

/-- **Outside `File`'s provider, `burn f` has no derivation** at a context below `f : File`.
Each rule that types an application reads `f` at a type whose head is over `File`
(`var_abs_hnf`), so with `File`'s head `Tok` (`Over.hnf`); and `burn` takes only a `Tok`, or a
`Ref` through its body (`der_burn`, `burnBody_ref`). -/
theorem not_burnFile {P : Nat → Prop} (hP : ¬ P fileName) {Δ : LifeCtx} {Γ Γ₁ : Ctx VTy}
    {j : Jdg} (hle : CtxLe Γ₁ (⟨File, true⟩ :: Γ)) (h : CDerivesIn P Δ Γ₁ (.app burnE (.var 0)) j) :
    False := by
  obtain ⟨j₀, hb, -⟩ := Inversions.der_app h _ _ rfl
  rcases hb with ⟨Γa, Γb, A, B, hs, hY, hf, -⟩ | ⟨Γa, Γb, i, A, C, hi, hs, hf, hx, -⟩ |
    ⟨N, Γa, Γb, A, S, C, hN, hs, hY, hN', -⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · -- `⊸E`: `f` at `A`, `burn` at `A ⊸ B`
    have hslot := slot_file ((Inversions.splitP_le_left hs).trans hle) hY
    obtain ⟨k, hk, ho⟩ := hY.var_abs_hnf hP rfl ⟨[], .inl rfl⟩ hslot
    rcases der_burn hf.toCDerives rfl with hc | ⟨A', D, hB, hc⟩
    · have := Inversions.vview_thunk hc
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      obtain ⟨m, B', rfl⟩ := ho.isAbs
      cases hk.eq_self
    · have := hc.val_thunk
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      obtain ⟨X, hv⟩ := burnBody_ref hB
      exact tok_not_ref (ho.hnf (Inversions.hnf_self (T := tokTy) (fun _ _ h => by cases h) (fun _ h => by cases h)) hk) hv
  · -- `[app]`: `f`'s slot at `A`, `burn` at `A ⊸ C`
    cases hi
    have hA : A = File := by
      have := hle 0 A ((Inversions.splitP_le_right hs) 0 A (Ctx.SoloP.getElem? hx))
      simpa using this.symm
    subst hA
    rcases der_burn hf.toCDerives rfl with hc | ⟨A', D, hB, hc⟩
    · obtain ⟨S, Y, he, -⟩ := hc
      exact absurd he.symm (Inversions.effOf_ne_arr _ _ _ _)
    · have := hc.comp_rigid (Inversions.rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      obtain ⟨X, hv⟩ := burnBody_ref hB
      exact tok_not_ref hnf_file hv
  · -- `[let]`: `f` at a row over `A`, `burn`'s body under `c : A`
    obtain rfl := burn_lam hN.symm
    have hslot := slot_file ((Inversions.splitP_le_left hs).trans hle) hY
    obtain ⟨k, hk, ho⟩ := hY.var_abs_hnf hP rfl ⟨S, .inr rfl⟩ hslot
    obtain ⟨X, hv⟩ := burnBody_ref hN'.toCDerives
    exact tok_not_ref (ho.hnf (Inversions.hnf_self (T := tokTy) (fun _ _ h => by cases h) (fun _ h => by cases h)) hk) hv
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX, -, -⟩ <;> cases hX

/-- **The skip-close destructor is refused as a term outside `File`'s provider**: `λf. burn f; ()`
has no derivation at any type `File ⊸ C`, so none at the destructor's type `File ⊸ F_{close} 1`.
This rules out the wrong implementation of #775: a client that disposes of a `File` by freeing
its cell instead of closing it does not type. Inside the provider it does
(`d_skipClose_inside`).  `[spec §63]` -/
theorem not_skipClose {P : Nat → Prop} (hP : ¬ P fileName) {Δ : LifeCtx} {Γ : Ctx VTy}
    {C : CTy} : ¬ CDerivesIn P Δ Γ (.val (.lam skipCloseB)) (.comp (.arr File C)) := by
  intro h
  rcases Inversions.der_lam h skipCloseB rfl with ⟨A, D, hM, hc⟩ | ⟨S, B, hM, hc⟩ |
    ⟨x, b, Δ', S, C', hM, hc⟩ | ⟨A, hM, hc⟩ | ⟨M₁, M₂, hw⟩ | hx
  · have := hc.comp_rigid (Inversions.rigid_arr _ _)
    simp only [CTy.arr.injEq] at this
    obtain ⟨rfl, -⟩ := this
    -- `λu. return ()` is `forget`: the body is read as an application, its argument `burn f`
    obtain ⟨j₀, hb, -⟩ := Inversions.der_app hM _ _ rfl
    rcases hb with ⟨Γa, Γb, A, B, hs, hY, -, -⟩ | ⟨-, -, i, -, -, hi, -⟩ |
      ⟨N, Γa, Γb, A, S, C, -, hs, hY, -, -⟩ | ⟨N, b, C, -, hb, -⟩ |
      ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
    · exact not_burnFile hP (Inversions.splitP_le_left hs) hY
    · cases hi
    · exact not_burnFile hP (Inversions.splitP_le_left hs) hY
    · cases hb
    · cases hu
    · cases hu
    · cases hu
    · cases hu
    · cases hu
    · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX, -, -⟩ <;> cases hX
  · have := hc.comp_rigid (Inversions.rigid_arr _ _); cases this
  · have := hc.comp_rigid (Inversions.rigid_arr _ _); cases this
  · rcases hc with ⟨S, Y, he, -⟩ | ⟨-, S, Y, he, -⟩ <;>
      exact absurd he.symm (Inversions.effOf_ne_arr _ _ _ _)
  · simp [withPair, skipCloseB, bindE, Expr.val, Val.lam] at hw
  · exact Inversions.NotConst.notAx (by unfold skipCloseB; not_const) _ hx

/-- **At `Outside`, the skip-close destructor is refused**: no checked program types it.
`[spec §63]` -/
theorem not_skipClose_outside {Δ : LifeCtx} {Γ : Ctx VTy} :
    ¬ CDerivesIn Outside Δ Γ (.val (.lam skipCloseB)) (.comp (.arr File (CTy.effOf SD .unit))) :=
  not_skipClose id

/-! ### A client outside every provider, at every representation

`Fs`'s operations at a file of representation `A`: `close : abs fileName A ↠^lin 1` and
`open : I32 ↠^lin abs fileName A`. At `A = Tok` they are `fcloseSig` and `fopenSig`. -/

/-- `close` at the representation `A`. -/
def fcloseSigR (A : VTy) : OpSig := ⟨4, 0, .lin, absTy fileName A, .unit, .ret .unit, false⟩

/-- `open` at the representation `A`. -/
def fopenSigR (A : VTy) : OpSig := ⟨4, 1, .lin, I32, absTy fileName A, .ret .unit, false⟩

/-- `{close, open}` at the representation `A`. -/
abbrev SOR (A : VTy) : Row := [fcloseSigR A, fopenSigR A]

theorem SOR_not_cancels (A : VTy) : ¬ (SOR A).Cancels := by
  rintro ⟨o, ho, hq⟩
  simp only [SOR, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact hq rfl

/-- `f ← open 1; close f`: a client of `File` through `Fs`'s operations alone. -/
def openClose : Expr := bindE (openE 1) closeB

/-- **The client is typed at every provider set and every representation**, `Outside` among
them: it takes no file apart.  `[spec §63]` -/
theorem d_openCloseR {P : Nat → Prop} (A : VTy) {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : Ctx.Dead Γ) : CDerivesIn P Δ Γ openClose (.comp (CTy.effOf (SOR A) .unit)) :=
  .effLet (A := absTy fileName A) (deadSplit hΓ) (fun h => absurd h (SOR_not_cancels A))
    (fun h => absurd h (Row.not_unr_of_not_cancels (SOR_not_cancels A)))
    (.effPerform (o := fopenSigR A) rfl rfl rfl (.lit (.i32 1) hΓ.toP))
    (.effPerform (o := fcloseSigR A) rfl rfl rfl (.var (.here hΓ.toP)))

/-- **The client is typed at every provider set**, `Outside` among them. -/
theorem d_openClose {P : Nat → Prop} {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesIn P Δ Γ openClose (.comp (CTy.effOf SO .unit)) :=
  d_openCloseR tokTy hΓ

/-- `with_fs (f ← open 1; close f)`: the client linked under `File`'s provider. -/
def fsOpenClose : Expr := withFs openClose

/-- **The linked program is a `CDerives` derivation**: the provider `with_fs` typed inside every
provider, the client outside every provider, embedded by `CDerivesIn.mono`. -/
theorem d_fsOpenClose : CDerives LifeCtx.empty [] fsOpenClose (.comp (.ret .unit)) := by
  refine d_withFsG (S := []) (A := .unit) (by simp) rfl ?_
  rw [ofEff_Efs_nil]
  exact (d_openClose (P := Outside) (.cons (.cons .nil))).toCDerives

/-- **The linked program is resource safe**: every run ends at the empty memory and none is
stuck. This is the provider's soundness, not encapsulation: the relation cannot tell `File` from
`Tok`, and a client that burned the file would be as safe. -/
theorem fsOpenClose_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem fsOpenClose μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_fsOpenClose hs

/-! ### A file at the representation `Ref I32`, provided by externs

`fileC = abs fileName (Ref I32)`: a location owning a cell that holds the descriptor. Its provider
is two externs, values in the program's context at `!U C` (SPEC §11): `open : I32 ⊸ F fileC`,
whose model `λx. alloc x` puts the descriptor in a fresh cell, and `close : fileC ⊸ F I32`, whose
model `λc. free c` frees it and answers the descriptor. Each model is typed at `Ref I32` and meets
its contract at `fileC` because the two relations are equal (`vCE_abs_eq_rep`), the identity that
is `absSeal`'s and `absUnseal`'s compatibility lemma. The client is typed at every provider set.

The kernel does not decide which externs are `fileC`'s provider: an extern `fileC ⊸ F (Ref I32)`
with the identity for its model meets its contract by the same equality. Which externs may
mention `abs fileName` is the trusted extern table's obligation (SPEC §63). -/

/-- A file represented by an owned cell holding its descriptor. -/
abbrev fileC : VTy := absTy fileName (.ref I32)

/-- `open`'s type at the representation `R`: `I32 ⊸ F R`. -/
def openXC (R : VTy) : CTy := .arr I32 (.ret R)

/-- `close`'s type at the representation `R`: `R ⊸ F I32`. -/
def closeXC (R : VTy) : CTy := .arr R (.ret I32)

/-- The externs' context: `open`, then `close`. -/
abbrev Γx : Ctx VTy := [⟨externTy (openXC fileC), true⟩, ⟨externTy (closeXC fileC), true⟩]

theorem d_openXModel :
    CDerives LifeCtx.empty [] (.val mkInputV) (.comp (openXC (.ref I32))) :=
  .lam (.ret (appP (.var (by csoloP)) (.alloc (by cdeadP))))

theorem d_closeXModel :
    CDerives LifeCtx.empty [] (.val takeCapV) (.comp (closeXC (.ref I32))) :=
  .lam (.ret (appP (.var (by csoloP)) (.free (by cdeadP))))

theorem cC_openXC : cC (openXC (.ref I32)) = cC (openXC fileC) := by
  funext ls δ e ρ
  rfl

theorem cC_closeXC : cC (closeXC (.ref I32)) = cC (closeXC fileC) := by
  funext ls δ e ρ
  rfl

/-- **`open`'s model meets its contract at `fileC`.**  `[spec §63]` -/
theorem openX_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (openXC fileC)) ls δ mkInputV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_openXC]
  exact meets_of_derives rfl d_openXModel ls δ

/-- **`close`'s model meets its contract at `fileC`.**  `[spec §63]` -/
theorem closeX_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (closeXC fileC)) ls δ takeCapV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_closeXC]
  exact meets_of_derives rfl d_closeXModel ls δ

theorem externsX_meet : ExternsMeet Γx [mkInputV, takeCapV] :=
  .cons rfl openX_meets (.cons rfl closeX_meets .nil)

/-- `o ← return open; n ← return 1; f ← o n; c ← return close; c f`. -/
def openCloseX : Expr :=
  bindE (.var 0)
    (bindE (.val (Val.i32 1))
      (bindE (.app (.var 1) (.var 0))
        (bindE (.var 4) (.app (.var 0) (.var 1)))))

/-- **The client is typed at every provider set**, `Outside` among them: it opens and closes a
`fileC` through the externs alone.  `[spec §63]` -/
theorem d_openCloseX {P : Nat → Prop} {Δ : LifeCtx} :
    CDerivesIn P Δ Γx openCloseX (.comp (.ret I32)) := by
  have pO : (externTy (openXC fileC)).Persistent := rfl
  have pC : (externTy (closeXC fileC)).Persistent := rfl
  refine .bind (A := .thunk (openXC fileC)) (.dup pO (.dup pC .nil))
    (.ret (.bangE (.var (.here (.drop pC .nil))))) ?_
  refine .bind (A := I32) (.right (.dup pO (.dup pC .nil)))
    (.ret (.lit (.i32 1) (.cons (.drop pO (.drop pC .nil))))) ?_
  refine .bind (A := fileC) (.left (.left (.dup pO (.dup pC .nil))))
    (.app (.right (.left (.dup pO (.dup pC .nil))))
      (.force (C := openXC fileC) (.there (.here (.drop pO (.drop pC .nil)))))
      (.here (.cons (.drop pO (.drop pC .nil))))) ?_
  refine .bind (A := .thunk (closeXC fileC)) (.right (.dead (.dead (.dup pO (.dup pC .nil)))))
    (.ret (.bangE (.var (.there (.there (.there (.skip pO (.here .nil)))))))) ?_
  exact .app (.left (.right (.dead (.dead (.dup pO (.dup pC .nil))))))
    (.force (C := closeXC fileC) (.here (.cons (.cons (.cons (.drop pO (.drop pC .nil)))))))
    (.there (.here (.cons (.cons (.drop pO (.drop pC .nil))))))

/-- **Linked with the externs' models, every run ends at the empty memory**: from the empty
memory, under every allocator, every run continues to an `I32` at the empty memory, the file's
cell freed.  `[spec §63]` -/
theorem openCloseX_runs {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (substAll [mkInputV, takeCapV] openCloseX) μ₁ e₁) :
    ∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true I32 ls δ v PMap.empty := by
  have hwp := fundamentalC (d_openCloseX (P := fun _ => True) (Δ := LifeCtx.empty)) LSub.empty
    [mkInputV, takeCapV] [] PMap.empty Adequacy.models_empty
    (gDenC_of_meets externsX_meet [] LSub.empty)
  have hwp' : wpTS [] (substAll [mkInputV, takeCapV] openCloseX)
      (fun _ v => Fig16.BoLo.pure (∃ ls δ, vC true I32 ls δ v PMap.empty)) PMap.empty := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty hwp
    obtain rfl := vP_empty_of_persistent (A := I32) rfl hv
    exact ⟨rfl, ls, LSub.empty, hv⟩
  exact theorem32D _ _ hwp' hs

end BoCa.Fig16.LogRel.Core

end
