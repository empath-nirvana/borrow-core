import Core.LetDtorFiles
import Core.Inversions

/-!
# Core — abstract types and their provider  `[spec §63]`

An abstract type `abs n` (`Opaque.abs`) is represented by `Tok` and has `Tok`'s relation. The
judgment `CDerivesIn P` is indexed by a provider set `P`: `P n` when the derivation is inside the
provider of `n`. Two rules read `P`, the iso between `abs n` and its representation:

    absSeal   (hn : P n) : CDerivesIn P Δ Γ e (.val Tok)     → CDerivesIn P Δ Γ e (.val (abs n))
    absUnseal (hn : P n) : CDerivesIn P Δ Γ e (.val (abs n)) → CDerivesIn P Δ Γ e (.val Tok)

`CDerives` is `CDerivesIn` inside every provider, so every theorem about `CDerives` reads as
before, and `CDerivesIn.mono` embeds a derivation at any provider set into it: `fundamentalC`,
`adequacyC` and `resourceSafety` hold of every client.

* `CDerivesIn.outside`: **encapsulation.** A derivation at a provider set that excludes `n` is a
  derivation at `ProvWithout P n`, where the seal and the unseal at `n` have no instance
  (`ProvWithout.not_self`): it contains no seal or unseal at `n`.
* `CDerivesIn.var_abs_hnf`, `CDerivesIn.var_abs_not_tok`: **the unseal step refused.** Outside
  `n`'s provider, a variable of type `abs n` is read only at types whose head is `abs n` (boxes
  stripped, `μ` unrolled): never at `Tok`, which `burn` takes, nor at any other type a constant
  consumes.
* `file_not_tok_outside`: at `File`, outside `with_fs`. A `File` reaches `burn` only through the
  unseal, so a destructor that burns a `File` instead of closing it does not type outside `Fs`'s
  provider; inside it, it does (`d_skipClose_inside`).
* `d_openClose`: a client at every provider set, `Outside` among them, that opens a file and closes
  it through `Fs`'s operations; `fsOpenClose_safe`: linked under `with_fs`, it is resource safe.

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
open BoCa.Lifetime (LifeCtx)
open BoCa.Fig16.LogRel.Core.LetDtor.Files

/-! ### Provider sets -/

/-- **The provider set outside every provider**: a client of every abstract type. -/
abbrev Outside : Nat → Prop := fun _ => False

/-- `P` without the name `n`. -/
def ProvWithout (P : Nat → Prop) (n : Nat) : Nat → Prop := fun m => P m ∧ m ≠ n

/-- **At `P` without `n`, the seal and the unseal at `n` have no instance**: their premise is
`ProvWithout P n n`, which is false. -/
theorem ProvWithout.not_self (P : Nat → Prop) (n : Nat) : ¬ ProvWithout P n n := fun h => h.2 rfl

/-! ### Encapsulation -/

/-- **Encapsulation**: a derivation at a provider set that excludes `n` is a derivation at `P`
without `n`, whose seal and unseal at `n` have no instance (`ProvWithout.not_self`). So it holds
no seal or unseal at `n`: outside `n`'s provider, a value of `abs n` is never taken to its
representation, nor made from one.  `[spec §63]` -/
theorem CDerivesIn.outside {P : Nat → Prop} {n : Nat} (hn : ¬ P n) {Δ : LifeCtx}
    {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) :
    CDerivesIn (ProvWithout P n) Δ Γ e j :=
  h.mono fun m hm => ⟨hm, fun e => hn (e ▸ hm)⟩

/-! ### The unseal step refused -/

theorem Ctx.SoloP.getElem? {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    Γ[i]? = some ⟨A, true⟩ := by
  induction h with
  | here => rfl
  | there _ ih => exact ih
  | skip _ _ ih => exact ih

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

/-- **Outside its provider, a variable of an abstract type is read at that type alone**: at every
judgment that reads it at a value type `A`, `A`'s head (`Hnf`: boxes stripped, `μ` unrolled) is
`abs n`. No rule takes it to its representation `Tok`, nor to any type a constant consumes. The
rules that read a variable at another judgment are `var`, `force`, the `!`, `[]`, `μ`, `ν`, `F`
and borrow-weakening rules, and the provider's two; at `¬ P n` the unseal at `n` has no
instance.  `[spec §63]` -/
theorem CDerivesIn.var_abs_hnf {P : Nat → Prop} {n : Nat} (hn : ¬ P n) {Δ : LifeCtx}
    {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) :
    ∀ {i : Nat} {A : VTy}, e = .var i → j.AtVal A → Γ[i]? = some ⟨absTy n, true⟩ →
      Inversions.Hnf A (absTy n) := by
  induction h with
  | var hs =>
      intro i A he hj hΓ
      cases he
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        rw [hs.getElem?] at hΓ
        cases hΓ
        exact .base (fun _ _ h => by cases h) (fun _ h => by cases h)
      · cases hj
  | force hs =>
      intro i A he hj hΓ
      rename_i C
      cases C <;> simp only [forceE] at he <;> (try cases he) <;>
        (rw [hs.getElem?] at hΓ; cases hΓ)
  | ret _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · have hA := CTy.effOf_inj_right (S := []) (Jdg.comp.inj hj)
        subst hA
        exact ih he ⟨[], .inl rfl⟩ hΓ
  | ofRet _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj; exact ih he ⟨[], .inr rfl⟩ hΓ
      · cases hj
  | effSub _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · rw [← CTy.effOf_inj_right (Jdg.comp.inj hj)]
        exact ih he ⟨_, .inr rfl⟩ hΓ
  | nuIn _ _ _ =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · exact absurd (Jdg.comp.inj hj).symm (Inversions.effOf_ne_nu _ _ _)
  | nuOut hC _ _ =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
      · obtain ⟨C₁, C₂, hu⟩ := Inversions.unroll_amp hC
        have hj := Jdg.comp.inj hj
        rw [hu] at hj
        exact absurd hj.symm (Inversions.effOf_ne_amp _ _ _ _)
  | bangE _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        have h' := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
      · cases hj
  | boxI _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj; exact .box (ih he ⟨[], .inl rfl⟩ hΓ)
      · cases hj
  | boxE _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        have h' := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | box h' => exact h'
      · cases hj
  | immSub _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        have h' := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
      · cases hj
  | mutSub _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        have h' := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
      · cases hj
  | roll _ _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj; exact .mu (ih he ⟨[], .inl rfl⟩ hΓ)
      · cases hj
  | unroll _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        have h' := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | mu h' => exact h'
      · cases hj
  | absSeal _ _ ih =>
      intro i A he hj hΓ
      have h' := ih he ⟨[], .inl rfl⟩ hΓ
      cases h'
  | @absUnseal _ _ _ m hm _ ih =>
      intro i A he hj hΓ
      have h' := ih he ⟨[], .inl rfl⟩ hΓ
      cases h'
      exact absurd hm hn
  | _ => intro i A he hj _; first | cases he | (obtain ⟨S, hj | hj⟩ := hj <;> cases hj) | simp_all

/-- **Outside its provider, a variable of an abstract type is never a `Tok`**: the unseal step
has no instance, so `burn`, which takes a `Tok`, does not take it.  `[spec §63]` -/
theorem CDerivesIn.var_abs_not_tok {P : Nat → Prop} {n : Nat} (hn : ¬ P n) {Δ : LifeCtx}
    {Γ : Ctx VTy} {i : Nat} (hΓ : Γ[i]? = some ⟨absTy n, true⟩) :
    ¬ CDerivesIn P Δ Γ (.var i) (.val tokTy) := fun h => by
  have h' := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  cases h'

/-! ### `File` outside and inside `with_fs` -/

/-- **Outside `File`'s provider a `File` is never a `Tok`.**  `[spec §63]` -/
theorem file_not_tok_outside {Δ : LifeCtx} {Γ : Ctx VTy} :
    ¬ CDerivesIn Outside Δ (⟨File, true⟩ :: Γ) (.var 0) (.val tokTy) :=
  CDerivesIn.var_abs_not_tok (n := fileName) id rfl

/-- Inside `File`'s provider a `File` is its `Tok`. -/
theorem file_tok_inside {P : Nat → Prop} (hP : P fileName) {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : Ctx.DeadP Γ) : CDerivesIn P Δ (⟨File, true⟩ :: Γ) (.var 0) (.val tokTy) :=
  .absUnseal hP (.var (.here hΓ))

/-- The wrong destructor of #775: `λf. u ← burn f; return ()`, which frees the handle's cell and
never performs `close`. -/
def skipCloseB : Expr := bindE (.app burnE (.var 0)) (.val .unit)

/-- **Inside `File`'s provider the wrong destructor types**, at the destructor's type: its one
step at `Tok` is the unseal of `f`. Outside, that step is refused (`file_not_tok_outside`). -/
theorem d_skipClose_inside {P : Nat → Prop} (hP : P fileName) {Δ : LifeCtx} (Γ : Ctx VTy)
    (hΓ : Ctx.Dead Γ) :
    CDerivesIn P Δ Γ (.val (.lam skipCloseB)) (.comp (.arr File (CTy.effOf SD .unit))) := by
  refine .lam (.bind (A := .unit) (.left (deadSplit hΓ))
    (.ret (appW (.absUnseal (n := fileName) hP (.var (by csolo))) (.tokBurn (by cdead)))) ?_)
  exact .effSub (RowLe.nil _) (.ret (.unitI (.drop rfl (by cdead))))

/-! ### A client outside every provider -/

/-- `f ← open 1; close f`: a client of `File` through `Fs`'s operations alone. -/
def openClose : Expr := bindE (openE 1) closeB

/-- **The client is typed at every provider set**, `Outside` among them: it takes no `File`
apart.  `[spec §63]` -/
theorem d_openClose {P : Nat → Prop} {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesIn P Δ Γ openClose (.comp (CTy.effOf SO .unit)) :=
  .effLet (A := File) (deadSplit hΓ) (fun h => absurd h SO_not_cancels)
    (fun h => absurd h SO_not_unr)
    (.effPerform (o := fopenSig) rfl rfl rfl (.lit (.i32 1) hΓ.toP))
    (.effPerform (o := fcloseSig) rfl rfl rfl (.var (.here hΓ.toP)))

/-- `with_fs (f ← open 1; close f)`: the client linked under `File`'s provider. -/
def fsOpenClose : Expr := withFs openClose

/-- **The linked program is a `CDerives` derivation**: the provider `with_fs` typed inside every
provider, the client outside every provider, embedded by `CDerivesIn.mono`. -/
theorem d_fsOpenClose : CDerives LifeCtx.empty [] fsOpenClose (.comp (.ret .unit)) := by
  refine d_withFsG (S := []) (A := .unit) (by simp) rfl ?_
  rw [ofEff_Efs_nil]
  exact (d_openClose (P := Outside) (.cons (.cons .nil))).toCDerives

/-- **The linked program is resource safe**: every run ends at the empty memory and none is
stuck. -/
theorem fsOpenClose_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem fsOpenClose μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_fsOpenClose hs

/-- **The encapsulation statement's premises hold**: the client's derivation is at a provider
set that excludes `File`'s name, and so at `Outside` without it. -/
theorem openClose_outside {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesIn (ProvWithout Outside fileName) Δ Γ openClose (.comp (CTy.effOf SO .unit)) :=
  (d_openClose (P := Outside) hΓ).outside id

end BoCa.Fig16.LogRel.Core

end
