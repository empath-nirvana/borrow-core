import Core.LetDtorFiles
import Core.Inversions
import Core.Stdio

/-!
# Core — abstract types and their provider  `[spec §63]`

An abstract type `abs n rep` (`Opaque.abs`) is named `n` and represented by the opaque type `rep`,
whose relation it has (`Opaque.rel_abs`). The judgment `CDerivesIn P` is indexed by a provider set
`P`: `P n` when the derivation is inside the provider of `n`. Two rules read `P`, the iso between
`abs n rep` and its representation:

    absSeal   (hn : P n) : CDerivesIn P Δ Γ e (.val rep)         → CDerivesIn P Δ Γ e (.val (abs n rep))
    absUnseal (hn : P n) : CDerivesIn P Δ Γ e (.val (abs n rep)) → CDerivesIn P Δ Γ e (.val rep)

`CDerives` is `CDerivesIn` inside every provider, so every theorem about `CDerives` reads as
before, and `CDerivesIn.mono` embeds a derivation at any provider set into it: `fundamentalC`,
`adequacyC` and `resourceSafety` hold of every client. Every theorem below is stated at every
representation.

* `CDerivesIn.outside`: **encapsulation.** A derivation at a provider set that excludes `n` is a
  derivation at `ProvWithout P n`, where the seal and the unseal at `n` have no instance
  (`ProvWithout.not_self`): it contains no seal or unseal at `n`.
* `CDerivesIn.var_abs_hnf`: **the unseal step refused.** Outside `n`'s provider, a variable of type
  `abs n rep` is read only at types whose head (boxes stripped, `μ` unrolled) is `abs n rep` under
  abstract types of `P` (`Opaque.Over`): it may be sealed again into a type whose provider `P` is
  in, never taken to `rep`. `CDerivesIn.var_abs_not_rep`: never at `rep`;
  `CDerivesIn.var_abs_not_tok`: never at `Tok`, which `burn` takes. At a provider set with no name
  (`Outside`, every checked program's), the head is `abs n rep` itself (`var_abs_hnf_none`).
* `file_not_tok_outside`, `file_not_rep_outside`: at `File`, outside its provider. A `File` reaches
  `burn` only through the unseal, so a destructor that burns a `File` instead of closing it does not
  type outside `Fs`'s provider; inside it, it does (`d_skipClose_inside`).
* **Non-vacuity at two representations.** At `Tok` (`File`): `d_openClose`, a client at every
  provider set, `Outside` among them, that opens a file and closes it through `Fs`'s operations;
  `fsOpenClose_safe`: linked under `with_fs`, it is resource safe. At `Cell`, an owned cell holding
  an `I32` (`fileC`): the provider is two externs, `open : I32 ⊸ F File` and
  `close : File ⊸ F I32`, whose models allocate and free the cell and meet their contracts at
  `abs fileName Cell` by the relation's equality (`openX_meets`, `closeX_meets`); the client
  `f ← open 1; close f` is typed at every provider set (`d_openCloseX`, `openCloseX_outside`), and
  run with the models every run ends at the empty memory (`openCloseX_runs`).

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

/-- `k` is `a` under abstract types whose names are in `P`: `a`, or `abs m k'` with `P m` and `k'`
such. Inside `m`'s provider, a value of `k'` may be sealed into `abs m k'`. -/
inductive Opaque.Over (P : Nat → Prop) (a : Opaque) : Opaque → Prop
  | refl : Opaque.Over P a a
  | abs {m : Nat} {k : Opaque} : P m → Opaque.Over P a k → Opaque.Over P a (.abs m k)

theorem Opaque.Over.sizeOf_le {P : Nat → Prop} {a k : Opaque} (h : Opaque.Over P a k) :
    sizeOf a ≤ sizeOf k := by
  induction h with
  | refl => exact Nat.le_refl _
  | abs _ _ ih => simp only [Opaque.abs.sizeOf_spec]; omega

/-- **The representation is not over its abstract type.** -/
theorem Opaque.Over.not_rep {P : Nat → Prop} {n : Nat} {rep : Opaque}
    (h : Opaque.Over P (.abs n rep) rep) : False := by
  have := h.sizeOf_le
  simp only [Opaque.abs.sizeOf_spec] at this
  omega

/-- At a provider set with no name, `k` over `a` is `a`. -/
theorem Opaque.Over.eq_of_none {P : Nat → Prop} (hP : ∀ m, ¬ P m) {a k : Opaque}
    (h : Opaque.Over P a k) : k = a := by
  cases h with
  | refl => rfl
  | abs hm _ => exact absurd hm (hP _)

/-- **Outside its provider, a variable of an abstract type is read at that type alone**, up to
seals the derivation's provider set allows: at every judgment that reads it at a value type `A`,
`A`'s head (`Hnf`: boxes stripped, `μ` unrolled) is an opaque type over `abs n rep` by abstract
types of `P` (`Opaque.Over`). No rule takes it to its representation `rep`, nor to any type a
constant consumes. The rules that read a variable at another judgment are `var`, `force`, the
`!`, `[]`, `μ`, `ν`, `F` and borrow-weakening rules, and the provider's two; at `¬ P n` the unseal
at `n` has no instance, and an unseal at another name `m` takes off only a seal at `m`.
`[spec §63]` -/
theorem CDerivesIn.var_abs_hnf {P : Nat → Prop} {n : Nat} {rep : Opaque} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) :
    ∀ {i : Nat} {A : VTy}, e = .var i → j.AtVal A → Γ[i]? = some ⟨absTy n rep, true⟩ →
      ∃ k, Inversions.Hnf A (.opq k) ∧ Opaque.Over P (.abs n rep) k := by
  induction h with
  | var hs =>
      intro i A he hj hΓ
      cases he
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        rw [hs.getElem?] at hΓ
        cases hΓ
        exact ⟨_, .base (fun _ _ h => by cases h) (fun _ h => by cases h), .refl⟩
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
        obtain ⟨k, h', -⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
      · cases hj
  | boxI _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨k, .box h', ho⟩
      · cases hj
  | boxE _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | box h' => exact ⟨k, h', ho⟩
      · cases hj
  | immSub _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', -⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
      · cases hj
  | mutSub _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', -⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
      · cases hj
  | roll _ _ _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        exact ⟨k, .mu h', ho⟩
      · cases hj
  | unroll _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h' with
        | mu h' => exact ⟨k, h', ho⟩
      · cases hj
  | @absSeal _ _ _ m r hm _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
        exact ⟨_, .base (fun _ _ h => by cases h) (fun _ h => by cases h), .abs hm ho⟩
      · cases hj
  | @absUnseal _ _ _ m r hm _ ih =>
      intro i A he hj hΓ
      obtain ⟨S, hj | hj⟩ := hj
      · cases hj
        obtain ⟨k, h', ho⟩ := ih he ⟨[], .inl rfl⟩ hΓ
        cases h'
        cases ho with
        | refl => exact absurd hm hn
        | abs _ ho => exact ⟨_, .base (fun _ _ h => by cases h) (fun _ h => by cases h), ho⟩
      · cases hj
  | _ => intro i A he hj _; first | cases he | (obtain ⟨S, hj | hj⟩ := hj <;> cases hj) | simp_all

/-- **At a provider set with no name, the head is the abstract type itself**: no seal or unseal
has an instance.  `[spec §63]` -/
theorem CDerivesIn.var_abs_hnf_none {P : Nat → Prop} (hP : ∀ m, ¬ P m) {n : Nat} {rep : Opaque}
    {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesIn P Δ Γ e j) {i : Nat}
    {A : VTy} (he : e = .var i) (hj : j.AtVal A) (hΓ : Γ[i]? = some ⟨absTy n rep, true⟩) :
    Inversions.Hnf A (absTy n rep) := by
  obtain ⟨k, hk, ho⟩ := h.var_abs_hnf (hP n) he hj hΓ
  rw [ho.eq_of_none hP] at hk
  exact hk

/-- **Outside its provider, a variable of an abstract type is never its representation**: the
unseal step has no instance at `n`.  `[spec §63]` -/
theorem CDerivesIn.var_abs_not_rep {P : Nat → Prop} {n : Nat} {rep : Opaque} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} (hΓ : Γ[i]? = some ⟨absTy n rep, true⟩) :
    ¬ CDerivesIn P Δ Γ (.var i) (.val (.opq rep)) := fun h => by
  obtain ⟨k, h', ho⟩ := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  cases h'
  exact ho.not_rep

/-- **Outside its provider, a variable of an abstract type is never a `Tok`**: `burn`, which
takes a `Tok`, does not take it.  `[spec §63]` -/
theorem CDerivesIn.var_abs_not_tok {P : Nat → Prop} {n : Nat} {rep : Opaque} (hn : ¬ P n)
    {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} (hΓ : Γ[i]? = some ⟨absTy n rep, true⟩) :
    ¬ CDerivesIn P Δ Γ (.var i) (.val tokTy) := fun h => by
  obtain ⟨k, h', ho⟩ := h.var_abs_hnf hn rfl ⟨[], .inl rfl⟩ hΓ
  cases h'
  cases ho

/-! ### `File` outside and inside `with_fs` -/

/-- **Outside `File`'s provider a `File` is never a `Tok`.**  `[spec §63]` -/
theorem file_not_tok_outside {Δ : LifeCtx} {Γ : Ctx VTy} :
    ¬ CDerivesIn Outside Δ (⟨File, true⟩ :: Γ) (.var 0) (.val tokTy) :=
  CDerivesIn.var_abs_not_tok (n := fileName) id rfl

/-- **Outside its provider, a file at any representation is never that representation.**
`[spec §63]` -/
theorem file_not_rep_outside (rep : Opaque) {Δ : LifeCtx} {Γ : Ctx VTy} :
    ¬ CDerivesIn Outside Δ (⟨absTy fileName rep, true⟩ :: Γ) (.var 0) (.val (.opq rep)) :=
  CDerivesIn.var_abs_not_rep (n := fileName) id rfl

/-- Inside its provider a file is its representation. -/
theorem file_rep_inside {P : Nat → Prop} (hP : P fileName) (rep : Opaque) {Δ : LifeCtx}
    {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerivesIn P Δ (⟨absTy fileName rep, true⟩ :: Γ) (.var 0) (.val (.opq rep)) :=
  .absUnseal hP (.var (.here hΓ))

/-- Inside `File`'s provider a `File` is its `Tok`. -/
theorem file_tok_inside {P : Nat → Prop} (hP : P fileName) {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : Ctx.DeadP Γ) : CDerivesIn P Δ (⟨File, true⟩ :: Γ) (.var 0) (.val tokTy) :=
  file_rep_inside hP .tok hΓ

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

/-! ### A client outside every provider, at every representation

`Fs`'s operations at a file of representation `rep`: `close : abs fileName rep ↠^lin 1` and
`open : I32 ↠^lin abs fileName rep`. At `rep = Tok` they are `fcloseSig` and `fopenSig`. -/

/-- `close` at the representation `rep`. -/
def fcloseSigR (rep : Opaque) : OpSig := ⟨4, 0, .lin, absTy fileName rep, .unit, .ret .unit, false⟩

/-- `open` at the representation `rep`. -/
def fopenSigR (rep : Opaque) : OpSig := ⟨4, 1, .lin, I32, absTy fileName rep, .ret .unit, false⟩

/-- `{close, open}` at the representation `rep`. -/
abbrev SOR (rep : Opaque) : Row := [fcloseSigR rep, fopenSigR rep]

theorem SOR_not_cancels (rep : Opaque) : ¬ (SOR rep).Cancels := by
  rintro ⟨o, ho, hq⟩
  simp only [SOR, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact hq rfl

/-- `f ← open 1; close f`: a client of `File` through `Fs`'s operations alone. -/
def openClose : Expr := bindE (openE 1) closeB

/-- **The client is typed at every provider set and every representation**, `Outside` among
them: it takes no file apart.  `[spec §63]` -/
theorem d_openCloseR {P : Nat → Prop} (rep : Opaque) {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : Ctx.Dead Γ) : CDerivesIn P Δ Γ openClose (.comp (CTy.effOf (SOR rep) .unit)) :=
  .effLet (A := absTy fileName rep) (deadSplit hΓ) (fun h => absurd h (SOR_not_cancels rep))
    (fun h => absurd h (Row.not_unr_of_not_cancels (SOR_not_cancels rep)))
    (.effPerform (o := fopenSigR rep) rfl rfl rfl (.lit (.i32 1) hΓ.toP))
    (.effPerform (o := fcloseSigR rep) rfl rfl rfl (.var (.here hΓ.toP)))

/-- **The client is typed at every provider set**, `Outside` among them: it takes no `File`
apart.  `[spec §63]` -/
theorem d_openClose {P : Nat → Prop} {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesIn P Δ Γ openClose (.comp (CTy.effOf SO .unit)) :=
  d_openCloseR .tok hΓ

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

/-- **The encapsulation statement's premises hold, at every representation**: the client's
derivation is at a provider set that excludes `File`'s name, and so at `Outside` without it. -/
theorem openCloseR_outside (rep : Opaque) {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesIn (ProvWithout Outside fileName) Δ Γ openClose
      (.comp (CTy.effOf (SOR rep) .unit)) :=
  (d_openCloseR (P := Outside) rep hΓ).outside id

/-- **The encapsulation statement's premises hold** at `File`. -/
theorem openClose_outside {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesIn (ProvWithout Outside fileName) Δ Γ openClose (.comp (CTy.effOf SO .unit)) :=
  openCloseR_outside .tok hΓ

/-! ### A file at the representation `Cell`, provided by externs

`fileC = abs fileName Cell`: a location owning a cell that holds the descriptor, `Ref I32`'s
relation (`vCE_cell_eq_ref`). Its provider is two externs, values in the program's context at
`!U C` (SPEC §11): `open : I32 ⊸ F fileC`, whose model `λx. alloc x` puts the descriptor in a
fresh cell, and `close : fileC ⊸ F I32`, whose model `λc. free c` frees it and answers the
descriptor. Each model is typed at `Ref I32` and meets its contract at `fileC` because the two
relations are equal: the identity that is `absSeal`'s and `absUnseal`'s compatibility lemma
(`absSeal_compatC`). The client is typed at every provider set. -/

/-- A file represented by an owned cell holding its descriptor. -/
abbrev fileC : VTy := absTy fileName .cell

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

/-- **The client is outside `fileC`'s provider**: the encapsulation statement's premises, at the
representation `Cell`. -/
theorem openCloseX_outside {Δ : LifeCtx} :
    CDerivesIn (ProvWithout Outside fileName) Δ Γx openCloseX (.comp (.ret I32)) :=
  (d_openCloseX (P := Outside)).outside id

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
