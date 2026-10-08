import Core.Stdio
import Targets.Base.Typing
import Targets.Base.Machine
import Targets.Base.Runs

/-!
# Base — Core's cancellation and unwinding shapes (RESTRUCTURE §0, base; DESIGN §5 I3)

The shapes of Core's cancel run and unwind on complete runs
(`CancelRun`, `UnwindRun`, `CancelOrder`, `UnwindOrder`, `FinaliserOrder`), and the syntactic
no-interception property (`NoInterception`: typed terms hold no `ccatch`, no `cfin`, no handler
named `0`).  They mention no world.  A's S5 (`Targets/A/Soundness.lean`) is the run-based form at
every instance; these are the Instance's route to it at Core (RESTRUCTURE §4.1).

**`FinaliserOrder` holds at every typing system that meets `NoInterception` and `FinAloneAt`**
(`finaliserOrder_at`, from `cancelOrder_at` and `unwindOrder_at`).  The route:
* **no step creates a handler named `0`** (`hndNamesNZ_steps`), so the frames a cancel tears down
  and its handler stop the cancel only at finaliser frames;
* **a step at a raise is the step of its innermost stopping frame** (`step1_raise`; that frame is
  unique, `innerCatch_unique`), so a cancel or an unwind goes from finaliser frame to finaliser
  frame;
* **run splitting** (`steps_plug_split_end`) runs a fired finaliser alone, and `FinAloneAt` says how
  that run ends; `[cfin-ret]`, `[cfin-raise]` or `1↦` then hand the raise on.

`FinAloneAt FR` is an added hypothesis: a fired finaliser's run alone, in a platform-free run of a
typed closed program, ends at a value or at an uncaught raise of a name in `FR`.  Its source is
SPEC §19's typing of `[then]`'s finaliser.  Its endings are parameterised by what a finaliser may
raise (decision D3): today's kernel types the finaliser at the abortive part of the row
(`D : F_{Σ^abort} 1`), whose names are not the reserved `0`, and `FinaliserOrder` reads that form,
`FinAloneAt (· ≠ 0)`; option A, the target, has a finaliser handle its raises itself,
`FinAloneAt (fun _ => False)`, which gives it (`finAloneAt_mono`, `finaliserOrder_A`).  Its scope
is what typing gives about a finaliser's own run, at a configuration a typed program reaches; it
says nothing about the cancel's or the unwind's trace.  `NoInterception` does not give it.  It is
read platform-free, as its consumers read it.  `FinRowsAt FR` is its half about operations; the
interaction shows that B gives the rest (`Targets/I/Restricted/FinAlone.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  kappaAt kappaCell kappaCBody freeE stuckE
  ccatchE cfinE ubindE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- What a cancel answers at `ccatch`: `()`, or the kept error raised at the canceller. -/
def cancelAnswer : Option Val → Expr
  | none => .val .unit
  | some E => raiseE (.val E)

/-- A cancel run that fires the finalisers `fs`, innermost first: one `ufinC` per finaliser, its
`D ()` run under `cfin` to `cfret`/`cferr`, and at the end `ccatch` answering. -/
inductive CancelRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | caught {μ : Heap} {K : Kont} {Ns : List UInt32} {err : Option Val}
      (hK : K.Catches 0 = false) :
      CancelRun μ (ccatchE (K.plug (raiseE (.val (cancelVal Ns err))))) [] μ (cancelAnswer err)
  | fin {μ μ₁ μ₂ : Heap} {K₀ K : Kont} {Nv Dv : Val} {Ns : List UInt32} {err err' : Option Val}
      {fs : List Expr} {r : Expr} (hK : K.Catches 0 = false)
      (hD : Steps (ℍ := ℍ) μ (cfinE (cancelVal Ns err) (.app (.val Dv) (.val .unit))) μ₁
              (raiseE (.val (cancelVal Ns err'))))
      (hr : CancelRun μ₁ (ccatchE (K₀.plug (raiseE (.val (cancelVal Ns err'))))) fs μ₂ r) :
      CancelRun μ
        (ccatchE (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (cancelVal Ns err)))))))
        (Dv.1 :: fs) μ₂ r

/-- An unwind that fires the finalisers `fs`, innermost first: one `ufin` per finaliser, its
`D (); raise p` run until a raise is pending under a context `Kd` that catches nothing of it,
ending at a raise that the remaining frames do not catch.  If `D` returns, `Kd` is the hole and
the raise is `p`.  If `D` raises its own abortive operation, the raise is that one, and `Kd` holds
the `seq` frame (`_; raise p`, which catches nothing) and `D`'s own frames at the raise; no rule
reduces a raise under a `seq`, so the unwind goes on from `K₀ ∘ Kd`. -/
inductive UnwindRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | out {μ : Heap} {K : Kont} {m j : UInt32} {w : Val} (hK : K.Catches m = false) :
      UnwindRun μ (K.plug (raiseE (.val (opPayload m j w)))) [] μ
        (K.plug (raiseE (.val (opPayload m j w))))
  | fin {μ μ₁ μ₂ : Heap} {K₀ K Kd : Kont} {Nv Dv : Val} {n i m j : UInt32} {v w : Val}
      {fs : List Expr} {r : Expr} (hn : n ≠ 0) (hK : K.Catches n = false)
      (hD : Steps (ℍ := ℍ) μ (.seq (.app (.val Dv) (.val .unit)) (raiseE (.val (opPayload n i v))))
              μ₁ (Kd.plug (raiseE (.val (opPayload m j w)))))
      (hKd : Kd.Catches m = false)
      (hr : UnwindRun μ₁ ((K₀.comp Kd).plug (raiseE (.val (opPayload m j w)))) fs μ₂ r) :
      UnwindRun μ (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (opPayload n i v))))))
        (Dv.1 :: fs) μ₂ r

/-- `K` has no `ccatch` and no `cfin` frame. -/
def _root_.BoCa.BoLo.Kont.NoCtl : Kont → Prop
  | .hole => True
  | .appR f K => (f ≠ .prim .ccatch ∧ ∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoCtl
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCtl

/-- **I3.b, cancel**: in a typed program, every complete run of a continuation's cancel fires the
frozen finalisers once each, innermost first.  (The three administrative steps from
`κ (inj₂ ())` to `cancelOf n H K` are pure; the canceller's context `K₀` takes no part until
`ccatch` answers.) -/
def CancelOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ : Kont) n H K, Kont.NoCtl K →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (.app (kappa n H K) (.val (Val.inj₂ .unit)))) →
    ∀ μ₃ r, Steps (ℍ := ℍ) μ₁ (cancelOf n H K) μ₃ r →
      (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
      CancelRun (ℍ := ℍ) μ₁ (cancelOf n H K) K.fins μ₃ r

/-- **I3.b, unwind**: every complete unwind through frames with no handler fires their finalisers
once each, innermost first. -/
def UnwindOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ K : Kont) n i v, K.hndNames = [] → Kont.NoCtl K → n ≠ 0 →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) →
    ∀ μ₂ (K' : Kont) m j w, K'.Catches m = false →
      Steps (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) μ₂
        (K'.plug (raiseE (.val (opPayload m j w)))) →
      UnwindRun (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) K.fins μ₂
        (K'.plug (raiseE (.val (opPayload m j w))))

/-- **I3.b.** -/
def FinaliserOrder (J : TypingJ) : Prop := CancelOrder (ℍ := ℍ) J ∧ UnwindOrder (ℍ := ℍ) J

/-- `.prim p` occurs in the term. -/
def _root_.BoCa.Expr.HasPrim (p : Prim) : Expr → Prop
  | .prim p' => p' = p
  | .var _ | .unit | .loc _ => False
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HasPrim p ∨ b.HasPrim p
  | .inj₁ a | .inj₂ a | .lam a => a.HasPrim p
  | .case a b c => a.HasPrim p ∨ b.HasPrim p ∨ c.HasPrim p

/-- Every occurrence of `.prim .hnd` is the function of
`.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _)` with `m ≠ 0`. -/
def _root_.BoCa.Expr.HndNamesNZ : Expr → Prop
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) r) => m ≠ 0 ∧ r.HndNamesNZ
  | .prim p => p ≠ .hnd
  | .var _ | .unit | .loc _ => True
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HndNamesNZ ∧ b.HndNamesNZ
  | .inj₁ a | .inj₂ a | .lam a => a.HndNamesNZ
  | .case a b c => a.HndNamesNZ ∧ b.HndNamesNZ ∧ c.HndNamesNZ

/-- **I3.c**: typed terms contain no `ccatch`, no `cfin`, and no handler named `0`. -/
def NoInterception (J : TypingJ) : Prop :=
  ∀ Θ Δ Γ e j, J Θ Δ Γ e j → ¬ e.HasPrim .ccatch ∧ ¬ e.HasPrim .cfin ∧ e.HndNamesNZ

/-! ### Handler names, read at an application -/

/-- An application is `NZ` as a handler of a nonzero literal name, or as an application of `NZ`
terms whose function is not `hnd`. -/
theorem hndNZ_app (f a : Expr) : (Expr.app f a).HndNamesNZ ↔
    (f = .prim .hnd ∧ ∃ m r, a = .pair (.prim (.lit (.i32 m))) r ∧ m ≠ 0 ∧ r.HndNamesNZ) ∨
    (f ≠ .prim .hnd ∧ f.HndNamesNZ ∧ a.HndNamesNZ) := by
  rw [Expr.HndNamesNZ.eq_def]
  split
  · rename_i m r heq
    simp only [Expr.app.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp
  all_goals rename_i heq
  all_goals (try simp only [Expr.app.injEq] at heq)
  all_goals (try (simp at heq))
  obtain ⟨rfl, rfl⟩ := heq
  rename_i hn
  by_cases hf : f = .prim .hnd
  · subst hf
    have ha : ∀ m r, a ≠ .pair (.prim (.lit (.i32 m))) r := fun m r h => hn m r rfl h
    simp only [Expr.HndNamesNZ, ne_eq, not_true_eq_false, false_and, and_false, or_false, true_and,
      false_iff, not_exists, not_and]
    intro m r h; exact absurd h (ha m r)
  · simp [hf]

theorem hndNZ_prim_hnd : ¬ (Expr.prim .hnd).HndNamesNZ := by simp [Expr.HndNamesNZ]

theorem shift_ne_hnd {f : Expr} (hf : f ≠ .prim .hnd) (d c : ℕ) : f.shift d c ≠ .prim .hnd := by
  cases f <;> simp only [Expr.shift] <;> (try split) <;> simp_all

theorem subst_ne_hnd {f : Expr} (hf : f ≠ .prim .hnd) (j : ℕ) (s : Val)
    (hs : s.1.HndNamesNZ) : f.subst j s ≠ .prim .hnd := by
  cases f <;> simp only [Expr.subst] <;> (try split) <;> (try split) <;> (try simp_all; done)
  intro h; rw [h] at hs; exact hndNZ_prim_hnd hs

/-- Shifting keeps handler names. -/
theorem hndNZ_shift (d : ℕ) : ∀ (e : Expr) (c : ℕ), e.HndNamesNZ → (e.shift d c).HndNamesNZ := by
  intro e
  induction e with
  | var i => intro c _; simp only [Expr.shift]; split <;> simp [Expr.HndNamesNZ]
  | unit => intro c h; exact h
  | loc _ => intro c h; exact h
  | prim _ => intro c h; exact h
  | pair a b iha ihb =>
      intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢; exact ⟨iha c h.1, ihb c h.2⟩
  | seq a b iha ihb =>
      intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢; exact ⟨iha c h.1, ihb c h.2⟩
  | letpair a b iha ihb =>
      intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢; exact ⟨iha c h.1, ihb _ h.2⟩
  | inj₁ a iha => intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢; exact iha c h
  | inj₂ a iha => intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢; exact iha c h
  | lam a iha => intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢; exact iha _ h
  | case a b e iha ihb ihe =>
      intro c h; simp only [Expr.shift, Expr.HndNamesNZ] at h ⊢
      exact ⟨iha c h.1, ihb _ h.2.1, ihe _ h.2.2⟩
  | app f a ihf iha =>
      intro c h
      simp only [Expr.shift]
      rw [hndNZ_app] at h ⊢
      rcases h with ⟨rfl, m, r, rfl, hm, hr⟩ | ⟨hf, hf', ha'⟩
      · left
        refine ⟨rfl, m, r.shift d c, rfl, hm, ?_⟩
        have := iha c (by simp [Expr.HndNamesNZ, hr])
        simpa [Expr.shift, Expr.HndNamesNZ] using this
      · exact .inr ⟨shift_ne_hnd hf d c, ihf c hf', iha c ha'⟩

theorem hndNZ_val_shift {v : Val} (h : v.1.HndNamesNZ) (d c : ℕ) : (v.shift d c).1.HndNamesNZ :=
  hndNZ_shift d v.1 c h

/-- Substituting a value whose handlers are named nonzero keeps handler names. -/
theorem hndNZ_subst : ∀ (e : Expr) (j : ℕ) (s : Val), e.HndNamesNZ → s.1.HndNamesNZ →
    (e.subst j s).HndNamesNZ := by
  intro e
  induction e with
  | var i =>
      intro j s _ hs; simp only [Expr.subst]; split
      · exact hs
      · split <;> simp [Expr.HndNamesNZ]
  | unit => intro j s h _; exact h
  | loc _ => intro j s h _; exact h
  | prim _ => intro j s h _; exact h
  | pair a b iha ihb =>
      intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢
      exact ⟨iha j s h.1 hs, ihb j s h.2 hs⟩
  | seq a b iha ihb =>
      intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢
      exact ⟨iha j s h.1 hs, ihb j s h.2 hs⟩
  | letpair a b iha ihb =>
      intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢
      exact ⟨iha j s h.1 hs, ihb _ _ h.2 (hndNZ_val_shift hs 2 0)⟩
  | inj₁ a iha => intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢; exact iha j s h hs
  | inj₂ a iha => intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢; exact iha j s h hs
  | lam a iha =>
      intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢
      exact iha _ _ h (hndNZ_val_shift hs 1 0)
  | case a b e iha ihb ihe =>
      intro j s h hs; simp only [Expr.subst, Expr.HndNamesNZ] at h ⊢
      exact ⟨iha j s h.1 hs, ihb _ _ h.2.1 (hndNZ_val_shift hs 1 0),
        ihe _ _ h.2.2 (hndNZ_val_shift hs 1 0)⟩
  | app f a ihf iha =>
      intro j s h hs
      simp only [Expr.subst]
      rw [hndNZ_app] at h ⊢
      rcases h with ⟨rfl, m, r, rfl, hm, hr⟩ | ⟨hf, hf', ha'⟩
      · left
        refine ⟨rfl, m, r.subst j s, rfl, hm, ?_⟩
        have := iha j s (by simp [Expr.HndNamesNZ, hr]) hs
        simpa [Expr.subst, Expr.HndNamesNZ] using this
      · exact .inr ⟨subst_ne_hnd hf j s hs, ihf j s hf' hs, iha j s ha' hs⟩

/-! ### Handler names in a context -/

/-- The handlers of `K`'s frames are named nonzero: `K` around a variable is `NZ`. -/
def KNZ (K : Kont) : Prop := (K.plug (.var 0)).HndNamesNZ

/-- Neither a literal-named pair nor a primitive: a term whose shape no handler frame reads. -/
def NotNameLike (a : Expr) : Prop := (∀ m r, a ≠ .pair (.prim (.lit (.i32 m))) r) ∧ ∀ p, a ≠ .prim p

theorem notNameLike_var (j : ℕ) : NotNameLike (.var j) :=
  ⟨fun _ _ h => Expr.noConfusion h, fun _ h => Expr.noConfusion h⟩

theorem plug_eq_prim {K : Kont} {e : Expr} {p : Prim} (h : K.plug e = .prim p) :
    K = .hole ∧ e = .prim p := by
  cases K <;> simp_all [Kont.plug]

theorem plug_ne_prim {K : Kont} {e : Expr} (he : ∀ p, e ≠ .prim p) (p : Prim) :
    K.plug e ≠ .prim p :=
  fun h => he p (plug_eq_prim h).2

/-- A handler frame's pair, read through a context: `K[a]` is a literal-named pair only as
`K = (lit m, K')`. -/
theorem plug_eq_namePair {K : Kont} {a : Expr} (ha : NotNameLike a) {m : UInt32} {r : Expr}
    (h : K.plug a = .pair (.prim (.lit (.i32 m))) r) :
    ∃ (v : Val) (K' : Kont), K = .pairR v K' ∧ v.1 = .prim (.lit (.i32 m)) ∧ r = K'.plug a := by
  cases K with
  | hole => exact absurd h (ha.1 m r)
  | pairL K' e =>
      simp only [Kont.plug, Expr.pair.injEq] at h
      exact absurd (plug_eq_prim h.1).2 (ha.2 _)
  | pairR v K' =>
      simp only [Kont.plug, Expr.pair.injEq] at h
      exact ⟨v, K', rfl, h.1, h.2.symm⟩
  | _ => simp [Kont.plug] at h

theorem plug_hndNZ_inv : ∀ (K : Kont) {a : Expr}, NotNameLike a → (K.plug a).HndNamesNZ →
    KNZ K ∧ a.HndNamesNZ := by
  intro K
  induction K with
  | hole => intro a _ h; exact ⟨by simp [KNZ, Kont.plug, Expr.HndNamesNZ], h⟩
  | pairL K e ih =>
      intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | pairR v K ih =>
      intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢
      exact ⟨⟨h.1, (ih ha h.2).1⟩, (ih ha h.2).2⟩
  | letpair K e ih =>
      intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | case K e₁ e₂ ih =>
      intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | seq K e ih =>
      intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | inj₁ K ih => intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢; exact ih ha h
  | inj₂ K ih => intro a ha h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h ⊢; exact ih ha h
  | appR f K ih =>
      intro a ha h
      simp only [KNZ, Kont.plug] at h ⊢
      rw [hndNZ_app] at h ⊢
      rcases h with ⟨rfl, m, r, hpr, hm, hr⟩ | ⟨hf, hf', hK⟩
      · obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_namePair ha hpr
        have := ih ha (by
          simp only [Kont.plug, Expr.HndNamesNZ]
          exact ⟨by show v.1.HndNamesNZ; rw [hv]; simp [Expr.HndNamesNZ], hr⟩)
        refine ⟨.inl ⟨rfl, m, K'.plug (.var 0), by simp [Kont.plug, hv], hm, ?_⟩, this.2⟩
        have h2 := this.1
        simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at h2
        exact h2.2
      · exact ⟨.inr ⟨hf, hf', (ih ha hK).1⟩, (ih ha hK).2⟩
  | appL K v ih =>
      intro a ha h
      simp only [KNZ, Kont.plug] at h ⊢
      rw [hndNZ_app] at h ⊢
      rcases h with ⟨hK, -⟩ | ⟨-, hK, hv⟩
      · exact absurd hK (plug_ne_prim ha.2 _)
      · exact ⟨.inr ⟨plug_ne_prim (fun _ h => by cases h) _, (ih ha hK).1, hv⟩, (ih ha hK).2⟩

theorem plug_hndNZ : ∀ (K : Kont) {a : Expr}, KNZ K → a.HndNamesNZ → (K.plug a).HndNamesNZ := by
  intro K
  induction K with
  | hole => intro a _ h; exact h
  | pairL K e ih =>
      intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | pairR v K ih =>
      intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ⟨hK.1, ih hK.2 h⟩
  | letpair K e ih =>
      intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | case K e₁ e₂ ih =>
      intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | seq K e ih =>
      intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | inj₁ K ih => intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ih hK h
  | inj₂ K ih => intro a hK h; simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK ⊢; exact ih hK h
  | appR f K ih =>
      intro a hK h
      simp only [KNZ, Kont.plug] at hK ⊢
      rw [hndNZ_app] at hK ⊢
      rcases hK with ⟨rfl, m, r, hpr, hm, hr⟩ | ⟨hf, hf', hK⟩
      · obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_namePair (notNameLike_var 0) hpr
        have := ih (a := a) (by
          simp only [KNZ, Kont.plug, Expr.HndNamesNZ]
          exact ⟨by show v.1.HndNamesNZ; rw [hv]; simp [Expr.HndNamesNZ], hr⟩) h
        simp only [Kont.plug, Expr.HndNamesNZ] at this
        exact .inl ⟨rfl, m, K'.plug a, by simp [Kont.plug, hv], hm, this.2⟩
      · exact .inr ⟨hf, hf', ih hK h⟩
  | appL K v ih =>
      intro a hK h
      simp only [KNZ, Kont.plug] at hK ⊢
      rw [hndNZ_app] at hK ⊢
      rcases hK with ⟨hK, -⟩ | ⟨-, hK, hv⟩
      · exact absurd hK (plug_ne_prim (fun _ h => by cases h) _)
      · refine .inr ⟨fun he => ?_, ih hK h, hv⟩
        obtain ⟨rfl, rfl⟩ := plug_eq_prim he
        exact hndNZ_prim_hnd h

/-! ### No step creates a handler named `0` -/

/-- Every stored value's handlers are named nonzero. -/
def HeapNZ (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → v.1.HndNamesNZ

theorem heapNZ_upd {μ : Heap} (hμ : HeapNZ μ) (ℓ : Loc) {v : Val} (hv : v.1.HndNamesNZ) :
    HeapNZ (μ.upd ℓ v) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h; subst h; exact hv
  · rw [Heap.upd_other hk] at h; exact hμ k w h

theorem heapNZ_del {μ : Heap} (hμ : HeapNZ μ) (ℓ : Loc) : HeapNZ (μ.del ℓ) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h
  · rw [Heap.del_other hk] at h; exact hμ k w h

theorem heapNZ_fill {μ : Heap} (hμ : HeapNZ μ) (ℓ : Loc) (n : ℕ) {v : Val} (hv : v.1.HndNamesNZ) :
    HeapNZ (μ.fill ℓ n v) := by
  intro k w h
  simp only [Heap.fill] at h
  split at h
  · cases h; exact hv
  · exact hμ k w h

theorem _root_.BoCa.BoLo.Kont.plug_shift (d : ℕ) (K : Kont) : ∀ (c : ℕ) (x : Expr),
    (K.plug x).shift d c = (K.shift d c).plug (x.shift d c) := by
  induction K with
  | hole => intro c x; rfl
  | pairL K e ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | pairR v K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih, Val.val_shift]
  | letpair K e ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | case K e₁ e₂ ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | appR f K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | appL K v ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih, Val.val_shift]
  | seq K e ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | inj₁ K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | inj₂ K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]

theorem knz_shift {K : Kont} (hK : KNZ K) (d : ℕ) : KNZ (K.shift d 0) := by
  have h := hndNZ_shift d _ 0 hK
  rw [Kont.plug_shift] at h
  simp only [Expr.shift, Nat.not_lt_zero, if_false, zero_add] at h
  exact (plug_hndNZ_inv _ (notNameLike_var d) h).1

theorem hndNZ_clauseAt : ∀ (e : Expr) (i : ℕ) {c : Val}, BoCa.BoLo.clauseAt e i = some c →
    e.HndNamesNZ → c.1.HndNamesNZ
  | .pair c' _, 0, c, h, he => by
      simp only [BoCa.BoLo.clauseAt] at h
      split at h
      · cases h; exact he.1
      · cases h
  | .pair _ r, i + 1, c, h, he => hndNZ_clauseAt r i h he.2
  | .var _, _, _, h, _ | .unit, _, _, h, _ | .inj₁ _, _, _, h, _ | .inj₂ _, _, _, h, _
  | .lam _, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ | .seq _ _, _, _, h, _
  | .letpair _ _, _, _, h, _ | .case _ _ _, _, _, h, _ | .app _ _, _, _, h, _ => by
      simp [BoCa.BoLo.clauseAt] at h

theorem hndNZ_namesVal : ∀ N : List UInt32, (BoCa.BoLo.namesVal N).1.HndNamesNZ
  | [] => by simp [BoCa.BoLo.namesVal, Val.inj₁, Val.unit, Expr.HndNamesNZ]
  | m :: N => by
      have := hndNZ_namesVal N
      simp only [BoCa.BoLo.namesVal, Val.inj₂, Val.pair, Val.i32, Expr.HndNamesNZ] at this ⊢
      exact ⟨by simp, this⟩

theorem hndNZ_errVal {err : Option Val} (h : ∀ E, err = some E → E.1.HndNamesNZ) :
    (BoCa.BoLo.errVal err).1.HndNamesNZ := by
  cases err with
  | none => simp [BoCa.BoLo.errVal, Val.inj₁, Val.unit, Expr.HndNamesNZ]
  | some E => simp only [BoCa.BoLo.errVal, Val.inj₂, Expr.HndNamesNZ]; exact h E rfl

theorem hndNZ_opPayload (n i : UInt32) {v : Val} (hv : v.1.HndNamesNZ) :
    (opPayload n i v).1.HndNamesNZ := by
  simp only [opPayload, Val.pair, Val.i32, Expr.HndNamesNZ]; exact ⟨by simp, by simp, hv⟩

theorem hndNZ_opPayload_inv {n i : UInt32} {v : Val} (h : (opPayload n i v).1.HndNamesNZ) :
    v.1.HndNamesNZ := by
  simp only [opPayload, Val.pair, Val.i32, Expr.HndNamesNZ] at h; exact h.2.2

theorem hndNZ_cancelVal (N : List UInt32) {err : Option Val}
    (h : ∀ E, err = some E → E.1.HndNamesNZ) : (cancelVal N err).1.HndNamesNZ := by
  simp only [cancelVal]
  apply hndNZ_opPayload
  simp only [Val.pair, Expr.HndNamesNZ]
  exact ⟨hndNZ_namesVal N, hndNZ_errVal h⟩

theorem hndNZ_cancelVal_inv {N : List UInt32} {err : Option Val}
    (h : (cancelVal N err).1.HndNamesNZ) : ∀ E, err = some E → E.1.HndNamesNZ := by
  rintro E rfl
  have h' := hndNZ_opPayload_inv h
  simp only [Val.pair, BoCa.BoLo.errVal, Val.inj₂, Expr.HndNamesNZ] at h'
  exact h'.2

theorem hndNZ_raise {p : Val} (hp : p.1.HndNamesNZ) : (raiseE (.val p)).HndNamesNZ := by
  simp only [raiseE, Expr.val, Val.prim]
  rw [hndNZ_app]
  exact .inr ⟨by simp, by simp [Expr.HndNamesNZ], hp⟩

theorem hndNZ_raise_inv {p : Val} (h : (raiseE (.val p)).HndNamesNZ) : p.1.HndNamesNZ := by
  simp only [raiseE, Expr.val, Val.prim] at h
  rw [hndNZ_app] at h
  rcases h with ⟨h, -⟩ | ⟨-, -, h⟩
  · simp at h
  · exact h

theorem hndNZ_perform_inv {p : Val} (h : (performE (.val p)).HndNamesNZ) : p.1.HndNamesNZ := by
  simp only [performE, Expr.val, Val.prim] at h
  rw [hndNZ_app] at h
  rcases h with ⟨h, -⟩ | ⟨-, -, h⟩
  · simp at h
  · exact h

theorem notNameLike_raise (p : Val) : NotNameLike (raiseE (.val p)) :=
  ⟨fun _ _ h => by simp [raiseE] at h, fun _ h => by simp [raiseE] at h⟩

theorem notNameLike_perform (p : Val) : NotNameLike (performE (.val p)) :=
  ⟨fun _ _ h => by simp [performE] at h, fun _ h => by simp [performE] at h⟩

/-- `hnd H e` is `NZ` exactly when `H` is a handler of a nonzero literal name and `e` is `NZ`. -/
theorem hndNZ_hndE (n : UInt32) (qs hr hs : Val) (e : Expr) :
    (hndE (hndVal n qs hr hs) e).HndNamesNZ ↔
      n ≠ 0 ∧ qs.1.HndNamesNZ ∧ hr.1.HndNamesNZ ∧ hs.1.HndNamesNZ ∧ e.HndNamesNZ := by
  simp only [hndE, hndVal, Expr.val, Val.prim, Val.pair, Val.i32]
  rw [hndNZ_app, hndNZ_app]
  simp only [Expr.HndNamesNZ]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, (⟨-, m, r, h, hm, hr'⟩ | ⟨h, -⟩), he⟩)
    · simp at h
    · simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hm, hr'.1, hr'.2.1, hr'.2.2, he⟩
    · exact absurd rfl h
  · rintro ⟨hn, hq', hr', hs', he⟩
    refine .inr ⟨by simp, .inl ⟨trivial, n, _, rfl, hn, ?_⟩, he⟩
    simp only [Expr.HndNamesNZ]; exact ⟨hq', hr', hs'⟩

theorem hndVal_shift (d : ℕ) (n : UInt32) (qs hr hs : Val) :
    Val.shift d 0 (hndVal n qs hr hs) = hndVal n (qs.shift d 0) (hr.shift d 0) (hs.shift d 0) := by
  apply Subtype.ext; simp [hndVal, Val.pair, Val.i32, Val.shift, Expr.shift]

theorem hndNZ_kappa {n : UInt32} {qs hr hs : Val} {K : Kont} (hn : n ≠ 0)
    (hq' : qs.1.HndNamesNZ) (hr' : hr.1.HndNamesNZ)
    (hs' : hs.1.HndNamesNZ) (hK : KNZ K) : (kappa n (hndVal n qs hr hs) K).HndNamesNZ := by
  simp only [kappa, Expr.val, Val.lam, Expr.HndNamesNZ]
  refine ⟨trivial, ⟨trivial, ?_⟩, trivial, ?_⟩
  · rw [hndVal_shift, hndNZ_hndE]
    exact ⟨hn, hndNZ_val_shift hq' 3 0, hndNZ_val_shift hr' 3 0, hndNZ_val_shift hs' 3 0,
      plug_hndNZ _ (knz_shift hK 3) (by simp [Expr.HndNamesNZ])⟩
  · simp only [ccatchE, Expr.val, Val.prim]
    rw [hndNZ_app]
    refine .inr ⟨by simp, by simp [Expr.HndNamesNZ], ?_⟩
    rw [hndVal_shift, hndNZ_hndE]
    exact ⟨hn, hndNZ_val_shift hq' 2 0, hndNZ_val_shift hr' 2 0, hndNZ_val_shift hs' 2 0,
      plug_hndNZ _ (knz_shift hK 2) (hndNZ_raise (hndNZ_cancelVal _ (fun _ h => by cases h)))⟩

theorem hndNZ_kappaCell {n : UInt32} {qs hr hs : Val} {K : Kont} (aff : Bool) (hn : n ≠ 0)
    (hq' : qs.1.HndNamesNZ) (hr' : hr.1.HndNamesNZ)
    (hs' : hs.1.HndNamesNZ) (hK : KNZ K) : (kappaCell aff n (hndVal n qs hr hs) K).HndNamesNZ := by
  simp only [kappaCell, kappaCBody, Expr.val, Val.lam, Val.prim, Val.unit, freeE, stuckE]
  rw [hndNZ_app, hndNZ_app]
  refine .inr ⟨by simp, ?_, .inr ⟨by simp, by simp [Expr.HndNamesNZ], trivial⟩⟩
  simp only [Expr.HndNamesNZ]
  refine ⟨trivial, ⟨trivial, ?_, ?_⟩, ?_⟩
  · exact ⟨by simp, trivial⟩
  · rw [hndVal_shift, hndNZ_hndE]
    exact ⟨hn, hndNZ_val_shift hq' 4 0, hndNZ_val_shift hr' 4 0, hndNZ_val_shift hs' 4 0,
      plug_hndNZ _ (knz_shift hK 4) (by simp [Expr.HndNamesNZ])⟩
  · cases aff
    · simp only [Bool.false_eq_true, if_false]
      rw [hndNZ_app]; exact .inr ⟨by simp, trivial, trivial⟩
    · simp only [if_true, Expr.HndNamesNZ]
      refine ⟨trivial, ?_, ?_⟩
      · exact ⟨by simp, trivial⟩
      · simp only [ccatchE, Expr.val, Val.prim]
        rw [hndNZ_app]
        refine .inr ⟨by simp, by simp [Expr.HndNamesNZ], ?_⟩
        rw [hndVal_shift, hndNZ_hndE]
        exact ⟨hn, hndNZ_val_shift hq' 3 0, hndNZ_val_shift hr' 3 0, hndNZ_val_shift hs' 3 0,
          plug_hndNZ _ (knz_shift hK 3) (hndNZ_raise (hndNZ_cancelVal _ (fun _ h => by cases h)))⟩

theorem hndNZ_kappaAt {t n : UInt32} {qs hr hs : Val} {K : Kont} (hn : n ≠ 0)
    (hq' : qs.1.HndNamesNZ) (hr' : hr.1.HndNamesNZ)
    (hs' : hs.1.HndNamesNZ) (hK : KNZ K) : (kappaAt t n (hndVal n qs hr hs) K).HndNamesNZ := by
  unfold kappaAt
  split
  · exact hndNZ_kappaCell false hn hq' hr' hs' hK
  · split
    · exact hndNZ_kappaCell true hn hq' hr' hs' hK
    · exact hndNZ_kappa hn hq' hr' hs' hK

theorem hndNZ_opt {o : Option Val} (h : ∀ v, o = some v → v.1.HndNamesNZ) :
    (Val.opt o).1.HndNamesNZ := by
  cases o with
  | none => simp [Val.opt, Val.inj₂, Val.unit, Expr.HndNamesNZ]
  | some v => simp only [Val.opt, Val.inj₁, Expr.HndNamesNZ]; exact h v rfl

theorem hndNZ_bool (b : Bool) : (Val.bool b).1.HndNamesNZ := by
  cases b <;> simp [Val.bool, Val.inj₁, Val.inj₂, Val.unit, Expr.HndNamesNZ]

theorem hndNZ_host (H : Host) (op : HostOp) {v r : Val} (h : H.call op v = some r) :
    r.1.HndNamesNZ := by
  have hi32 : ∀ n, (Val.i32 n).1.HndNamesNZ := fun n => by simp [Val.i32, Expr.HndNamesNZ]
  have hi64 : ∀ n, (Val.i64 n).1.HndNamesNZ := fun n => by simp [Val.i64, Expr.HndNamesNZ]
  have hu8 : ∀ n, (Val.u8 n).1.HndNamesNZ := fun n => by simp [Val.u8, Expr.HndNamesNZ]
  cases op with
  | bin w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi64 _
  | div w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hndNZ_opt fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hndNZ_opt fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi64 _
  | un w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | eqz w =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hndNZ_bool _
      · obtain ⟨_, -, rfl⟩ := h; exact hndNZ_bool _
  | rel w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hndNZ_bool _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hndNZ_bool _
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hu8 _
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _

theorem hndNZ_app_val {f a : Expr} (hf : f.HndNamesNZ) (ha : a.HndNamesNZ) :
    (Expr.app f a).HndNamesNZ := by
  rw [hndNZ_app]
  by_cases h : f = .prim .hnd
  · subst h; exact absurd hf hndNZ_prim_hnd
  · exact .inr ⟨h, hf, ha⟩

theorem hndNZ_app_inv {f a : Expr} (hf : f ≠ .prim .hnd) (h : (Expr.app f a).HndNamesNZ) :
    f.HndNamesNZ ∧ a.HndNamesNZ := by
  rw [hndNZ_app] at h
  rcases h with ⟨h, -⟩ | ⟨-, h₁, h₂⟩
  · exact absurd h hf
  · exact ⟨h₁, h₂⟩

theorem hndNZ_tabFill {f : Val} (hf : f.1.HndNamesNZ) (ℓ : Loc) (n : UInt32) :
    ∀ i k, (tabFill f ℓ n i k).HndNamesNZ
  | i, 0 => by simp [tabFill, Val.arr, Val.pair, Val.loc, Val.i32, Expr.HndNamesNZ]
  | i, k + 1 => by
      simp only [tabFill, Expr.HndNamesNZ]
      refine ⟨hndNZ_app_val (hndNZ_app_val (by simp [Expr.HndNamesNZ])
        (by simp [Val.loc, Expr.HndNamesNZ]))
        (hndNZ_app_val hf (by simp [Val.i32, Expr.HndNamesNZ])),
        hndNZ_tabFill hf ℓ n (i + 1) k⟩

theorem hndNZ_dropFill {f : Val} (hf : f.1.HndNamesNZ) (ℓ : Loc) :
    ∀ i k, (dropFill f ℓ i k).HndNamesNZ
  | i, 0 => by simp [dropFill, Val.unit, Expr.HndNamesNZ]
  | i, k + 1 => by
      simp only [dropFill, Expr.HndNamesNZ]
      exact ⟨hndNZ_app_val hf (hndNZ_app_val (by simp [Expr.HndNamesNZ])
        (by simp [Val.loc, Expr.HndNamesNZ])), hndNZ_dropFill hf ℓ (i + 1) k⟩

theorem hndNZ_val_i32 (n : UInt32) : (Val.i32 n).1.HndNamesNZ := by
  simp [Val.i32, Expr.HndNamesNZ]

theorem hndNZ_primApp {p : Prim} (hp : p ≠ .hnd) (e : Expr) :
    (Expr.app (.prim p) e).HndNamesNZ ↔ e.HndNamesNZ := by
  rw [hndNZ_app]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
    · exact absurd (Expr.prim.inj h) hp
    · exact h
  · intro h; exact .inr ⟨fun h' => hp (Expr.prim.inj h'), by simpa [Expr.HndNamesNZ] using hp, h⟩

theorem hndNZ_ubindE (ND : Val) (e : Expr) :
    (ubindE ND e).HndNamesNZ ↔ ND.1.HndNamesNZ ∧ e.HndNamesNZ := by
  simp only [ubindE, Expr.val, Val.prim]
  rw [hndNZ_app, hndNZ_primApp (by decide)]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h₁, h₂⟩)
    · simp at h
    · exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩; exact .inr ⟨by simp, h₁, h₂⟩

theorem hndNZ_cfinE (st : Val) (e : Expr) :
    (cfinE st e).HndNamesNZ ↔ st.1.HndNamesNZ ∧ e.HndNamesNZ := by
  simp only [cfinE, Expr.val, Val.prim]
  rw [hndNZ_app, hndNZ_primApp (by decide)]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h₁, h₂⟩)
    · simp at h
    · exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩; exact .inr ⟨by simp, h₁, h₂⟩

theorem hndNZ_ccatchE (e : Expr) : (ccatchE e).HndNamesNZ ↔ e.HndNamesNZ := by
  simp only [ccatchE, Expr.val, Val.prim]
  exact hndNZ_primApp (by decide) e

theorem hndNZ_loc (ℓ : Loc) : (Val.loc ℓ).1.HndNamesNZ := by simp [Val.loc, Expr.HndNamesNZ]

theorem hndNZ_arr (ℓ : Loc) (n : UInt32) : (Val.arr ℓ n).1.HndNamesNZ := by
  simp [Val.arr, Val.pair, Val.loc, Val.i32, Expr.HndNamesNZ]

/-- **No head step creates a handler named `0`**, nor stores one. -/
theorem hndNZ_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') (ha : a.HndNamesNZ)
    (hμ : HeapNZ μ) : a'.HndNamesNZ ∧ HeapNZ μ' := by
  cases h with
  | beta b v =>
      have := hndNZ_app_inv (by simp [Expr.val, Val.lam]) ha
      exact ⟨hndNZ_subst b 0 v this.1 this.2, hμ⟩
  | alloc v ℓ hℓ =>
      exact ⟨hndNZ_loc ℓ, heapNZ_upd hμ ℓ ((hndNZ_primApp (by decide) _).1 ha)⟩
  | free ℓ v hv => exact ⟨hμ ℓ v hv, heapNZ_del hμ ℓ⟩
  | load ℓ v hv => exact ⟨hμ ℓ v hv, hμ⟩
  | store ℓ v w hw =>
      have := hndNZ_app_inv (by simp [Expr.val, Val.prim]) ha
      exact ⟨by simp [Val.unit, Expr.HndNamesNZ], heapNZ_upd hμ ℓ this.2⟩
  | seq e => exact ⟨ha.2, hμ⟩
  | letpair v₁ v₂ e =>
      have h1 : (Val.pair v₁ v₂).1.HndNamesNZ := ha.1
      simp only [Val.pair, Expr.HndNamesNZ] at h1
      exact ⟨hndNZ_subst _ 0 v₁ (hndNZ_subst e 0 (v₂.shift 1 0) ha.2 (hndNZ_val_shift h1.2 1 0))
        h1.1, hμ⟩
  | case₁ v e₁ e₂ => exact ⟨hndNZ_subst e₁ 0 v ha.2.1 ha.1, hμ⟩
  | case₂ v e₁ e₂ => exact ⟨hndNZ_subst e₂ 0 v ha.2.2 ha.1, hμ⟩
  | host op v r hr => exact ⟨hndNZ_host ℍ op hr, hμ⟩
  | tab c f ℓ hℓ =>
      have h1 := (hndNZ_primApp (by decide) _).1 ha
      simp only [Val.pair, Expr.HndNamesNZ] at h1
      exact ⟨hndNZ_tabFill h1.2 ℓ _ _ _, heapNZ_fill hμ ℓ _ (by simp [Val.unit, Expr.HndNamesNZ])⟩
  | idx ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [idxAns]; split <;> simp [Val.inj₁, Val.inj₂, Val.loc, Val.unit, Expr.HndNamesNZ]
  | split ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [splitAns]; split <;>
        simp [Val.inj₁, Val.inj₂, Val.pair, Val.arr, Val.loc, Val.i32, Expr.HndNamesNZ]
  | drop f ℓ n =>
      have h1 := (hndNZ_primApp (by decide) _).1 ha
      simp only [Val.pair, Expr.HndNamesNZ] at h1
      exact ⟨hndNZ_dropFill h1.1 ℓ _ _, hμ⟩
  | count f n i s' =>
      have h1 := (hndNZ_primApp (by decide) _).1 ha
      simp only [Val.pair, Val.i32, Expr.HndNamesNZ] at h1
      refine ⟨?_, hμ⟩
      simp only [countNext]; split
      · simp only [Expr.val, Val.prim]
        rw [hndNZ_primApp (p := .count) (by decide)]
        simp only [Val.pair, Val.i32, Expr.HndNamesNZ]
        refine ⟨h1.1, Prim.noConfusion, Prim.noConfusion, hndNZ_app_val h1.1 ?_⟩
        simp only [Expr.HndNamesNZ]
        exact ⟨Prim.noConfusion, h1.2.2.2⟩
      · exact h1.2.2.2
  | countTry f n i s' =>
      have h1 := (hndNZ_primApp (by decide) _).1 ha
      simp only [Val.pair, Val.i32, Expr.HndNamesNZ] at h1
      refine ⟨?_, hμ⟩
      simp only [countTryNext]; split
      · simp only [Expr.HndNamesNZ]
        refine ⟨hndNZ_app_val h1.1 ?_, ?_, trivial⟩
        · simp only [Expr.val, Val.pair, Val.i32, Expr.HndNamesNZ]; exact ⟨by simp, h1.2.2.2⟩
        · simp only [Expr.val, Val.prim]
          rw [hndNZ_primApp (p := .countTry) (by decide)]
          simp only [Val.i32, Expr.HndNamesNZ]
          exact ⟨hndNZ_val_shift h1.1 1 0, by simp, by simp, trivial⟩
      · simp only [Expr.val, Val.inj₁, Expr.HndNamesNZ]; exact h1.2.2.2
  | boundedFix s' k a =>
      have h1 := (hndNZ_primApp (by decide) _).1 ha
      simp only [Val.pair, Val.i32, Expr.HndNamesNZ] at h1
      refine ⟨hndNZ_app_val h1.1 ?_, hμ⟩
      simp only [Expr.val, Val.pair, Expr.HndNamesNZ]
      refine ⟨?_, h1.2.2⟩
      simp only [fixSelf]; split
      · simp [Val.inj₁, Val.unit, Expr.HndNamesNZ]
      · simp only [Val.inj₂, Val.lam, Expr.HndNamesNZ, Expr.val, Val.prim]
        exact ⟨by decide, hndNZ_val_shift h1.1 1 0, by simp [Val.i32, Expr.HndNamesNZ], trivial⟩
  | hret n qs hr hs w =>
      obtain ⟨-, -, hr', -, hw⟩ := (hndNZ_hndE n qs hr hs _).1 ha
      exact ⟨hndNZ_app_val hr' hw, hμ⟩
  | hop n i qs hr hs c v K hc hK =>
      obtain ⟨hn, hq', hr', hs', hb⟩ := (hndNZ_hndE n qs hr hs _).1 ha
      obtain ⟨hKnz, hp⟩ := plug_hndNZ_inv K (notNameLike_perform _) hb
      have hv := hndNZ_opPayload_inv (hndNZ_perform_inv hp)
      have hc' := hndNZ_clauseAt hs.1 i.toNat hc hs'
      exact ⟨hndNZ_app_val hc' ⟨hv, hndNZ_kappaAt hn hq' hr' hs' hKnz⟩, hμ⟩
  | hunwind n i qs hr hs c v K hc hK =>
      obtain ⟨hn, -, hr', hs', hb⟩ := (hndNZ_hndE n qs hr hs _).1 ha
      obtain ⟨-, hp⟩ := plug_hndNZ_inv K (notNameLike_raise _) hb
      have hv := hndNZ_opPayload_inv (hndNZ_raise_inv hp)
      exact ⟨hndNZ_app_val (hndNZ_clauseAt hs.1 i.toNat hc hs') hv, hμ⟩
  | uthen N D w =>
      obtain ⟨hND, hw⟩ := (hndNZ_ubindE _ _).1 ha
      simp only [Val.pair, Expr.HndNamesNZ] at hND
      exact ⟨hndNZ_app_val hND.1 hw, hμ⟩
  | ufin N D n i v K hn hK =>
      obtain ⟨hND, hb⟩ := (hndNZ_ubindE _ _).1 ha
      simp only [Val.pair, Expr.HndNamesNZ] at hND
      obtain ⟨-, hp⟩ := plug_hndNZ_inv K (notNameLike_raise _) hb
      exact ⟨⟨hndNZ_app_val hND.2 (by simp [Val.unit, Expr.HndNamesNZ]), hp⟩, hμ⟩
  | ufinC N D Ns err K hK =>
      obtain ⟨hND, hb⟩ := (hndNZ_ubindE _ _).1 ha
      simp only [Val.pair, Expr.HndNamesNZ] at hND
      obtain ⟨-, hp⟩ := plug_hndNZ_inv K (notNameLike_raise _) hb
      exact ⟨(hndNZ_cfinE _ _).2 ⟨hndNZ_raise_inv hp,
        hndNZ_app_val hND.2 (by simp [Val.unit, Expr.HndNamesNZ])⟩, hμ⟩
  | cfret Ns err w =>
      exact ⟨hndNZ_raise ((hndNZ_cfinE _ _).1 ha).1, hμ⟩
  | cferr Ns err m j w K hK =>
      obtain ⟨hs', hb⟩ := (hndNZ_cfinE _ _).1 ha
      obtain ⟨-, hp⟩ := plug_hndNZ_inv K (notNameLike_raise _) hb
      have hw := hndNZ_opPayload_inv (hndNZ_raise_inv hp)
      refine ⟨hndNZ_raise (hndNZ_cancelVal Ns ?_), hμ⟩
      intro E hE
      simp only [BoCa.BoLo.errNext] at hE
      split at hE
      · exact hndNZ_cancelVal_inv hs' E hE
      · split at hE
        · cases hE
        · cases hE; exact hndNZ_opPayload m j hw
  | cancel Ns K hK => exact ⟨by simp [Val.unit, Expr.HndNamesNZ], hμ⟩
  | creraise Ns E K hK =>
      obtain ⟨-, hp⟩ := plug_hndNZ_inv K (notNameLike_raise _) ((hndNZ_ccatchE _).1 ha)
      exact ⟨hndNZ_raise (hndNZ_cancelVal_inv (hndNZ_raise_inv hp) E rfl), hμ⟩

/-- A redex is neither a pair nor a primitive. -/
theorem notNameLike_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') :
    NotNameLike a := by
  constructor
  · intro m r hpr
    subst hpr
    cases h
  · intro p hp
    subst hp
    exact h.not_isVal .prim

theorem hndNZ_step1 {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e')
    (he : e.HndNamesNZ) (hμ : HeapNZ μ) : e'.HndNamesNZ ∧ HeapNZ μ' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  obtain ⟨hK, ha⟩ := plug_hndNZ_inv K (notNameLike_head hh) he
  obtain ⟨ha', hμ'⟩ := hndNZ_head hh ha hμ
  exact ⟨plug_hndNZ K hK ha', hμ'⟩

/-- **No step creates a handler named `0`**: a run from a term whose handlers are named nonzero,
with stored values so, keeps both. -/
theorem hndNamesNZ_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e')
    (he : e.HndNamesNZ) (hμ : HeapNZ μ) : e'.HndNamesNZ ∧ HeapNZ μ' := by
  induction h with
  | refl => exact ⟨he, hμ⟩
  | more h₁ _ ih =>
      obtain ⟨he₁, hμ₁⟩ := hndNZ_step1 h₁ he hμ
      exact ih he₁ hμ₁

theorem heapNZ_empty : HeapNZ Adequacy.emptyMem := fun _ _ h => by simp [Adequacy.emptyMem] at h

/-! ### Where a raise is stopped -/

/-- The frame `f` stops a raise of `n`. -/
abbrev FrameCatches (n : UInt32) (f : Expr) : Prop := (Kont.appR f .hole).Catches n = true

/-- **The innermost frame of `K` that stops a raise of `n`**: `K` is `Ko` around the frame `f`
around `Ki`, and no frame of `Ki` stops it. -/
def InnerCatch (n : UInt32) (K Ko : Kont) (f : Expr) (Ki : Kont) : Prop :=
  K = Ko.comp (.appR f Ki) ∧ Ki.Catches n = false ∧ FrameCatches n f

theorem catches_appR (n : UInt32) (f : Expr) (K : Kont) :
    (Kont.appR f K).Catches n = ((Kont.appR f .hole).Catches n || K.Catches n) := by
  simp only [Kont.Catches, Bool.or_false]

theorem innerCatch_exists (n : UInt32) :
    ∀ (K : Kont), K.Catches n = true → ∃ Ko f Ki, InnerCatch n K Ko f Ki
  | .hole, h => by simp [Kont.Catches] at h
  | .appR f K, h => by
      by_cases hK : K.Catches n = true
      · obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K hK
        exact ⟨.appR f Ko, g, Ki, rfl, h₁, h₂⟩
      · rw [catches_appR] at h
        simp only [Bool.not_eq_true] at hK
        rw [hK, Bool.or_false] at h
        exact ⟨.hole, f, K, rfl, hK, h⟩
  | .pairL K e, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.pairL Ko e, g, Ki, rfl, h₁, h₂⟩
  | .pairR v K, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.pairR v Ko, g, Ki, rfl, h₁, h₂⟩
  | .letpair K e, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.letpair Ko e, g, Ki, rfl, h₁, h₂⟩
  | .case K e₁ e₂, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.case Ko e₁ e₂, g, Ki, rfl, h₁, h₂⟩
  | .appL K v, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.appL Ko v, g, Ki, rfl, h₁, h₂⟩
  | .seq K e, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.seq Ko e, g, Ki, rfl, h₁, h₂⟩
  | .inj₁ K, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.inj₁ Ko, g, Ki, rfl, h₁, h₂⟩
  | .inj₂ K, h => by
      obtain ⟨Ko, g, Ki, rfl, h₁, h₂⟩ := innerCatch_exists n K h
      exact ⟨.inj₂ Ko, g, Ki, rfl, h₁, h₂⟩

/-- A context around a stopping frame stops the raise. -/
theorem catches_of_innerCatch {n : UInt32} {Ko Ki : Kont} {f : Expr} (hf : FrameCatches n f) :
    (Ko.comp (.appR f Ki)).Catches n = true := by
  rw [catches_comp, catches_appR, hf]; simp

/-- **The innermost stopping frame is unique.** -/
theorem innerCatch_unique {n : UInt32} : ∀ {Ko : Kont} {K Ko' : Kont} {f f' : Expr} {Ki Ki' : Kont},
    InnerCatch n K Ko f Ki → InnerCatch n K Ko' f' Ki' → Ko = Ko' ∧ f = f' ∧ Ki = Ki' := by
  intro Ko
  induction Ko with
  | hole =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, -⟩ ⟨h₁', -, h₃'⟩
      subst h₁
      cases Ko' with
      | hole =>
          simp only [Kont.comp, Kont.appR.injEq] at h₁'
          obtain ⟨rfl, rfl⟩ := h₁'
          exact ⟨rfl, rfl, rfl⟩
      | appR g Ko'' =>
          simp only [Kont.comp, Kont.appR.injEq] at h₁'
          obtain ⟨rfl, rfl⟩ := h₁'
          rw [catches_of_innerCatch h₃'] at h₂
          cases h₂
      | _ => simp [Kont.comp] at h₁'
  | appR g Ko ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | hole =>
          simp only [Kont.comp, Kont.appR.injEq] at h₁'
          obtain ⟨rfl, h⟩ := h₁'
          rw [← h, catches_of_innerCatch h₃] at h₂'
          cases h₂'
      | appR g' Ko'' =>
          simp only [Kont.comp, Kont.appR.injEq] at h₁'
          obtain ⟨rfl, h⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | pairL Ko e ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | pairL Ko'' e' =>
          simp only [Kont.comp, Kont.pairL.injEq] at h₁'
          obtain ⟨h, rfl⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | pairR v Ko ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | pairR v' Ko'' =>
          simp only [Kont.comp, Kont.pairR.injEq] at h₁'
          obtain ⟨rfl, h⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | letpair Ko e ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | letpair Ko'' e' =>
          simp only [Kont.comp, Kont.letpair.injEq] at h₁'
          obtain ⟨h, rfl⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | case Ko e₁ e₂ ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | case Ko'' e₁' e₂' =>
          simp only [Kont.comp, Kont.case.injEq] at h₁'
          obtain ⟨h, rfl, rfl⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | appL Ko v ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | appL Ko'' v' =>
          simp only [Kont.comp, Kont.appL.injEq] at h₁'
          obtain ⟨h, rfl⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | seq Ko e ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | seq Ko'' e' =>
          simp only [Kont.comp, Kont.seq.injEq] at h₁'
          obtain ⟨h, rfl⟩ := h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h, h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | inj₁ Ko ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | inj₁ Ko'' =>
          simp only [Kont.comp, Kont.inj₁.injEq] at h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'
  | inj₂ Ko ih =>
      rintro K Ko' f f' Ki Ki' ⟨h₁, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
      subst h₁
      cases Ko' with
      | inj₂ Ko'' =>
          simp only [Kont.comp, Kont.inj₂.injEq] at h₁'
          obtain ⟨rfl, rfl, rfl⟩ := ih ⟨rfl, h₂, h₃⟩ ⟨h₁', h₂', h₃'⟩
          exact ⟨rfl, rfl, rfl⟩
      | _ => simp [Kont.comp] at h₁'

/-- A raise is no redex by itself. -/
theorem not_head_raise {μ μ' : Heap} {p : Val} {a' : Expr} :
    ¬ Head (ℍ := ℍ) μ (raiseE (.val p)) μ' a' := fun h =>
  head_not_inertApp (p := .raise) trivial h

/-- **A step at a raise is the step of its innermost stopping frame.** -/
theorem step1_raise {μ μ' : Heap} {K : Kont} {p : Val} {n : UInt32} {T : Expr}
    (hp : payloadName p = some n) (h : Step1 (ℍ := ℍ) μ (K.plug (raiseE (.val p))) μ' T) :
    ∃ Ko f Ki a', InnerCatch n K Ko f Ki ∧
      Head (ℍ := ℍ) μ (.app f (Ki.plug (raiseE (.val p)))) μ' a' ∧ T = Ko.plug a' := by
  obtain ⟨Kx, a, a', hE, rfl, hh⟩ := h
  have hnv : ¬ IsVal (raiseE (.val p)) := opE_not_isVal true p
  rcases plug_cmp K Kx hnv hh.not_isVal hE with ⟨K'', h₁, -⟩ | ⟨K'', h₁, h₂⟩
  · have hK := plug_primApp (h₁.symm.trans (opE_eq_app true p)) hh.not_isVal
    subst hK
    simp only [Kont.plug] at h₁
    subst h₁
    exact absurd hh not_head_raise
  · subst h₂
    by_cases h0 : K'' = .hole
    · subst h0
      simp only [Kont.plug] at h₁
      subst h₁
      exact absurd hh not_head_raise
    rcases head_plug hh K'' hnv h₁ h0 with
      ⟨m, qs, hr, hs, K', rfl⟩ | ⟨N, D, K', rfl⟩ | ⟨K', rfl⟩ | ⟨w, H, q, -, rfl, -⟩ |
        ⟨Ns, err, K', rfl⟩
    · subst h₁
      generalize hX : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal m qs hr hs))) K').plug
        (raiseE (.val p)) = X at hh
      cases hh with
      | hunwind n' i qs' hr' hs' c v K₀ hc hK₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          obtain ⟨hf, hb⟩ := hX
          obtain ⟨hK', hpv⟩ := plug_raise_inj hb
          subst hK' hpv
          simp only [payloadName_opPayload, Option.some.injEq] at hp
          subst hp
          refine ⟨Kx, _, K', _, ⟨by rw [hf.2], hK₀, ?_⟩, .hunwind μ n' i qs' hr' hs' c v K' hc hK₀, rfl⟩
          simp [FrameCatches, Kont.Catches, hndVal, Val.pair, Val.i32, Expr.val]
      | hop n' i qs' hr' hs' c v K₀ hc hK₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact absurd hX.2.symm (plug_perform_ne_raise _ _ _ _)
      | hret n' qs' hr' hs' w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact absurd hX.2 (plug_raise_ne_val _ _ _)
      | _ => simp_all [Kont.plug, ubindE, ccatchE, cfinE]
    · subst h₁
      generalize hX : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K').plug
        (raiseE (.val p)) = X at hh
      cases hh with
      | ufin N' D' n' i v K₀ hn hK₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          obtain ⟨hf, hb⟩ := hX
          obtain ⟨hK', hpv⟩ := plug_raise_inj hb
          subst hK' hpv
          simp only [payloadName_opPayload, Option.some.injEq] at hp
          subst hp
          refine ⟨Kx, _, K', _, ⟨by rw [hf.2], hK₀, ?_⟩, .ufin μ N' D' n' i v K' hn hK₀, rfl⟩
          simp [FrameCatches, Kont.Catches, Expr.val]
      | ufinC N' D' Ns err K₀ hK₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          obtain ⟨hf, hb⟩ := hX
          obtain ⟨hK', hpv⟩ := plug_raise_inj hb
          subst hK' hpv
          simp only [payloadName_cancelVal, Option.some.injEq] at hp
          subst hp
          refine ⟨Kx, _, K', _, ⟨by rw [hf.2], hK₀, ?_⟩, .ufinC μ N' D' Ns err K' hK₀, rfl⟩
          simp [FrameCatches, Kont.Catches, Expr.val]
      | uthen N' D' w =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact absurd hX.2 (plug_raise_ne_val _ _ _)
      | _ => simp_all [Kont.plug, hndE, ccatchE, cfinE]
    · subst h₁
      generalize hX : (Kont.appR (.val (.prim .ccatch)) K').plug (raiseE (.val p)) = X at hh
      cases hh with
      | cancel Ns K₀ hK₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          obtain ⟨hf, hb⟩ := hX
          obtain ⟨hK', hpv⟩ := plug_raise_inj hb
          subst hK' hpv
          simp only [payloadName_cancelVal, Option.some.injEq] at hp
          subst hp
          refine ⟨Kx, _, K', _, ⟨rfl, hK₀, ?_⟩, .cancel μ Ns K' hK₀, rfl⟩
          simp [FrameCatches, Kont.Catches, Expr.val]
      | creraise Ns E K₀ hK₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          obtain ⟨hf, hb⟩ := hX
          obtain ⟨hK', hpv⟩ := plug_raise_inj hb
          subst hK' hpv
          simp only [payloadName_cancelVal, Option.some.injEq] at hp
          subst hp
          refine ⟨Kx, _, K', _, ⟨rfl, hK₀, ?_⟩, .creraise μ Ns E K' hK₀, rfl⟩
          simp [FrameCatches, Kont.Catches, Expr.val]
      | _ => simp_all [Kont.plug, hndE, ubindE, cfinE]
    · subst h₁
      generalize hX : (Kont.appL .hole w).plug (raiseE (.val p)) = X at hh
      cases hh <;> simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE, raiseE]
    · subst h₁
      generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal Ns err))) K').plug
        (raiseE (.val p)) = X at hh
      cases hh with
      | cferr Ns' err' m j w K₀ hK₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          obtain ⟨hf, hb⟩ := hX
          obtain ⟨hK', hpv⟩ := plug_raise_inj hb
          subst hK' hpv
          simp only [payloadName_opPayload, Option.some.injEq] at hp
          subst hp
          refine ⟨Kx, _, K', _, ⟨by rw [hf.2], hK₀, ?_⟩, .cferr μ Ns' err' m j w K' hK₀, rfl⟩
          simp [FrameCatches, Kont.Catches, Expr.val]
      | cfret Ns' err' w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact absurd hX.2 (plug_raise_ne_val _ _ _)
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE]

/-- A step at a redex that allocates nothing is the redex's head step. -/
theorem step1_det {μ μ₁ μ' : Heap} {K : Kont} {a a₁ T : Expr} (hh : Head (ℍ := ℍ) μ a μ₁ a₁)
    (hn : a.allocs = false) (h : Step1 (ℍ := ℍ) μ (K.plug a) μ' T) : μ' = μ₁ ∧ T = K.plug a₁ := by
  obtain ⟨K', a', a'', hE, rfl, hh'⟩ := h
  obtain ⟨rfl, rfl⟩ := plug_decomp hh K' K hh' hE.symm
  obtain ⟨h1, h2⟩ := head_det hh hn hh' rfl
  exact ⟨h1.symm, by rw [h2]⟩

/-! ### A fired finaliser runs alone -/

/-- **A fired finaliser runs alone** (SPEC §19's finaliser row, at run time), platform-free: a run
from a typed closed program at `F A` reaches a `[then]` frame at the step that fires it; the
finaliser's run alone, from `D ()`, ends only at a value or at an uncaught raise of a name in `FR`,
the names a finaliser may raise (decision D3). -/
def FinAloneAt (FR : UInt32 → Prop) (J : TypingJ) : Prop :=
  ∀ {e : Expr} {A : VTy}, J.closed e (.ret A) →
    ∀ {μ : Heap} {K₀ K : Kont} {N D : Val} {n i : UInt32} {v : Val},
      Steps (ℍ := ℍ) Adequacy.emptyMem e μ
        (K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))) →
      K.Catches n = false →
      ∀ {μ' : Heap} {t : Expr}, Steps (ℍ := ℍ) μ (.app (.val D) (.val .unit)) μ' t →
        (∀ μ'' t', ¬ Step1 (ℍ := ℍ) μ' t μ'' t') →
        IsVal t ∨ ∃ (K' : Kont) (m j : UInt32) (w : Val),
          t = K'.plug (raiseE (.val (opPayload m j w))) ∧ K'.Catches m = false ∧ FR m

/-- **The operations a fired finaliser's run alone stops at**, platform-free: at every term the
run reaches, an operation its context leaves uncaught is a raise of a name in `FR`.  This is the
half of `FinAloneAt FR` that reads the finaliser's row: no resuming operation, and no cancel,
escapes it. -/
def FinRowsAt (FR : UInt32 → Prop) (J : TypingJ) : Prop :=
  ∀ {e : Expr} {A : VTy}, J.closed e (.ret A) →
    ∀ {μ : Heap} {K₀ K : Kont} {N D : Val} {n i : UInt32} {v : Val},
      Steps (ℍ := ℍ) Adequacy.emptyMem e μ
        (K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))) →
      K.Catches n = false →
      ∀ {μ' : Heap} {t : Expr}, Steps (ℍ := ℍ) μ (.app (.val D) (.val .unit)) μ' t →
        ∀ (K' : Kont) (r : Bool) (m j : UInt32) (w : Val), t = K'.plug (opE r (opPayload m j w)) →
          OpFree r m K' → r = true ∧ FR m

/-- A finaliser that may raise fewer names runs alone at more. -/
theorem finAloneAt_mono {FR FR' : UInt32 → Prop} (hle : ∀ m, FR m → FR' m) {J : TypingJ}
    (h : FinAloneAt (ℍ := ℍ) FR J) : FinAloneAt (ℍ := ℍ) FR' J := by
  intro e A he μ K₀ K N D n i v hreach hK μ' t hD hirr
  rcases h he hreach hK hD hirr with hv | ⟨K', m, j, w, ht, hK', hm⟩
  · exact .inl hv
  · exact .inr ⟨K', m, j, w, ht, hK', hle m hm⟩

theorem rowNU_nil : Row.NU [] := fun _ _ _ h => by simp [Row.find] at h

/-! ### Runs and contexts -/

theorem _root_.BoCa.BoLo.Kont.comp_assoc :
    ∀ (K₁ K₂ K₃ : Kont), (K₁.comp K₂).comp K₃ = K₁.comp (K₂.comp K₃) := by
  intro K₁ K₂ K₃
  induction K₁ <;> simp_all [Kont.comp]

/-- A run from a term that takes no step stays there. -/
theorem steps_irr {μ μ₂ : Heap} {T R : Expr} (hirr : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ T μ' t)
    (h : Steps (ℍ := ℍ) μ T μ₂ R) : μ₂ = μ ∧ R = T := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | more h₁ _ => exact absurd h₁ (hirr _ _)

/-- A run between two different terms takes a first step. -/
theorem steps_first {μ μ₂ : Heap} {T R : Expr} (h : Steps (ℍ := ℍ) μ T μ₂ R) (hne : R ≠ T) :
    ∃ μ₁ T₁, Step1 (ℍ := ℍ) μ T μ₁ T₁ ∧ Steps (ℍ := ℍ) μ₁ T₁ μ₂ R := by
  cases h with
  | refl => exact absurd rfl hne
  | more h₁ h₂ => exact ⟨_, _, h₁, h₂⟩

/-- **Run splitting at an end that takes no step**: the inner term runs to a term that takes no
step, and the run goes on from the context around it. -/
theorem steps_plug_split_end (K : Kont) {μ μ' : Heap} {e E : Expr}
    (hs : Steps (ℍ := ℍ) μ (K.plug e) μ' E) (hE : ∀ μ'' E', ¬ Step1 (ℍ := ℍ) μ' E μ'' E') :
    ∃ μ₁ t, Steps (ℍ := ℍ) μ e μ₁ t ∧ (∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ t₂) ∧
      Steps (ℍ := ℍ) μ₁ (K.plug t) μ' E := by
  rcases steps_plug_split K hs with ⟨e', rfl, he'⟩ | h
  · exact ⟨μ', e', he', fun μ₂ t₂ h => hE _ _ (h.plug K), .refl _ _⟩
  · exact h

/-- A raise its context does not stop takes no step. -/
theorem raise_irr {μ : Heap} {K : Kont} {m j : UInt32} {w : Val} (hK : K.Catches m = false) :
    ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ (K.plug (raiseE (.val (opPayload m j w)))) μ' t :=
  fun _ _ h => opPlug_no_step (r := true) (payloadName_opPayload m j w) hK h

/-- A context that stops no raise of `n` holds no finaliser. -/
theorem fins_nil_of_catches {n : UInt32} : ∀ (K : Kont), K.Catches n = false → K.fins = []
  | .hole, _ => rfl
  | .appR f K, h => by
      rw [catches_appR, Bool.or_eq_false_iff] at h
      simp only [Kont.fins, fins_nil_of_catches K h.2, List.nil_append]
      split
      · simp [Kont.Catches] at h
      · rfl
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => fins_nil_of_catches K h

theorem noCtl_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).NoCtl ↔ K₁.NoCtl ∧ K₂.NoCtl := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, Kont.NoCtl]
  | appR f K ih => simp only [Kont.comp, Kont.NoCtl, ih]; tauto
  | _ => simp_all [Kont.comp, Kont.NoCtl]

/-- A stopping frame of a context with no handler, `ccatch` or `cfin` frame, at a name other than
`0`, is a finaliser frame. -/
theorem frame_ubind_of_unwind {n : UInt32} {f : Expr} {Ki : Kont} (hf : FrameCatches n f)
    (hn : n ≠ 0) (hH : (Kont.appR f Ki).hndNames = []) (hC : (Kont.appR f Ki).NoCtl) :
    ∃ x, f = .app (.prim .ubind) x := by
  simp only [FrameCatches, Kont.Catches, Bool.or_false] at hf
  simp only [Kont.hndNames, List.append_eq_nil_iff] at hH
  obtain ⟨⟨hc, hc'⟩, -⟩ := hC
  split at hf
  · simp at hH
  · exact ⟨_, rfl⟩
  · simp at hf; exact absurd hf hn
  · exact absurd rfl (hc' _)
  · simp at hf

/-- A stopping frame of `0`, in a context with no handler named `0` and no `ccatch` or `cfin`
frame, is a finaliser frame. -/
theorem frame_ubind_of_cancel {f : Expr} {Ki : Kont} (hf : FrameCatches 0 f)
    (hH : (Kont.appR f Ki).HasHnd 0 = false) (hC : (Kont.appR f Ki).NoCtl) :
    ∃ x, f = .app (.prim .ubind) x := by
  simp only [FrameCatches, Kont.Catches, Bool.or_false] at hf
  simp only [Kont.HasHnd, Bool.or_eq_false_iff] at hH
  obtain ⟨⟨hc, hc'⟩, -⟩ := hC
  split at hf
  · rename_i m r
    simp only [beq_iff_eq] at hf
    subst hf
    simp at hH
  · exact ⟨_, rfl⟩
  · exact absurd rfl hc
  · exact absurd rfl (hc' _)
  · simp at hf

/-- A finaliser frame stopping a raise: `[finalise]` at a raise of a name other than `0`,
`[finalise-cancel]` at a cancel. -/
theorem head_ubind_raise {μ μ' : Heap} {x : Expr} {Ki : Kont} {p : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p)))) μ' a') :
    μ' = μ ∧ ∃ N D : Val, x = (Val.pair N D).1 ∧
      ((∃ n i v, n ≠ 0 ∧ p = opPayload n i v ∧
          a' = .seq (.app (.val D) (.val .unit)) (raiseE (.val p))) ∨
       (∃ Ns err, p = cancelVal Ns err ∧
          a' = cfinE (cancelVal Ns err) (.app (.val D) (.val .unit)))) := by
  generalize hX : Expr.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p))) = X at h
  cases h with
  | ufin N D n i v K hn hK =>
      simp only [ubindE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, N, D, hx, .inl ⟨n, i, v, hn, rfl, rfl⟩⟩
  | ufinC N D Ns err K hK =>
      simp only [ubindE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, N, D, hx, .inr ⟨Ns, err, rfl, rfl⟩⟩
  | uthen N D w =>
      simp only [ubindE, Expr.app.injEq] at hX
      exact absurd hX.2 (plug_raise_ne_val _ _ _)
  | _ => simp_all [hndE, ccatchE, cfinE]

/-- `v; e` at a value other than `()` is a stuck redex. -/
theorem stuckAt_seq {w : Val} (hw : w.1 ≠ .unit) (e : Expr) : StuckAt (ℍ := ℍ) (.seq w.1 e) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.seq w.1 e = E at h
    cases h with
    | seq _ =>
        simp only [Expr.seq.injEq] at hE
        exact hw hE.1
    | _ => simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | seq K _ =>
        simp only [Kont.plug, Expr.seq.injEq] at h
        exact K.isVal_of_plug (by rw [← h.1]; exact w.2)
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-- A raise is never at an evaluation position of `v; e`. -/
theorem plug_raise_ne_seq_val {K K' : Kont} {q w : Val} {e : Expr} :
    K'.plug (raiseE (.val q)) ≠ K.plug (.seq (.val w) e) := by
  intro h
  rcases plug_cmp K' K (opE_not_isVal true q) not_isVal_seq h with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · have hK := plug_primApp (h₁.symm.trans (opE_eq_app true q)) not_isVal_seq
    subst hK
    simp [Kont.plug, opE, raiseE] at h₁
  · cases K'' with
    | hole => simp [Kont.plug, opE, raiseE] at h₁
    | seq K₃ e' =>
        simp only [Kont.plug, Expr.seq.injEq] at h₁
        exact plug_raise_ne_val K₃ q w h₁.1.symm
    | _ => simp [Kont.plug] at h₁

/-! ### The unwind -/

/-- A raise nothing stops: the run is empty. -/
theorem unwind_out {K K' : Kont} {μ μ₂ : Heap} {n i m j : UInt32} {v w : Val}
    (hK : K.Catches n = false)
    (hrun : Steps (ℍ := ℍ) μ (K.plug (raiseE (.val (opPayload n i v)))) μ₂
      (K'.plug (raiseE (.val (opPayload m j w))))) :
    UnwindRun (ℍ := ℍ) μ (K.plug (raiseE (.val (opPayload n i v)))) [] μ₂
      (K'.plug (raiseE (.val (opPayload m j w)))) := by
  obtain ⟨rfl, hR⟩ := steps_irr (raise_irr hK) hrun
  obtain ⟨rfl, hq⟩ := plug_raise_inj hR
  obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hq
  exact .out hK

/-- The finalisers of a context whose innermost stopping frame is a finaliser frame. -/
theorem fins_innerUbind {n : UInt32} {Ko Ki : Kont} {N D : Val} (hKi : Ki.Catches n = false) :
    (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).fins = D.1 :: Ko.fins := by
  rw [fins_comp]
  simp only [Kont.fins, fins_nil_of_catches Ki hKi, List.nil_append, Val.pair]
  rfl

theorem catches_innerUbind {n : UInt32} {Ko Ki : Kont} (x : Expr) :
    (Ko.comp (.appR (.app (.prim .ubind) x) Ki)).Catches n = true :=
  catches_of_innerCatch (by simp [FrameCatches, Kont.Catches])

/-- **The unwind through frames with no handler fires their finalisers once each, innermost
first**: `KA` holds no handler, `ccatch` or `cfin` frame, and `KB` stops nothing of the raise. -/
theorem unwindRun_of {J : TypingJ} (hF : FinAloneAt (ℍ := ℍ) (· ≠ 0) J) {e : Expr} {A : VTy}
    (he : J.closed e (.ret A)) (K₀ : Kont) :
    ∀ (k : ℕ) (KA KB : Kont) (μ : Heap) (n i : UInt32) (v : Val), KA.fins.length = k →
      KA.hndNames = [] → KA.NoCtl → KB.Catches n = false → n ≠ 0 →
      Steps (ℍ := ℍ) Adequacy.emptyMem e μ
        (K₀.plug ((KA.comp KB).plug (raiseE (.val (opPayload n i v))))) →
      ∀ μ₂ (K' : Kont) m j w, K'.Catches m = false →
        Steps (ℍ := ℍ) μ ((KA.comp KB).plug (raiseE (.val (opPayload n i v)))) μ₂
          (K'.plug (raiseE (.val (opPayload m j w)))) →
        UnwindRun (ℍ := ℍ) μ ((KA.comp KB).plug (raiseE (.val (opPayload n i v)))) KA.fins μ₂
          (K'.plug (raiseE (.val (opPayload m j w)))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro KA KB μ n i v hk hH hC hB hn hreach μ₂ K' m j w hK' hrun
  by_cases hA : KA.Catches n = true
  swap
  · simp only [Bool.not_eq_true] at hA
    rw [fins_nil_of_catches KA hA]
    exact unwind_out (by rw [catches_comp, hA, hB]; rfl) hrun
  obtain ⟨Ko, f, Ki, rfl, hKi, hf⟩ := innerCatch_exists n KA hA
  have hHo := (List.append_eq_nil_iff.1 ((hndNames_comp _ _).symm.trans hH))
  have hCo := (noCtl_comp _ _).1 hC
  obtain ⟨x, rfl⟩ := frame_ubind_of_unwind (Ki := Ki) hf hn hHo.2 hCo.2
  have hctx : (Ko.comp (.appR (.app (.prim .ubind) x) Ki)).comp KB =
      Ko.comp (.appR (.app (.prim .ubind) x) (Ki.comp KB)) := by
    rw [Kont.comp_assoc]; rfl
  have hKiB : (Ki.comp KB).Catches n = false := by rw [catches_comp, hKi, hB]; rfl
  have hIC : InnerCatch n ((Ko.comp (.appR (.app (.prim .ubind) x) Ki)).comp KB) Ko
      (.app (.prim .ubind) x) (Ki.comp KB) := ⟨hctx, hKiB, hf⟩
  have hne : K'.plug (raiseE (.val (opPayload m j w))) ≠
      ((Ko.comp (.appR (.app (.prim .ubind) x) Ki)).comp KB).plug
        (raiseE (.val (opPayload n i v))) := by
    intro h
    obtain ⟨rfl, hq⟩ := plug_raise_inj h
    obtain ⟨rfl, -, -⟩ := opPayload_inj hq
    rw [catches_comp, catches_innerUbind] at hK'
    simp at hK'
  obtain ⟨μ₁, T₁, hst, hrest⟩ := steps_first hrun hne
  obtain ⟨Ko', f', Ki', a', hIC', hhead, rfl⟩ := step1_raise (payloadName_opPayload n i v) hst
  obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
  obtain ⟨hμ, N, D, rfl, hcase⟩ := head_ubind_raise hhead
  subst μ₁
  rcases hcase with ⟨n', i', v', -, hp', rfl⟩ | ⟨Ns, err, hp', -⟩
  swap
  · exact absurd (opPayload_inj hp').1 hn
  clear hp'
  have hk' : Ko.fins.length < k := by
    rw [fins_innerUbind hKi] at hk; simp at hk; omega
  rw [fins_innerUbind hKi]
  have hT : ((Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).comp KB).plug
      (raiseE (.val (opPayload n i v))) =
      Ko.plug (ubindE (Val.pair N D) ((Ki.comp KB).plug (raiseE (.val (opPayload n i v))))) := by
    rw [hctx, Kont.plug_comp]; rfl
  rw [hT] at hreach hst ⊢
  have hrest' : Steps (ℍ := ℍ) μ ((Ko.comp (.seq .hole (raiseE (.val (opPayload n i v))))).plug
      (.app (.val D) (.val .unit))) μ₂ (K'.plug (raiseE (.val (opPayload m j w)))) := by
    rw [Kont.plug_comp]; exact hrest
  obtain ⟨μ₃, t, hD, hirr, hcont⟩ := steps_plug_split_end _ hrest' (raise_irr hK')
  have hfire : Steps (ℍ := ℍ) Adequacy.emptyMem e μ ((K₀.comp Ko).plug
      (ubindE (Val.pair N D) ((Ki.comp KB).plug (raiseE (.val (opPayload n i v)))))) := by
    rw [Kont.plug_comp]; exact hreach
  have hpre : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₃
      (K₀.plug ((Ko.comp (.seq .hole (raiseE (.val (opPayload n i v))))).plug t)) := by
    refine hreach.trans (.more (hst.plug K₀) ?_)
    have := Steps.plug (K₀.comp Ko) (Steps.plug (.seq .hole (raiseE (.val (opPayload n i v)))) hD)
    rw [Kont.plug_comp, Kont.plug_comp] at this
    rw [Kont.plug_comp]
    exact this
  rcases hF he hfire hKiB hD hirr with hval | ⟨K'', m', j', w', rfl, hK'', hm'⟩
  · obtain ⟨w', rfl⟩ : ∃ w' : Val, t = w'.1 := ⟨⟨t, hval⟩, rfl⟩
    by_cases hu : w'.1 = .unit
    · have hseq : Head (ℍ := ℍ) μ₃ (.seq (.val w') (raiseE (.val (opPayload n i v)))) μ₃
          (raiseE (.val (opPayload n i v))) := by
        have := Head.seq (ℍ := ℍ) μ₃ (raiseE (.val (opPayload n i v)))
        simp only [Expr.val] at this ⊢; rw [hu]; exact this
      rw [Kont.plug_comp] at hcont hpre
      have hne' : K'.plug (raiseE (.val (opPayload m j w))) ≠
          Ko.plug ((Kont.seq .hole (raiseE (.val (opPayload n i v)))).plug w'.1) :=
        plug_raise_ne_seq_val
      obtain ⟨μ₄, T₄, hst₄, hrest₄⟩ := steps_first hcont hne'
      obtain ⟨hμ₄, rfl⟩ := step1_det hseq rfl hst₄
      subst μ₄
      have hD' : Steps (ℍ := ℍ) μ (.seq (.app (.val D) (.val .unit))
          (raiseE (.val (opPayload n i v)))) μ₃
          (Kont.hole.plug (raiseE (.val (opPayload n i v)))) :=
        (Steps.plug (.seq .hole _) hD).trans (Steps.one (Step1.head hseq))
      refine .fin (Kd := .hole) hn hKiB hD' rfl ?_
      rw [Kont.comp_hole]
      have h' := ih Ko.fins.length hk' Ko .hole μ₃ n i v rfl hHo.1 hCo.1 rfl hn
        (by rw [Kont.comp_hole]; exact hpre.trans (.more (hst₄.plug K₀) (.refl _ _)))
        μ₂ K' m j w hK' (by rw [Kont.comp_hole]; exact hrest₄)
      rw [Kont.comp_hole] at h'
      exact h'
    · exfalso
      rw [Kont.plug_comp] at hcont
      obtain ⟨-, hR⟩ := steps_irr (fun _ _ => stuck_no_step (stuckAt_seq hu _) Ko) hcont
      exact plug_raise_ne_seq_val hR
  · have hD' : Steps (ℍ := ℍ) μ (.seq (.app (.val D) (.val .unit))
        (raiseE (.val (opPayload n i v)))) μ₃
        ((Kont.seq K'' (raiseE (.val (opPayload n i v)))).plug
          (raiseE (.val (opPayload m' j' w')))) :=
      Steps.plug (.seq .hole _) hD
    have hplug : (Ko.comp (.seq .hole (raiseE (.val (opPayload n i v))))).plug
        (K''.plug (raiseE (.val (opPayload m' j' w')))) =
        (Ko.comp (.seq K'' (raiseE (.val (opPayload n i v))))).plug
          (raiseE (.val (opPayload m' j' w'))) := by
      rw [Kont.plug_comp, Kont.plug_comp]; rfl
    rw [hplug] at hcont hpre
    exact .fin (Kd := .seq K'' (raiseE (.val (opPayload n i v)))) hn hKiB hD' hK''
      (ih Ko.fins.length hk' Ko (.seq K'' (raiseE (.val (opPayload n i v)))) μ₃ m' j' w' rfl hHo.1
        hCo.1 hK'' hm' hpre μ₂ K' m j w hK' hcont)


/-- **I3.b, unwind, given `FinAloneAt`.** -/
theorem unwindOrder_at {J : TypingJ} (hF : FinAloneAt (ℍ := ℍ) (· ≠ 0) J) : UnwindOrder (ℍ := ℍ) J := by
  intro e A he μ₁ K₀ K n i v hH hC hn hreach μ₂ K' m j w hK' hrun
  have h := unwindRun_of hF he K₀ K.fins.length K .hole μ₁ n i v rfl hH hC rfl hn
    (by rw [Kont.comp_hole]; exact hreach) μ₂ K' m j w hK' (by rw [Kont.comp_hole]; exact hrun)
  rw [Kont.comp_hole] at h
  exact h


/-! ### The cancel -/

/-- Cancelling `κ` reaches `cancelOf n H K` by `ewp_kappa_cancel`'s three steps. -/
theorem kappa_cancel_run (μ : Heap) (n : UInt32) (H : Val) (K : Kont) :
    Steps (ℍ := ℍ) μ (.app (kappa n H K) (.val (Val.inj₂ .unit))) μ (cancelOf n H K) := by
  refine .more (Step1.head (Head.beta μ _ _)) ?_
  refine .more (Step1.head (Head.case₂ μ Val.unit _ _)) ?_
  refine .more (Step1.head (Head.seq μ _)) ?_
  have e : ∀ (s u : Val), Expr.subst 0 u (Expr.subst 1 s
      (ccatchE (hndE (Val.shift 2 0 H) ((Kont.shift 2 0 K).plug
        (raiseE (.val (cancelVal (n :: K.hndNames) none))))))) =
      ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none))))) := by
    intro s u
    simp only [ccatchE, hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 1 0 1 s H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 u H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 1 K 0 1 s _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 u _ (by omega) (by omega), Kont.shift_zero]
    simp only [raiseE, Expr.subst, Expr.val, subst_cancelVal_none, Val.prim]
  rw [show (0 + 1 : Nat) = 1 from rfl, e]
  exact .refl _ _

/-- A raise at the top takes no step. -/
theorem raise_top_irr {μ : Heap} {E : Val} : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ (raiseE (.val E)) μ' t := by
  rintro μ' t ⟨K, a, a', h, -, hh⟩
  rcases plug_cmp .hole K (opE_not_isVal true E) hh.not_isVal h with ⟨K'', h₁, -⟩ | ⟨K'', h₁, h₂⟩
  · have h₁' : K''.plug a = .app (.val (.prim .raise)) (.val E) := h₁.symm
    have hK := plug_primApp h₁' hh.not_isVal
    subst hK
    simp only [Kont.plug] at h₁'
    rw [h₁'] at hh
    exact not_head_raise hh
  · obtain ⟨rfl, rfl⟩ := comp_eq_hole h₂.symm
    simp only [Kont.plug] at h₁
    subst h₁
    exact not_head_raise hh

theorem val_irr {μ : Heap} {w : Val} : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ (.val w) μ' t :=
  fun _ _ h => BoCa.BoLo.no_step_val h

/-- A context whose handlers are named nonzero has no handler of `0`. -/
theorem hasHnd0_of_knz : ∀ (K : Kont), KNZ K → K.HasHnd 0 = false := by
  intro K
  induction K with
  | hole => intro _; rfl
  | appR f K ih =>
      intro hK
      simp only [KNZ, Kont.plug] at hK
      rw [hndNZ_app] at hK
      simp only [Kont.HasHnd, Bool.or_eq_false_iff]
      rcases hK with ⟨rfl, m, r, hpr, hm, hr⟩ | ⟨hf, hf', hK⟩
      · obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_namePair (notNameLike_var 0) hpr
        refine ⟨rfl, ih ?_⟩
        simp only [KNZ, Kont.plug, Expr.HndNamesNZ]
        exact ⟨by show v.1.HndNamesNZ; rw [hv]; simp [Expr.HndNamesNZ], hr⟩
      · refine ⟨?_, ih hK⟩
        split
        · rename_i m r
          rw [hndNZ_app] at hf'
          rcases hf' with ⟨-, m', r', hpr', hm', -⟩ | ⟨h, -, -⟩
          · simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hpr'
            obtain ⟨rfl, rfl⟩ := hpr'
            simpa using hm'
          · exact absurd rfl h
        · rfl
  | pairL K e ih =>
      intro hK; exact ih (by simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK; exact hK.1)
  | pairR v K ih =>
      intro hK; exact ih (by simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK; exact hK.2)
  | letpair K e ih =>
      intro hK; exact ih (by simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK; exact hK.1)
  | case K e₁ e₂ ih =>
      intro hK; exact ih (by simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK; exact hK.1)
  | appL K v ih =>
      intro hK
      simp only [KNZ, Kont.plug] at hK
      rw [hndNZ_app] at hK
      rcases hK with ⟨h, -⟩ | ⟨-, hK, -⟩
      · exact absurd h (plug_ne_prim (fun _ h => by cases h) _)
      · exact ih hK
  | seq K e ih =>
      intro hK; exact ih (by simp only [KNZ, Kont.plug, Expr.HndNamesNZ] at hK; exact hK.1)
  | inj₁ K ih => intro hK; exact ih hK
  | inj₂ K ih => intro hK; exact ih hK

/-- The `ccatch` frame. -/
abbrev ccatchK (K : Kont) : Kont := .appR (.prim .ccatch) K

/-- **A cancel run through frames with no `ccatch`, no `cfin` and no handler of `0` fires their
finalisers once each, innermost first.** -/
theorem cancelRun_of {J : TypingJ} (hF : FinAloneAt (ℍ := ℍ) (· ≠ 0) J) {e : Expr} {A : VTy}
    (he : J.closed e (.ret A)) (K₀ : Kont) (Ns : List UInt32) :
    ∀ (k : ℕ) (Kc : Kont) (μ : Heap) (err : Option Val), Kc.fins.length = k →
      Kc.NoCtl → Kc.HasHnd 0 = false →
      Steps (ℍ := ℍ) Adequacy.emptyMem e μ
        (K₀.plug (ccatchE (Kc.plug (raiseE (.val (cancelVal Ns err)))))) →
      ∀ μ₃ r, Steps (ℍ := ℍ) μ (ccatchE (Kc.plug (raiseE (.val (cancelVal Ns err))))) μ₃ r →
        (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
        CancelRun (ℍ := ℍ) μ (ccatchE (Kc.plug (raiseE (.val (cancelVal Ns err))))) Kc.fins μ₃
          r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Kc μ err hk hC hH hreach μ₃ r hrun hr
  have hrirr : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ₃ r μ' t := by
    rcases hr with rfl | ⟨E, rfl⟩
    · exact val_irr (w := Val.unit)
    · exact raise_top_irr
  have hne : r ≠ ccatchE (Kc.plug (raiseE (.val (cancelVal Ns err)))) := by
    rcases hr with rfl | ⟨E, rfl⟩
    · simp [ccatchE]
    · simp [ccatchE, raiseE]
  obtain ⟨μ₁, T₁, hst, hrest⟩ := steps_first hrun hne
  obtain ⟨Ko', f', Ki', a', hIC', hhead, rfl⟩ :=
    step1_raise (K := ccatchK Kc) (payloadName_cancelVal Ns err) hst
  by_cases hA : Kc.Catches 0 = true
  swap
  · -- the canceller answers
    simp only [Bool.not_eq_true] at hA
    have hIC : InnerCatch 0 (ccatchK Kc) .hole (.prim .ccatch) Kc :=
      ⟨rfl, hA, by simp [FrameCatches, Kont.Catches]⟩
    obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
    rw [fins_nil_of_catches Kc hA]
    have hcase : μ₁ = μ ∧ a' = cancelAnswer err := by
      clear hrun hrest hreach hst ih hrirr hne hIC hIC' hr hk hC hH
      generalize hX : Expr.app (.prim .ccatch) (Kc.plug (raiseE (.val (cancelVal Ns err)))) = X
        at hhead
      cases hhead with
      | cancel Ns' K₀' hK₀' =>
          simp only [ccatchE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
          obtain ⟨-, hp⟩ := plug_raise_inj hX
          obtain ⟨rfl, rfl⟩ := cancelVal_inj hp
          exact ⟨rfl, rfl⟩
      | creraise Ns' E K₀' hK₀' =>
          simp only [ccatchE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
          obtain ⟨-, hp⟩ := plug_raise_inj hX
          obtain ⟨rfl, rfl⟩ := cancelVal_inj hp
          exact ⟨rfl, rfl⟩
      | _ => simp_all [hndE, ubindE, cfinE]
    obtain ⟨hμ₁, rfl⟩ := hcase
    subst μ₁
    have hirr' : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ (Kont.hole.plug (cancelAnswer err)) μ' t := by
      cases err with
      | none => exact val_irr (w := Val.unit)
      | some E => exact raise_top_irr
    obtain ⟨rfl, rfl⟩ := steps_irr hirr' hrest
    exact .caught hA
  -- a finaliser frame stops the cancel
  obtain ⟨Ko, f, Ki, rfl, hKi, hf⟩ := innerCatch_exists 0 Kc hA
  have hHo : Ko.HasHnd 0 = false ∧ (Kont.appR f Ki).HasHnd 0 = false := by
    rw [hasHnd_comp, Bool.or_eq_false_iff] at hH; exact hH
  have hCo := (noCtl_comp _ _).1 hC
  obtain ⟨x, rfl⟩ := frame_ubind_of_cancel hf hHo.2 hCo.2
  have hIC : InnerCatch 0 (ccatchK (Ko.comp (.appR (.app (.prim .ubind) x) Ki))) (ccatchK Ko)
      (.app (.prim .ubind) x) Ki := ⟨rfl, hKi, hf⟩
  obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
  obtain ⟨hμ, N, D, rfl, hcase⟩ := head_ubind_raise hhead
  subst μ₁
  rcases hcase with ⟨n', i', v', hn', hp', -⟩ | ⟨Ns', err', hp', rfl⟩
  · exact absurd (opPayload_inj hp').1.symm hn'
  obtain ⟨rfl, rfl⟩ := cancelVal_inj hp'
  have hk' : Ko.fins.length < k := by
    rw [fins_innerUbind hKi] at hk; simp at hk; omega
  rw [fins_innerUbind hKi]
  have hT : ccatchE ((Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).plug
      (raiseE (.val (cancelVal Ns err)))) =
      ccatchE (Ko.plug (ubindE (Val.pair N D) (Ki.plug (raiseE (.val (cancelVal Ns err)))))) := by
    rw [Kont.plug_comp]; rfl
  rw [hT] at hreach hst ⊢
  -- the finaliser's run under `cfin`
  have hrest' : Steps (ℍ := ℍ) μ (((ccatchK Ko).comp
      (.appR (.app (.prim .cfin) (cancelVal Ns err).1) .hole)).plug (.app (.val D) (.val .unit)))
      μ₃ r := by
    rw [Kont.plug_comp]; exact hrest
  obtain ⟨μ₂, t, hD, hirr, hcont⟩ := steps_plug_split_end _ hrest' hrirr
  have hfire : Steps (ℍ := ℍ) Adequacy.emptyMem e μ ((K₀.comp (ccatchK Ko)).plug
      (ubindE (Val.pair N D) (Ki.plug (raiseE (.val (opPayload 0 0
        (Val.pair (BoCa.BoLo.namesVal Ns) (BoCa.BoLo.errVal err)))))))) := by
    rw [Kont.plug_comp]; exact hreach
  have hpre : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₂
      (K₀.plug (((ccatchK Ko).comp (.appR (.app (.prim .cfin) (cancelVal Ns err).1) .hole)).plug
        t)) := by
    refine hreach.trans (.more (hst.plug K₀) ?_)
    have := Steps.plug (K₀.comp ((ccatchK Ko).comp
      (.appR (.app (.prim .cfin) (cancelVal Ns err).1) .hole))) hD
    simp only [Kont.plug_comp] at this ⊢
    exact this
  rw [Kont.plug_comp] at hcont hpre
  rcases hF he hfire hKi hD hirr with hval | ⟨K'', m, j, w, rfl, hK'', -⟩
  · -- the finaliser returned: `[cfin-ret]`
    obtain ⟨w, rfl⟩ : ∃ w : Val, t = w.1 := ⟨⟨t, hval⟩, rfl⟩
    have hret := Head.cfret (ℍ := ℍ) μ₂ Ns err w
    have hne' : r ≠ (ccatchK Ko).plug (cfinE (cancelVal Ns err) (.val w)) := by
      rcases hr with rfl | ⟨E, rfl⟩
      · simp [Kont.plug]
      · simp [Kont.plug, raiseE]
    obtain ⟨μ₄, T₄, hst₄, hrest₄⟩ := steps_first hcont hne'
    obtain ⟨hμ₄, rfl⟩ := step1_det hret rfl hst₄
    subst μ₄
    have hD' : Steps (ℍ := ℍ) μ (cfinE (cancelVal Ns err) (.app (.val D) (.val .unit))) μ₂
        (raiseE (.val (cancelVal Ns err))) :=
      (Steps.plug (.appR (.app (.prim .cfin) (cancelVal Ns err).1) .hole) hD).trans
        (Steps.one (Step1.head hret))
    exact .fin hKi hD' (ih Ko.fins.length hk' Ko μ₂ err rfl hCo.1 hHo.1
      (hpre.trans (.more (hst₄.plug K₀) (.refl _ _))) μ₃ r hrest₄ hr)
  · -- the finaliser raised: `[cfin-raise]`
    have hraise := Head.cferr (ℍ := ℍ) μ₂ Ns err m j w K'' hK''
    have hne' : r ≠ (ccatchK Ko).plug (cfinE (cancelVal Ns err)
        (K''.plug (raiseE (.val (opPayload m j w))))) := by
      rcases hr with rfl | ⟨E, rfl⟩
      · simp [Kont.plug]
      · simp [Kont.plug, raiseE]
    obtain ⟨μ₄, T₄, hst₄, hrest₄⟩ := steps_first hcont hne'
    obtain ⟨hμ₄, rfl⟩ := step1_det hraise rfl hst₄
    subst μ₄
    have hD' : Steps (ℍ := ℍ) μ (cfinE (cancelVal Ns err) (.app (.val D) (.val .unit))) μ₂
        (raiseE (.val (cancelVal Ns (BoCa.BoLo.errNext Ns err m j w)))) :=
      (Steps.plug (.appR (.app (.prim .cfin) (cancelVal Ns err).1) .hole) hD).trans
        (Steps.one (Step1.head hraise))
    exact .fin hKi hD' (ih Ko.fins.length hk' Ko μ₂ _ rfl hCo.1 hHo.1
      (hpre.trans (.more (hst₄.plug K₀) (.refl _ _))) μ₃ r hrest₄ hr)

/-- **I3.b, cancel, given `NoInterception` and `FinAloneAt`.** -/
theorem cancelOrder_at {J : TypingJ} (hN : NoInterception J) (hF : FinAloneAt (ℍ := ℍ) (· ≠ 0) J) :
    CancelOrder (ℍ := ℍ) J := by
  intro e A he μ₁ K₀ n H K hC hreach μ₃ r hrun hr
  have hreach' : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (cancelOf n H K)) :=
    hreach.trans (Steps.plug K₀ (kappa_cancel_run μ₁ n H K))
  have hnz := (hndNamesNZ_steps hreach' (hN _ _ _ _ _ he).2.2 heapNZ_empty).1
  have hc : (cancelOf n H K).HndNamesNZ :=
    (plug_hndNZ_inv K₀ ⟨fun _ _ h => by simp [cancelOf, ccatchE] at h,
      fun _ h => by simp [cancelOf, ccatchE] at h⟩ hnz).2
  simp only [cancelOf] at hc
  rw [hndNZ_ccatchE] at hc
  have hc' := hndNZ_app_inv (f := .app (.prim .hnd) H.1) (by simp) hc
  have hH0 : (Kont.appR (.app (.prim .hnd) H.1) .hole).HasHnd 0 = false := by
    have h := hc'.1
    rw [hndNZ_app] at h
    rcases h with ⟨-, m, r', hpr, hm, -⟩ | ⟨h, -, -⟩
    · simp only [Kont.HasHnd, hpr, Bool.or_false]; simpa using hm
    · exact absurd rfl h
  have hK0 : K.HasHnd 0 = false :=
    hasHnd0_of_knz K (plug_hndNZ_inv K (notNameLike_raise _) hc'.2).1
  have hCc : ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp K).NoCtl :=
    (noCtl_comp _ _).2 ⟨⟨⟨by simp, fun _ h => by simp at h⟩, trivial⟩, hC⟩
  have hHc : ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp K).HasHnd 0 = false := by
    rw [hasHnd_comp, hH0, hK0]; rfl
  have hfins : ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp K).fins = K.fins := by
    rw [fins_comp]; simp [Kont.fins]
  have h := cancelRun_of hF he K₀ (n :: K.hndNames) _ _ μ₁ none rfl hCc hHc hreach' μ₃ r hrun hr
  rw [hfins] at h
  exact h

/-- **I3.b given `NoInterception` and `FinAloneAt`** at today's endings (raises of nonzero
names). -/
theorem finaliserOrder_at {J : TypingJ} (hN : NoInterception J)
    (hF : FinAloneAt (ℍ := ℍ) (· ≠ 0) J) : FinaliserOrder (ℍ := ℍ) J :=
  ⟨cancelOrder_at hN hF, unwindOrder_at hF⟩

/-- **I3.b at option A** (decision D3): given `NoInterception` and that a fired finaliser's run
alone ends at a value. -/
theorem finaliserOrder_A {J : TypingJ} (hN : NoInterception J)
    (hF : FinAloneAt (ℍ := ℍ) (fun _ => False) J) : FinaliserOrder (ℍ := ℍ) J :=
  finaliserOrder_at hN (finAloneAt_mono (fun _ h => h.elim) hF)

end Targets

end
