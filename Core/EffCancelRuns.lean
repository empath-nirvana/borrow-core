import Core.RaiseNames
import Core.EffSafety
import Core.EffCancelTyped

/-!
# Core — the runs of an unwind and of a cancel  `[spec §19, §27]`

The order in which an unwind and a cancel fire the finalisers of the frames they pass, stated of
Core's machine.  A *path* is the list of configurations a run passes through (`Path`); every run
is one (`path_of_steps`).

* **Where a raise is stopped.**  A step at `K[raise p]` is the step of the innermost frame of `K`
  that stops `p`'s name (`step1_raise`); that frame is unique (`innerCatch_unique`).  In a context
  with no running finaliser's `cfin` frame it is a handler of the name or a finaliser frame
  (`frame_of_unwind`).  For a cancel in a region with no handler of `0` and no `ccatch` frame, it
  is a finaliser frame or a `cfin` frame (`frame_of_cancel`).
* **The unwind, read prefix-closed** (`unwind_prefix`).  Take a raise of a nonzero name pending
  under `K`.  Every path from there is a prefix of the unwind trace (`UnwindTr`).  `K`'s finalisers
  fire innermost first: `[finalise]`, then `D ()` runs alone.  A finaliser that returns `()` hands
  the raise on; one whose own raise escapes supersedes it.  The trace is over where a handler of
  the raise's name catches it, or where the raise leaves `K`.
* **The cancel, read prefix-closed, under frame deadness** (`cancel_prefix`).  The start is the
  cancel run of a continuation `kappa H K`, or of `kappaC hasCancel ℓ H K` after its cell's release.
  Every path from there is a prefix of the cancel trace of the dead region `K†` (`CancelTr`).
  `K†` holds no handler and no `ccatch` frame (`hasHnd_dead`, `noCC_dead`), so nothing in the
  region intercepts the cancel.  It fires `K`'s finalisers innermost first, each by
  `[finalise-cancel]` and then running alone under `cfin` to `[cfin-ret]` or `[cfin-raise]`.  It
  passes a running finaliser's `cfin` by `[cfin-cancel]`, that error first (`pend`).  The first
  kept error wins, and the canceller gets `()` or the kept error re-raised.  For a term a tied
  derivation types, every kept error is of a name of its effect context (`CancelsNamed`).
* **What S5 reads of a fired finaliser** (`FinRow FR`): `D ()` is a closed computation at a row of
  abortive operations of names in `FR`.  Typing gives that it runs alone from every memory with
  finitely many cells, to `()` or to an uncaught raise of such a name (`finAlone_of_finRow`); at
  option A, to `()` (`finOK_of_finRow`).  The memory's cells are `wpG`'s frame (`ownWorld`), and
  every run is a prefix of `wpG`'s (`wpG_seg`).  A finaliser that performs an operation a handler
  outside it answers (§27) is not covered.
* **Complete runs** (`finaliserOrder_at`).  Suppose each finaliser a program's runs fire runs alone
  to a value or to an uncaught raise of a nonzero name (`FinAloneAt`).  Then every complete cancel
  run of `kappa H K`, `K` free of `ccatch` and `cfin`, fires `K`'s finalisers innermost first
  (`CancelRun`).  So does every complete unwind through frames with no handler (`UnwindRun`).
* **Programs.**  `supersedeE`, `(raise 1) then x. x unwind raise 2`, meets `unwind_prefix`'s
  hypotheses (`supersede_prefix`), and its fired finaliser runs alone to its raise of `2`
  (`finAloneAt_supersedeE`), so `finaliserOrder_at` holds of it (`supersede_finaliserOrder`).
  `progOutT` (`Core/EffCancelTyped.lean`) is typed by a tied derivation (`dAt_progOutT`), its run
  cancels `κ` (`progOutT_cancels`), and its region's finaliser raises `2`: it meets
  `cancel_prefix`'s hypotheses (`progOutT_cancel_prefix`).  So does `progOutTA`, the same program
  at a cancellable raise of `2` (`progOutTA_cancel_prefix`): a tied derivation types it at `Ξ₁₂A`,
  which has no unrestricted abortive operation (`dAt_progOutTA`, `noUnrExn_Ξ₁₂A`), the shape the
  checker gives every program it accepts (`checkProgram_tiedAt`, `Frontend/Check/Program.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal errVal errNext kappa kappaC freeE Alloc ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx)

/-! ### The finalisers of a context, and the cancel branch -/

/-- The finalisers of `K`'s finaliser frames `ubind (N, D) □`, innermost first.  In `.appR f K`
the frame `f` is outside `K`.  `[spec §19]` -/
def _root_.BoCa.BoLo.Kont.fins : Kont → List Expr
  | .hole => []
  | .appR f K => K.fins ++ (match f with
      | .app (.prim .ubind) (.pair _ D) => [D]
      | _ => [])
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.fins

theorem fins_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).fins = K₂.fins ++ K₁.fins
  | .hole, _ => by simp [Kont.comp, Kont.fins]
  | .appR f K, K₂ => by simp only [Kont.comp, Kont.fins, fins_comp K K₂, List.append_assoc]
  | .pairL K _, K₂ | .pairR _ K, K₂ | .letpair K _, K₂ | .case K _ _, K₂ | .appL K _, K₂
  | .seq K _, K₂ | .inj₁ K, K₂ | .inj₂ K, K₂ => by simp only [Kont.comp, Kont.fins, fins_comp K K₂]

/-- **`κ`'s cancel branch after its three administrative steps**: the dead region `K†` run from the
cancel `raise (0, (0, none))` under its delimiter (`kappa_cancel_steps`).  `[spec §19]` -/
def cancelOf (K : Kont) : Expr :=
  ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))

/-- A dead region keeps the region's finaliser frames. -/
theorem fins_dead : ∀ K : Kont, K.dead.fins = K.fins
  | .hole => rfl
  | .appR f K => by
      simp only [Kont.dead]
      split
      · rename_i hf
        rw [fins_dead K]
        simp only [Kont.fins]
        split
        · simp [Kont.DeadFrame] at hf
        · simp
      · simp only [Kont.fins, fins_dead K]
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => by simp only [Kont.dead, Kont.fins, fins_dead K]

theorem catches_appR (n : UInt32) (f : Expr) (K : Kont) :
    (Kont.appR f K).Catches n = ((Kont.appR f .hole).Catches n || K.Catches n) := by
  simp only [Kont.Catches, Bool.or_false]

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

theorem _root_.BoCa.BoLo.Kont.comp_assoc :
    ∀ (K₁ K₂ K₃ : Kont), (K₁.comp K₂).comp K₃ = K₁.comp (K₂.comp K₃) := by
  intro K₁ K₂ K₃
  induction K₁ <;> simp_all [Kont.comp]

/-! ### Contexts with no cancel delimiter, no running finaliser -/

/-- `K` has no `ccatch` and no `cfin` frame.  `[spec §19]` -/
def _root_.BoCa.BoLo.Kont.NoCtl : Kont → Prop
  | .hole => True
  | .appR f K => (f ≠ .prim .ccatch ∧ ∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoCtl
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCtl

theorem noCtl_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).NoCtl ↔ K₁.NoCtl ∧ K₂.NoCtl := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, Kont.NoCtl]
  | appR f K ih => simp only [Kont.comp, Kont.NoCtl, ih]; tauto
  | _ => simp_all [Kont.comp, Kont.NoCtl]

/-- The dead region of a context with no `ccatch` and no `cfin` frame has none either. -/
theorem noCtl_dead : ∀ {K : Kont}, K.NoCtl → K.dead.NoCtl
  | .hole, h => h
  | .appR f K, h => by
      simp only [Kont.dead]
      split
      · exact noCtl_dead h.2
      · exact ⟨h.1, noCtl_dead h.2⟩
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => noCtl_dead (K := K) h

/-- `K` has no `ccatch` frame: no delimiter of a cancel in progress.  `[spec §19]` -/
def _root_.BoCa.BoLo.Kont.NoCC : Kont → Prop
  | .hole => True
  | .appR f K => f ≠ .prim .ccatch ∧ K.NoCC
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCC

theorem noCC_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).NoCC ↔ K₁.NoCC ∧ K₂.NoCC := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, Kont.NoCC]
  | appR f K ih => simp only [Kont.comp, Kont.NoCC, ih]; tauto
  | _ => simp_all [Kont.comp, Kont.NoCC]

/-- **A dead region holds no `ccatch` frame**: a cancel delimiter of the region is a frame the
cancel kills. -/
theorem noCC_dead : ∀ K : Kont, K.dead.NoCC
  | .hole => trivial
  | .appR f K => by
      simp only [Kont.dead]
      split
      · exact noCC_dead K
      · rename_i hf
        refine ⟨fun h => ?_, noCC_dead K⟩
        subst h
        simp [Kont.DeadFrame] at hf
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => noCC_dead K

/-- `K` has no `cfin` frame: no finaliser of a cancel runs inside it.  `[spec §19]` -/
def _root_.BoCa.BoLo.Kont.NoCfin : Kont → Prop
  | .hole => True
  | .appR f K => (∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoCfin
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCfin

theorem noCfin_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).NoCfin ↔ K₁.NoCfin ∧ K₂.NoCfin := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, Kont.NoCfin]
  | appR f K ih => simp only [Kont.comp, Kont.NoCfin, ih]; tauto
  | _ => simp_all [Kont.comp, Kont.NoCfin]

/-- A context that stops no raise of `n` holds no `cfin` frame, which stops every raise. -/
theorem noCfin_of_catches {n : UInt32} : ∀ (K : Kont), K.Catches n = false → K.NoCfin
  | .hole, _ => trivial
  | .appR f K, h => by
      rw [catches_appR, Bool.or_eq_false_iff] at h
      refine ⟨fun s hs => ?_, noCfin_of_catches K h.2⟩
      subst hs
      simp [Kont.Catches] at h
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => noCfin_of_catches K h

/-! ### Where a raise is stopped -/

/-- The frame `f □` stops a raise of `n`. -/
abbrev FrameCatches (n : UInt32) (f : Expr) : Prop := (Kont.appR f .hole).Catches n = true

/-- **The innermost frame of `K` that stops a raise of `n`**: `K` is `Ko` around the frame `f`
around `Ki`, and no frame of `Ki` stops it. -/
def InnerCatch (n : UInt32) (K Ko : Kont) (f : Expr) (Ki : Kont) : Prop :=
  K = Ko.comp (.appR f Ki) ∧ Ki.Catches n = false ∧ FrameCatches n f

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
    subst h₁
    obtain ⟨f, K₁, rfl, hf, hK₁, -⟩ := head_raise_ctx hp hh
    exact ⟨Kx, f, K₁, a', ⟨rfl, hK₁, hf⟩, hh, rfl⟩

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

/-- A raise at the top takes no step. -/
theorem raise_top_irr {μ : Heap} {E : Val} :
    ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ (raiseE (.val E)) μ' t := by
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

/-- A value takes no step. -/
theorem val_irr {μ : Heap} {w : Val} : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ (.val w) μ' t :=
  fun _ _ h => BoCa.BoLo.no_step_val h

/-- A step at a redex that allocates nothing is the redex's head step. -/
theorem step1_det {μ μ₁ μ' : Heap} {K : Kont} {a a₁ T : Expr} (hh : Head (ℍ := ℍ) μ a μ₁ a₁)
    (hn : a.allocs = false) (h : Step1 (ℍ := ℍ) μ (K.plug a) μ' T) : μ' = μ₁ ∧ T = K.plug a₁ :=
  (step1Only_plug hh hn K).2 _ _ h

/-! ### The frame that stops a raise or a cancel -/

/-- A finaliser frame stopping a raise: `[finalise]` at a raise of a name other than `0`,
`[finalise-cancel]` at a cancel. -/
theorem head_ubind_raise {μ μ' : Heap} {x : Expr} {Ki : Kont} {p : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p)))) μ' a') :
    μ' = μ ∧ ∃ N D : Val, x = (Val.pair N D).1 ∧
      ((∃ n i v, n ≠ 0 ∧ p = opPayload n i v ∧
          a' = .seq (.app (.val D) (.val .unit)) (raiseE (.val p))) ∨
       (∃ err, p = cancelVal err ∧
          a' = cfinE (cancelVal err) (.app (.val D) (.val .unit)))) := by
  generalize hX : Expr.app (.app (.prim .ubind) x) (Ki.plug (raiseE (.val p))) = X at h
  cases h with
  | ufin N D n i v K hn hK =>
      simp only [ubindE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, N, D, hx, .inl ⟨n, i, v, hn, rfl, rfl⟩⟩
  | ufinC N D err K hK =>
      simp only [ubindE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, N, D, hx, .inr ⟨err, rfl, rfl⟩⟩
  | uthen N D w =>
      simp only [ubindE, Expr.app.injEq] at hX
      exact absurd hX.2 (plug_raise_ne_val _ _ _)
  | _ => simp_all [hndE, ccatchE, cfinE]

/-- A running finaliser's `cfin` frame stopping a raise: `[cfin-raise]` at a name other than `0`,
`[cfin-cancel]` at a cancel; its state is a cancel's. -/
theorem head_cfin_raise {μ μ' : Heap} {x : Expr} {Ki : Kont} {p : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.app (.prim .cfin) x) (Ki.plug (raiseE (.val p)))) μ' a') :
    μ' = μ ∧ ∃ err : Option Val, x = (cancelVal err).1 ∧
      ((∃ m j w, m ≠ 0 ∧ p = opPayload m j w ∧
          a' = raiseE (.val (cancelVal (errNext err m j w)))) ∨
       (∃ err', p = cancelVal err' ∧ a' = raiseE (.val (cancelVal (err.or err'))))) := by
  generalize hX : Expr.app (.app (.prim .cfin) x) (Ki.plug (raiseE (.val p))) = X at h
  cases h with
  | cfret err w =>
      simp only [cfinE, Expr.app.injEq] at hX
      exact absurd hX.2 (plug_raise_ne_val _ _ _)
  | cferr err m j w K hm hK =>
      simp only [cfinE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, err, hx, .inl ⟨m, j, w, hm, rfl, rfl⟩⟩
  | cfcancel err err' K hK =>
      simp only [cfinE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
      obtain ⟨hx, hb⟩ := hX
      obtain ⟨-, rfl⟩ := plug_raise_inj hb
      exact ⟨rfl, err, hx, .inr ⟨err', rfl, rfl⟩⟩
  | _ => simp_all [hndE, ccatchE, ubindE]

/-- A stopping frame of a context with no handler, `ccatch` or `cfin` frame, at a name other than
`0`, is a finaliser frame. -/
theorem frame_ubind_of_unwind {n : UInt32} {f : Expr} {Ki : Kont} (hf : FrameCatches n f)
    (hn : n ≠ 0) (hH : ∀ m, (Kont.appR f Ki).HasHnd m = false) (hC : (Kont.appR f Ki).NoCtl) :
    ∃ x, f = .app (.prim .ubind) x := by
  simp only [FrameCatches, Kont.Catches, Bool.or_false] at hf
  obtain ⟨⟨hc, hc'⟩, -⟩ := hC
  split at hf
  · rename_i m r
    have := hH m
    simp [Kont.HasHnd] at this
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

/-- **A stopping frame of `0`, in a context with no handler named `0` and no `ccatch` frame**, is a
finaliser frame or a running finaliser's `cfin` frame. -/
theorem frame_of_cancel {f : Expr} {Ki : Kont} (hf : FrameCatches 0 f)
    (hH : (Kont.appR f Ki).HasHnd 0 = false) (hC : (Kont.appR f Ki).NoCC) :
    (∃ x, f = .app (.prim .ubind) x) ∨ ∃ x, f = .app (.prim .cfin) x := by
  simp only [FrameCatches, Kont.Catches, Bool.or_false] at hf
  simp only [Kont.HasHnd, Bool.or_eq_false_iff] at hH
  obtain ⟨hc, -⟩ := hC
  split at hf
  · rename_i m r
    simp only [beq_iff_eq] at hf
    subst hf
    simp at hH
  · exact .inl ⟨_, rfl⟩
  · exact absurd rfl hc
  · exact .inr ⟨_, rfl⟩
  · simp at hf

/-- **A stopping frame of a nonzero name, in a context with no `cfin` frame**, is a handler of the
name or a finaliser frame. -/
theorem frame_of_unwind {n : UInt32} {f : Expr} {Ki : Kont} (hf : FrameCatches n f) (hn : n ≠ 0)
    (hC : (Kont.appR f Ki).NoCfin) :
    (∃ r, f = .app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) r)) ∨
      ∃ x, f = .app (.prim .ubind) x := by
  simp only [FrameCatches, Kont.Catches, Bool.or_false] at hf
  obtain ⟨hc, -⟩ := hC
  split at hf
  · rename_i m r
    simp only [beq_iff_eq] at hf
    subst hf
    exact .inl ⟨r, rfl⟩
  · exact .inr ⟨_, rfl⟩
  · simp at hf; exact absurd hf hn
  · exact absurd rfl (hc _)
  · simp at hf

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

/-- The finalisers of a context whose innermost stopping frame is a finaliser frame. -/
theorem fins_innerUbind {n : UInt32} {Ko Ki : Kont} {N D : Val} (hKi : Ki.Catches n = false) :
    (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).fins = D.1 :: Ko.fins := by
  rw [fins_comp]
  simp only [Kont.fins, fins_nil_of_catches Ki hKi, List.nil_append, Val.pair]
  rfl

/-- The finalisers of a context whose innermost stopping frame is a running finaliser's `cfin`
frame: those outside it. -/
theorem fins_innerCfin {n : UInt32} {Ko Ki : Kont} {x : Expr} (hKi : Ki.Catches n = false) :
    (Ko.comp (.appR (.app (.prim .cfin) x) Ki)).fins = Ko.fins := by
  rw [fins_comp]
  simp only [Kont.fins, fins_nil_of_catches Ki hKi, List.nil_append, List.append_nil]

/-! ### Complete runs: the order a cancel and an unwind fire the finalisers -/

/-- What a cancel answers at `ccatch`: `()`, or the kept error raised at the canceller.
`[spec §19]` -/
def cancelAnswer : Option Val → Expr
  | none => .val .unit
  | some E => raiseE (.val E)

/-- The cancel delimiter `ccatch □` around a context. -/
abbrev ccatchAt (K : Kont) : Kont := .appR (.prim .ccatch) K

/-- **A complete cancel run that fires the finalisers `fs`, innermost first**: one
`[finalise-cancel]` per finaliser, its `D ()` run under `cfin` to `[cfin-ret]` or `[cfin-raise]`,
and at the end `ccatch` answering (`[cancel]`, `[cancel-raise]`).  `[spec §19]` -/
inductive CancelRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | caught {μ : Heap} {K : Kont} {err : Option Val}
      (hK : K.Catches 0 = false) :
      CancelRun μ (ccatchE (K.plug (raiseE (.val (cancelVal err))))) [] μ (cancelAnswer err)
  | fin {μ μ₁ μ₂ : Heap} {K₀ K : Kont} {Nv Dv : Val} {err err' : Option Val}
      {fs : List Expr} {r : Expr} (hK : K.Catches 0 = false)
      (hD : Steps (ℍ := ℍ) μ (cfinE (cancelVal err) (.app (.val Dv) (.val .unit))) μ₁
              (raiseE (.val (cancelVal err'))))
      (hr : CancelRun μ₁ (ccatchE (K₀.plug (raiseE (.val (cancelVal err'))))) fs μ₂ r) :
      CancelRun μ
        (ccatchE (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (cancelVal err)))))))
        (Dv.1 :: fs) μ₂ r

/-- **A complete unwind that fires the finalisers `fs`, innermost first**: one `[finalise]` per
finaliser, its `D (); raise p` run until a raise is pending under a context `Kd` that catches
nothing of it, ending at a raise that the remaining frames do not catch.  If `D` returns, `Kd` is
the hole and the raise is `p`.  If `D` raises, the raise is `D`'s, which supersedes `p`, and `Kd`
holds the frame `□; raise p` (which catches nothing) and `D`'s own frames at the raise; the
unwind goes on from `K₀ ∘ Kd`.  `[spec §19]` -/
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

/-- **A fired finaliser runs alone**, in the runs of `e` from the empty memory: at a configuration
a run reaches that fires the finaliser `D` of a frame `ubind (N, D)` (at a raise of `n`, `0` the
cancel's name, that the frame's inside catches nothing of), the run of `D ()` alone ends only at
a value or at an uncaught raise of a name in `FR`.  It excludes a finaliser that performs an
operation a handler outside answers (§27), whose run alone stops at the operation.
`[spec §19, §27]` -/
def FinAloneAt (FR : UInt32 → Prop) (e : Expr) : Prop :=
  ∀ {μ : Heap} {K₀ K : Kont} {N D : Val} {n i : UInt32} {v : Val},
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ
      (K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))) →
    K.Catches n = false →
    ∀ {μ' : Heap} {t : Expr}, Steps (ℍ := ℍ) μ (.app (.val D) (.val .unit)) μ' t →
      (∀ μ'' t', ¬ Step1 (ℍ := ℍ) μ' t μ'' t') →
      IsVal t ∨ ∃ (K' : Kont) (m j : UInt32) (w : Val),
        t = K'.plug (raiseE (.val (opPayload m j w))) ∧ K'.Catches m = false ∧ FR m

/-- A finaliser that may raise fewer names runs alone at more. -/
theorem finAloneAt_mono {FR FR' : UInt32 → Prop} (hle : ∀ m, FR m → FR' m) {e : Expr}
    (h : FinAloneAt (ℍ := ℍ) FR e) : FinAloneAt (ℍ := ℍ) FR' e := by
  intro μ K₀ K N D n i v hreach hK μ' t hD hirr
  rcases h hreach hK hD hirr with hv | ⟨K', m, j, w, ht, hK', hm⟩
  · exact .inl hv
  · exact .inr ⟨K', m, j, w, ht, hK', hle m hm⟩

/-- **The cancel's order**: every complete run of the cancel of a continuation `kappa H K` that a
run of `e` reaches, `K` holding no `ccatch` and no `cfin` frame, fires `K`'s finalisers once each,
innermost first.  The three administrative steps from `κ (inj₂ ())` to `cancelOf K` keep the
store (`kappa_cancel_steps`); the canceller's context takes no part until `ccatch` answers.
`[spec §19]` -/
def CancelOrder (e : Expr) : Prop :=
  ∀ μ₁ (K₀ : Kont) H K, Kont.NoCtl K →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (.app (kappa H K) (.val (Val.inj₂ .unit)))) →
    ∀ μ₃ r, Steps (ℍ := ℍ) μ₁ (cancelOf K) μ₃ r →
      (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
      CancelRun (ℍ := ℍ) μ₁ (cancelOf K) K.fins μ₃ r

/-- **The unwind's order**: every complete unwind that a run of `e` reaches, through frames with
no handler and no `ccatch` or `cfin` frame, fires their finalisers once each, innermost first.
`[spec §19]` -/
def UnwindOrder (e : Expr) : Prop :=
  ∀ μ₁ (K₀ K : Kont) n i v, (∀ m, K.HasHnd m = false) → Kont.NoCtl K → n ≠ 0 →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) →
    ∀ μ₂ (K' : Kont) m j w, K'.Catches m = false →
      Steps (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) μ₂
        (K'.plug (raiseE (.val (opPayload m j w)))) →
      UnwindRun (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) K.fins μ₂
        (K'.plug (raiseE (.val (opPayload m j w))))

/-- **The order a cancel and an unwind fire the finalisers.**  `[spec §19]` -/
def FinaliserOrder (e : Expr) : Prop := CancelOrder (ℍ := ℍ) e ∧ UnwindOrder (ℍ := ℍ) e

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

theorem catches_innerUbind {n : UInt32} {Ko Ki : Kont} (x : Expr) :
    (Ko.comp (.appR (.app (.prim .ubind) x) Ki)).Catches n = true :=
  catches_of_innerCatch (by simp [FrameCatches, Kont.Catches])

/-- **The unwind through frames with no handler fires their finalisers once each, innermost
first**: `KA` holds no handler, `ccatch` or `cfin` frame, and `KB` stops nothing of the raise. -/
theorem unwindRun_of {FR : UInt32 → Prop} (hFR : ∀ m, FR m → m ≠ 0) {e : Expr}
    (hF : FinAloneAt (ℍ := ℍ) FR e) (K₀ : Kont) :
    ∀ (k : ℕ) (KA KB : Kont) (μ : Heap) (n i : UInt32) (v : Val), KA.fins.length = k →
      (∀ m, KA.HasHnd m = false) → KA.NoCtl → KB.Catches n = false → n ≠ 0 →
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
  have hHo : (∀ m, Ko.HasHnd m = false) ∧ (∀ m, (Kont.appR f Ki).HasHnd m = false) :=
    ⟨fun m => by have := hH m; rw [hasHnd_comp, Bool.or_eq_false_iff] at this; exact this.1,
     fun m => by have := hH m; rw [hasHnd_comp, Bool.or_eq_false_iff] at this; exact this.2⟩
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
  rcases hcase with ⟨n', i', v', -, hp', rfl⟩ | ⟨err, hp', -⟩
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
  rcases hF hfire hKiB hD hirr with hval | ⟨K'', m', j', w', rfl, hK'', hm'⟩
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
        hCo.1 hK'' (hFR m' hm') hpre μ₂ K' m j w hK' hcont)

/-- **The unwind's order, given that a fired finaliser runs alone**, at endings that are raises of
nonzero names. -/
theorem unwindOrder_at {FR : UInt32 → Prop} (hFR : ∀ m, FR m → m ≠ 0) {e : Expr}
    (hF : FinAloneAt (ℍ := ℍ) FR e) : UnwindOrder (ℍ := ℍ) e := by
  intro μ₁ K₀ K n i v hH hC hn hreach μ₂ K' m j w hK' hrun
  have h := unwindRun_of hFR hF K₀ K.fins.length K .hole μ₁ n i v rfl hH hC rfl hn
    (by rw [Kont.comp_hole]; exact hreach) μ₂ K' m j w hK' (by rw [Kont.comp_hole]; exact hrun)
  rw [Kont.comp_hole] at h
  exact h

/-- **A cancel run through frames with no `ccatch`, no `cfin` and no handler of `0` fires their
finalisers once each, innermost first.** -/
theorem cancelRun_of {FR : UInt32 → Prop} (hFR : ∀ m, FR m → m ≠ 0) {e : Expr}
    (hF : FinAloneAt (ℍ := ℍ) FR e) (K₀ : Kont) :
    ∀ (k : ℕ) (Kc : Kont) (μ : Heap) (err : Option Val), Kc.fins.length = k →
      Kc.NoCtl → Kc.HasHnd 0 = false →
      Steps (ℍ := ℍ) Adequacy.emptyMem e μ
        (K₀.plug (ccatchE (Kc.plug (raiseE (.val (cancelVal err)))))) →
      ∀ μ₃ r, Steps (ℍ := ℍ) μ (ccatchE (Kc.plug (raiseE (.val (cancelVal err))))) μ₃ r →
        (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
        CancelRun (ℍ := ℍ) μ (ccatchE (Kc.plug (raiseE (.val (cancelVal err))))) Kc.fins μ₃
          r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Kc μ err hk hC hH hreach μ₃ r hrun hr
  have hrirr : ∀ μ' t, ¬ Step1 (ℍ := ℍ) μ₃ r μ' t := by
    rcases hr with rfl | ⟨E, rfl⟩
    · exact val_irr (w := Val.unit)
    · exact raise_top_irr
  have hne : r ≠ ccatchE (Kc.plug (raiseE (.val (cancelVal err)))) := by
    rcases hr with rfl | ⟨E, rfl⟩
    · simp [ccatchE]
    · simp [ccatchE, raiseE]
  obtain ⟨μ₁, T₁, hst, hrest⟩ := steps_first hrun hne
  obtain ⟨Ko', f', Ki', a', hIC', hhead, rfl⟩ :=
    step1_raise (K := ccatchAt Kc) (payloadName_cancelVal err) hst
  by_cases hA : Kc.Catches 0 = true
  swap
  · -- the canceller answers
    simp only [Bool.not_eq_true] at hA
    have hIC : InnerCatch 0 (ccatchAt Kc) .hole (.prim .ccatch) Kc :=
      ⟨rfl, hA, by simp [FrameCatches, Kont.Catches]⟩
    obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
    rw [fins_nil_of_catches Kc hA]
    have hcase : μ₁ = μ ∧ a' = cancelAnswer err := by
      clear hrun hrest hreach hst ih hrirr hne hIC hIC' hr hk hC hH
      generalize hX : Expr.app (.prim .ccatch) (Kc.plug (raiseE (.val (cancelVal err)))) = X
        at hhead
      cases hhead with
      | cancel K₀' hK₀' =>
          simp only [ccatchE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
          obtain ⟨-, hp⟩ := plug_raise_inj hX
          obtain rfl := cancelVal_inj hp
          exact ⟨rfl, rfl⟩
      | creraise E K₀' hK₀' =>
          simp only [ccatchE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
          obtain ⟨-, hp⟩ := plug_raise_inj hX
          obtain rfl := cancelVal_inj hp
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
  have hIC : InnerCatch 0 (ccatchAt (Ko.comp (.appR (.app (.prim .ubind) x) Ki))) (ccatchAt Ko)
      (.app (.prim .ubind) x) Ki := ⟨rfl, hKi, hf⟩
  obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
  obtain ⟨hμ, N, D, rfl, hcase⟩ := head_ubind_raise hhead
  subst μ₁
  rcases hcase with ⟨n', i', v', hn', hp', -⟩ | ⟨err', hp', rfl⟩
  · exact absurd (opPayload_inj hp').1.symm hn'
  obtain rfl := cancelVal_inj hp'
  have hk' : Ko.fins.length < k := by
    rw [fins_innerUbind hKi] at hk; simp at hk; omega
  rw [fins_innerUbind hKi]
  have hT : ccatchE ((Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).plug
      (raiseE (.val (cancelVal err)))) =
      ccatchE (Ko.plug (ubindE (Val.pair N D) (Ki.plug (raiseE (.val (cancelVal err)))))) := by
    rw [Kont.plug_comp]; rfl
  rw [hT] at hreach hst ⊢
  -- the finaliser's run under `cfin`
  have hrest' : Steps (ℍ := ℍ) μ (((ccatchAt Ko).comp
      (.appR (.app (.prim .cfin) (cancelVal err).1) .hole)).plug (.app (.val D) (.val .unit)))
      μ₃ r := by
    rw [Kont.plug_comp]; exact hrest
  obtain ⟨μ₂, t, hD, hirr, hcont⟩ := steps_plug_split_end _ hrest' hrirr
  have hfire : Steps (ℍ := ℍ) Adequacy.emptyMem e μ ((K₀.comp (ccatchAt Ko)).plug
      (ubindE (Val.pair N D) (Ki.plug (raiseE (.val (opPayload 0 0 (errVal err))))))) := by
    rw [Kont.plug_comp]; exact hreach
  have hpre : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₂
      (K₀.plug (((ccatchAt Ko).comp (.appR (.app (.prim .cfin) (cancelVal err).1) .hole)).plug
        t)) := by
    refine hreach.trans (.more (hst.plug K₀) ?_)
    have := Steps.plug (K₀.comp ((ccatchAt Ko).comp
      (.appR (.app (.prim .cfin) (cancelVal err).1) .hole))) hD
    simp only [Kont.plug_comp] at this ⊢
    exact this
  rw [Kont.plug_comp] at hcont hpre
  rcases hF hfire hKi hD hirr with hval | ⟨K'', m, j, w, rfl, hK'', hm⟩
  · -- the finaliser returned: `[cfin-ret]`
    obtain ⟨w, rfl⟩ : ∃ w : Val, t = w.1 := ⟨⟨t, hval⟩, rfl⟩
    have hret := Head.cfret (ℍ := ℍ) μ₂ err w
    have hne' : r ≠ (ccatchAt Ko).plug (cfinE (cancelVal err) (.val w)) := by
      rcases hr with rfl | ⟨E, rfl⟩
      · simp [Kont.plug]
      · simp [Kont.plug, raiseE]
    obtain ⟨μ₄, T₄, hst₄, hrest₄⟩ := steps_first hcont hne'
    obtain ⟨hμ₄, rfl⟩ := step1_det hret rfl hst₄
    subst μ₄
    have hD' : Steps (ℍ := ℍ) μ (cfinE (cancelVal err) (.app (.val D) (.val .unit))) μ₂
        (raiseE (.val (cancelVal err))) :=
      (Steps.plug (.appR (.app (.prim .cfin) (cancelVal err).1) .hole) hD).trans
        (Steps.one (Step1.head hret))
    exact .fin hKi hD' (ih Ko.fins.length hk' Ko μ₂ err rfl hCo.1 hHo.1
      (hpre.trans (.more (hst₄.plug K₀) (.refl _ _))) μ₃ r hrest₄ hr)
  · -- the finaliser raised: `[cfin-raise]`
    have hraise := Head.cferr (ℍ := ℍ) μ₂ err m j w K'' (hFR m hm) hK''
    have hne' : r ≠ (ccatchAt Ko).plug (cfinE (cancelVal err)
        (K''.plug (raiseE (.val (opPayload m j w))))) := by
      rcases hr with rfl | ⟨E, rfl⟩
      · simp [Kont.plug]
      · simp [Kont.plug, raiseE]
    obtain ⟨μ₄, T₄, hst₄, hrest₄⟩ := steps_first hcont hne'
    obtain ⟨hμ₄, rfl⟩ := step1_det hraise rfl hst₄
    subst μ₄
    have hD' : Steps (ℍ := ℍ) μ (cfinE (cancelVal err) (.app (.val D) (.val .unit))) μ₂
        (raiseE (.val (cancelVal (errNext err m j w)))) :=
      (Steps.plug (.appR (.app (.prim .cfin) (cancelVal err).1) .hole) hD).trans
        (Steps.one (Step1.head hraise))
    exact .fin hKi hD' (ih Ko.fins.length hk' Ko μ₂ _ rfl hCo.1 hHo.1
      (hpre.trans (.more (hst₄.plug K₀) (.refl _ _))) μ₃ r hrest₄ hr)

/-- **The cancel's order, given that a fired finaliser runs alone**: the cancel runs the dead
region, which holds no handler (`hasHnd_dead`), so no handler stops it before its finaliser
frames. -/
theorem cancelOrder_at {FR : UInt32 → Prop} (hFR : ∀ m, FR m → m ≠ 0) {e : Expr}
    (hF : FinAloneAt (ℍ := ℍ) FR e) : CancelOrder (ℍ := ℍ) e := by
  intro μ₁ K₀ H K hC hreach μ₃ r hrun hr
  have hreach' : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (cancelOf K)) :=
    hreach.trans (Steps.plug K₀ (CancelIntercept.kappa_cancel_steps μ₁ H K))
  have h := cancelRun_of hFR hF K₀ _ K.dead μ₁ none rfl (noCtl_dead hC) (hasHnd_dead 0 K) hreach'
    μ₃ r hrun hr
  rw [fins_dead] at h
  exact h

/-- **The order a cancel and an unwind fire the finalisers, given that a fired finaliser runs
alone** to a value or to an uncaught raise of a nonzero name.  `[spec §19]` -/
theorem finaliserOrder_at {e : Expr} (hF : FinAloneAt (ℍ := ℍ) (· ≠ 0) e) :
    FinaliserOrder (ℍ := ℍ) e :=
  ⟨cancelOrder_at (fun _ h => h) hF, unwindOrder_at (fun _ h => h) hF⟩

/-- **At option A** (§24): given that a fired finaliser's run alone ends at a value. -/
theorem finaliserOrder_A {e : Expr} (hF : FinAloneAt (ℍ := ℍ) (fun _ => False) e) :
    FinaliserOrder (ℍ := ℍ) e :=
  finaliserOrder_at (finAloneAt_mono (fun _ h => h.elim) hF)

/-! ### Finite memories -/

theorem finDom_empty : FinDom (Adequacy.emptyMem : Heap) :=
  ⟨[], fun _ h => absurd rfl h⟩

theorem finDom_upd {μ : Heap} (h : FinDom μ) (ℓ : Loc) (v : Val) : FinDom (μ.upd ℓ v) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨ℓ :: d, fun k hk => ?_⟩
  by_cases hkℓ : k = ℓ
  · rw [hkℓ]; exact List.mem_cons_self
  · rw [BoCa.BoLo.Heap.upd_other hkℓ] at hk; exact List.mem_cons_of_mem _ (hd k hk)

theorem finDom_del {μ : Heap} (h : FinDom μ) (ℓ : Loc) : FinDom (μ.del ℓ) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun k hk => hd k ?_⟩
  by_cases hkℓ : k = ℓ
  · rw [hkℓ, BoCa.BoLo.Heap.del_same] at hk; exact absurd rfl hk
  · rwa [BoCa.BoLo.Heap.del_other hkℓ] at hk

theorem finDom_fill {μ : Heap} (h : FinDom μ) (ℓ : Loc) (n : ℕ) (v : Val) :
    FinDom (μ.fill ℓ n v) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨List.range' ℓ n ++ d, fun k hk => ?_⟩
  unfold BoCa.BoLo.Heap.fill at hk
  split at hk
  · rename_i hr
    exact List.mem_append_left _ (List.mem_range'_1.2 ⟨hr.1, hr.2⟩)
  · exact List.mem_append_right _ (hd k hk)

/-- A head step keeps a memory's cells finitely many. -/
theorem finDom_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') (hf : FinDom μ) :
    FinDom μ' := by
  cases h <;>
    first
    | exact hf
    | exact finDom_upd hf _ _
    | exact finDom_del hf _
    | exact finDom_fill hf _ _ _

/-- **A run keeps a memory's cells finitely many**, so every memory a run from the empty memory
reaches has finitely many. -/
theorem finDom_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e') (hf : FinDom μ) :
    FinDom μ' := by
  induction h with
  | refl => exact hf
  | more h₁ _ ih =>
      obtain ⟨_, _, _, -, -, hh⟩ := h₁
      exact ih (finDom_head hh hf)

/-! ### Paths, and a term that runs alone -/

/-- **A path of the machine** from `(μ, e)`: the configurations a run passes through, each a step
from the one before.  `[spec §19]` -/
inductive Path : Heap → Expr → List (Heap × Expr) → Prop
  | nil {μ : Heap} {e : Expr} : Path μ e []
  | cons {μ μ' : Heap} {e e' : Expr} {q : List (Heap × Expr)} :
      Step1 (ℍ := ℍ) μ e μ' e' → Path μ' e' q → Path μ e ((μ', e') :: q)

/-- The last configuration of a path from `(μ, e)`: `(μ, e)` itself when the path is empty. -/
def pathEnd (μ : Heap) (e : Expr) : List (Heap × Expr) → Heap × Expr
  | [] => (μ, e)
  | x :: q => pathEnd x.1 x.2 q

/-- The first step of a path, and the path after it. -/
theorem Path.cons_inv {μ : Heap} {e : Expr} {x : Heap × Expr} {q : List (Heap × Expr)}
    (h : Path (ℍ := ℍ) μ e (x :: q)) : Step1 (ℍ := ℍ) μ e x.1 x.2 ∧ Path (ℍ := ℍ) x.1 x.2 q := by
  cases h with
  | cons h₁ h₂ => exact ⟨h₁, h₂⟩

/-- A path runs from its start to its last configuration. -/
theorem Path.steps {μ : Heap} {e : Expr} {q : List (Heap × Expr)} (h : Path (ℍ := ℍ) μ e q) :
    Steps (ℍ := ℍ) μ e (pathEnd μ e q).1 (pathEnd μ e q).2 := by
  induction h with
  | nil => exact .refl _ _
  | cons h₁ _ ih => exact .more h₁ ih

/-- **Every run is a path.** -/
theorem path_of_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e') :
    ∃ q : List (Heap × Expr), Path (ℍ := ℍ) μ e q ∧ pathEnd μ e q = (μ', e') := by
  induction h with
  | refl => exact ⟨[], .nil, rfl⟩
  | @more μ μ₁ μ' e e₁ e' h₁ _ ih =>
      obtain ⟨q, hq, hl⟩ := ih
      exact ⟨(μ₁, e₁) :: q, .cons h₁ hq, hl⟩

/-- **Along the path `q` from `(μ, Kf[t])`, the term `t` runs alone in the context `Kf`**, to
`(μ', t')`: each configuration of `q` is `Kf` around a step of the term before.  `[spec §19]` -/
inductive Alone (Kf : Kont) : Heap → Expr → List (Heap × Expr) → Heap → Expr → Prop
  | nil {μ : Heap} {t : Expr} : Alone Kf μ t [] μ t
  | cons {μ μ₁ μ' : Heap} {t t₁ t' : Expr} {q : List (Heap × Expr)} :
      Step1 (ℍ := ℍ) μ t μ₁ t₁ → Alone Kf μ₁ t₁ q μ' t' →
      Alone Kf μ t ((μ₁, Kf.plug t₁) :: q) μ' t'

/-! ### Finalisers that run alone -/

/-- **From `μ`, every run of `D` alone continues to `()`, or to a raise of a name in `FR` other
than `0` that `D`'s own frames catch nothing of.**  At `FR = ∅` (option A, §24) the finaliser
lets no raise escape.  `[spec §19, §27]` -/
def FinAlone (FR : UInt32 → Prop) (μ : Heap) (D : Expr) : Prop :=
  ∀ μ₁ t, Steps (ℍ := ℍ) μ D μ₁ t → ∃ μ' t', Steps (ℍ := ℍ) μ₁ t μ' t' ∧
    (t' = Val.unit.1 ∨ ∃ (K' : Kont) (m j : UInt32) (w : Val),
      t' = K'.plug (raiseE (.val (opPayload m j w))) ∧ K'.Catches m = false ∧ m ≠ 0 ∧ FR m)

/-- **From `μ`, every run of `D` continues to `()`.**  `[spec §19, §24]` -/
def FinOK (μ : Heap) (D : Expr) : Prop :=
  ∀ μ₁ t, Steps (ℍ := ℍ) μ D μ₁ t → ∃ μ', Steps (ℍ := ℍ) μ₁ t μ' Val.unit.1

/-- A finaliser that runs to `()` runs alone at every set of names. -/
theorem FinOK.finAlone {μ : Heap} {D : Expr} (h : FinOK (ℍ := ℍ) μ D) (FR : UInt32 → Prop) :
    FinAlone (ℍ := ℍ) FR μ D := fun μ₁ t hs =>
  let ⟨μ', h'⟩ := h μ₁ t hs
  ⟨μ', _, h', .inl rfl⟩

/-- **Along a run of a finaliser that runs alone, every term is `()`, an uncaught raise of a name in
`FR`, or steps.** -/
theorem FinAlone.cases {FR : UInt32 → Prop} {μf : Heap} {D : Expr} (h : FinAlone (ℍ := ℍ) FR μf D)
    {μ : Heap} {t : Expr} (hs : Steps (ℍ := ℍ) μf D μ t) :
    t = Val.unit.1 ∨
      (∃ (K' : Kont) (m j : UInt32) (w : Val),
        t = K'.plug (raiseE (.val (opPayload m j w))) ∧ K'.Catches m = false ∧ m ≠ 0 ∧ FR m) ∨
      ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ t μ₂ t₂ := by
  obtain ⟨μ', t', hrest, hend⟩ := h μ t hs
  cases hrest with
  | refl => exact hend.elim .inl (fun h => .inr (.inl h))
  | more h₁ _ => exact .inr (.inr ⟨_, _, h₁⟩)

/-- A finaliser that runs alone from `μ` runs alone from where a run of it reaches. -/
theorem FinAlone.steps {FR : UInt32 → Prop} {μf μ : Heap} {D t : Expr}
    (h : FinAlone (ℍ := ℍ) FR μf D) (hs : Steps (ℍ := ℍ) μf D μ t) :
    FinAlone (ℍ := ℍ) FR μ t := fun μ₁ t₁ hs₁ => h μ₁ t₁ (hs.trans hs₁)

/-! ### The unwind, read prefix-closed -/

/-- The frame a pending raise waits in while a fired finaliser runs: `□; raise p`.
`[spec §19]` -/
abbrev pendK (p : Val) : Kont := .seq .hole (raiseE (.val p))

mutual
/-- **An unwind trace** of the raise `raise p` pending under `K`, in the context `K₀`: the path
`q` from `(μ, K₀[K[raise p]])` follows it.  The innermost frame of `K` that stops the raise
decides.  None: the raise has left `K`, and the trace is over (`out`).  A handler of its name: the
trace is over there, the handler's abortive catch next (`caught`, `catch_abort`).  A finaliser
frame `ubind (N, D)`: it fires (`[finalise]`), and `D ()` runs alone with the raise pending under
`□; raise p` (`PendTr`).  A trace stops anywhere: before a fire step (`stop`) or while a
finaliser runs (`PendTr.running`).  `[spec §19]` -/
inductive UnwindTr (FR : UInt32 → Prop) (K₀ : Kont) :
    Heap → Kont → Val → List (Heap × Expr) → Prop
  | stop {μ : Heap} {K : Kont} {p : Val} : UnwindTr FR K₀ μ K p []
  | out {μ : Heap} {K : Kont} {n i : UInt32} {v : Val} {q : List (Heap × Expr)}
      (hK : K.Catches n = false) : UnwindTr FR K₀ μ K (opPayload n i v) q
  | caught {μ : Heap} {K₂ K₁ : Kont} {n i : UInt32} {v : Val} {r : Expr}
      {q : List (Heap × Expr)} (hK₁ : K₁.Catches n = false) :
      UnwindTr FR K₀ μ (K₂.comp (.appR (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) r)) K₁))
        (opPayload n i v) q
  | fire {μ : Heap} {K₂ K₁ : Kont} {N D : Val} {n i : UInt32} {v : Val} {q : List (Heap × Expr)}
      (hn : n ≠ 0) (hK₁ : K₁.Catches n = false)
      (h : PendTr FR K₀ K₂ (opPayload n i v) μ (.app (.val D) (.val .unit)) q) :
      UnwindTr FR K₀ μ (K₂.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) K₁))
        (opPayload n i v)
        ((μ, ((K₀.comp K₂).comp (pendK (opPayload n i v))).plug (.app (.val D) (.val .unit))) ::
          q)
/-- **An unwind trace while a fired finaliser runs alone**, the raise `p` pending under
`K₀ ∘ K₂ ∘ (□; raise p)`.  If it returns `()`, `(); raise p` hands the raise on (`[1↦]`) and the
unwind goes on through `K₂` (`returned`).  If a raise of a name in `FR` escapes it, that raise
supersedes `p`, and the unwind goes on from it (`superseded`).  `[spec §19]` -/
inductive PendTr (FR : UInt32 → Prop) (K₀ : Kont) :
    Kont → Val → Heap → Expr → List (Heap × Expr) → Prop
  | running {K₂ : Kont} {p : Val} {μ μ' : Heap} {t t' : Expr} {q : List (Heap × Expr)}
      (h : Alone (ℍ := ℍ) ((K₀.comp K₂).comp (pendK p)) μ t q μ' t') : PendTr FR K₀ K₂ p μ t q
  | returned {K₂ : Kont} {p : Val} {μ μ' : Heap} {t : Expr} {q q₂ : List (Heap × Expr)}
      (h : Alone (ℍ := ℍ) ((K₀.comp K₂).comp (pendK p)) μ t q μ' Val.unit.1)
      (h₂ : UnwindTr FR K₀ μ' K₂ p q₂) :
      PendTr FR K₀ K₂ p μ t (q ++ (μ', (K₀.comp K₂).plug (raiseE (.val p))) :: q₂)
  | superseded {K₂ K' : Kont} {p : Val} {μ μ' : Heap} {t : Expr} {m j : UInt32} {w : Val}
      {q q₂ : List (Heap × Expr)}
      (h : Alone (ℍ := ℍ) ((K₀.comp K₂).comp (pendK p)) μ t q μ'
        (K'.plug (raiseE (.val (opPayload m j w)))))
      (hK' : K'.Catches m = false) (hm0 : m ≠ 0) (hm : FR m)
      (h₂ : UnwindTr FR K₀ μ' ((K₂.comp (pendK p)).comp K') (opPayload m j w) q₂) :
      PendTr FR K₀ K₂ p μ t (q ++ q₂)
end

/-- A step of the finaliser, read alone, goes in front of the trace of what follows. -/
theorem PendTr.cons {FR : UInt32 → Prop} {K₀ K₂ : Kont} {p : Val} {μ μ₁ : Heap} {t t₁ : Expr}
    {q : List (Heap × Expr)} (hs : Step1 (ℍ := ℍ) μ t μ₁ t₁)
    (h : PendTr (ℍ := ℍ) FR K₀ K₂ p μ₁ t₁ q) :
    PendTr (ℍ := ℍ) FR K₀ K₂ p μ t ((μ₁, ((K₀.comp K₂).comp (pendK p)).plug t₁) :: q) := by
  cases h with
  | running ha => exact .running (.cons hs ha)
  | returned ha h₂ => exact .returned (.cons hs ha) h₂
  | superseded ha hK' hm0 hm h₂ => exact .superseded (.cons hs ha) hK' hm0 hm h₂

/-- The finalisers a context holds, every one running alone from every finite memory. -/
abbrev FinsAlone (FR : UInt32 → Prop) (K : Kont) : Prop :=
  ∀ D ∈ K.fins, ∀ μ, FinDom μ → FinAlone (ℍ := ℍ) FR μ (.app D (.val .unit))

/-- **The unwind while a fired finaliser runs alone**, given the unwind through the rest of the
context on shorter paths.  While the finaliser steps, the run is its run alone
(`step1_plug_of_step`); at `()`, `(); raise p` hands the raise on; at a raise that escapes it, that
raise is pending under `K₂ ∘ (□; raise p) ∘ K'`, which holds no finaliser outside `K₂`'s. -/
theorem pend_pfx {FR : UInt32 → Prop} {K₀ K₂ : Kont} {n₀ i₀ : UInt32} {v₀ : Val} (hn₀ : n₀ ≠ 0)
    (hK₂ : K₂.NoCfin) (hfin₂ : FinsAlone (ℍ := ℍ) FR K₂) {μf : Heap} {D : Expr}
    (hD : FinAlone (ℍ := ℍ) FR μf D) (hfd : FinDom μf) (k : ℕ)
    (ihU : ∀ q : List (Heap × Expr), q.length < k → ∀ (μ : Heap) (K : Kont) (n i : UInt32)
      (v : Val), FinDom μ → n ≠ 0 → K.NoCfin → FinsAlone (ℍ := ℍ) FR K →
      Path (ℍ := ℍ) μ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) q →
      UnwindTr (ℍ := ℍ) FR K₀ μ K (opPayload n i v) q) :
    ∀ (q : List (Heap × Expr)), q.length < k → ∀ (μ : Heap) (t : Expr),
      Steps (ℍ := ℍ) μf D μ t →
      Path (ℍ := ℍ) μ (((K₀.comp K₂).comp (pendK (opPayload n₀ i₀ v₀))).plug t) q →
      PendTr (ℍ := ℍ) FR K₀ K₂ (opPayload n₀ i₀ v₀) μ t q := by
  intro q
  induction q with
  | nil => intro _ μ t _ _; exact .running .nil
  | cons x q₁ ih =>
      intro hlen μ t hrun hq
      have hfdμ : FinDom μ := finDom_steps hrun hfd
      obtain ⟨μx, ex⟩ := x
      rcases hD.cases hrun with rfl | ⟨K', m, j, w, rfl, hK', hm0, hm⟩ | ⟨μ₂, t₂, ht⟩
      · -- the finaliser returned `()`: `(); raise p` hands the raise on
        obtain ⟨hst, hq₁⟩ := hq.cons_inv
        have he : ((K₀.comp K₂).comp (pendK (opPayload n₀ i₀ v₀))).plug Val.unit.1 =
            (K₀.comp K₂).plug (.seq (.val Val.unit) (raiseE (.val (opPayload n₀ i₀ v₀)))) := by
          rw [Kont.plug_comp]; rfl
        rw [he] at hst
        obtain ⟨h1, h2⟩ := step1_det (Head.seq (ℍ := ℍ) μ (raiseE (.val (opPayload n₀ i₀ v₀))))
          rfl hst
        simp only at h1 h2 hq₁
        subst μx ex
        have hq₁' :
            Path (ℍ := ℍ) μ (K₀.plug (K₂.plug (raiseE (.val (opPayload n₀ i₀ v₀))))) q₁ := by
          rw [← Kont.plug_comp]; exact hq₁
        have h₂ := ihU q₁ (by simp at hlen; omega) μ K₂ n₀ i₀ v₀ hfdμ hn₀ hK₂ hfin₂ hq₁'
        exact .returned (q := []) .nil h₂
      · -- a raise escaped the finaliser: it supersedes the pending one
        have hctx : ((K₀.comp K₂).comp (pendK (opPayload n₀ i₀ v₀))).plug
            (K'.plug (raiseE (.val (opPayload m j w)))) =
            K₀.plug (((K₂.comp (pendK (opPayload n₀ i₀ v₀))).comp K').plug
              (raiseE (.val (opPayload m j w)))) := by
          simp only [Kont.plug_comp]
        rw [hctx] at hq
        have hC : ((K₂.comp (pendK (opPayload n₀ i₀ v₀))).comp K').NoCfin :=
          (noCfin_comp _ _).2 ⟨(noCfin_comp _ _).2 ⟨hK₂, trivial⟩, noCfin_of_catches K' hK'⟩
        have hF : FinsAlone (ℍ := ℍ) FR ((K₂.comp (pendK (opPayload n₀ i₀ v₀))).comp K') := by
          intro D' hD'
          rw [fins_comp, fins_comp, fins_nil_of_catches K' hK'] at hD'
          simp only [Kont.fins, List.nil_append] at hD'
          exact hfin₂ D' hD'
        exact .superseded (q := []) .nil hK' hm0 hm (ihU _ hlen μ _ m j w hfdμ hm0 hC hF hq)
      · -- the finaliser steps: the run's step is its step alone
        obtain ⟨hst, hq₁⟩ := hq.cons_inv
        obtain ⟨t', rfl, hs'⟩ := step1_plug_of_step _ ht hst
        exact PendTr.cons hs' (ih (by simp at hlen ⊢; omega) _ t' (hrun.trans (.one hs')) hq₁)

/-- **The unwind, read prefix-closed**: at a raise `raise (n, …)` pending under a context `K` with
no running finaliser's `cfin` frame, from a memory with finitely many cells, every path is a
prefix of the unwind trace, when each of `K`'s finalisers runs alone from every finite memory.
`[spec §19]` -/
theorem unwind_pfx {FR : UInt32 → Prop} (K₀ : Kont) :
    ∀ (k : ℕ) (q : List (Heap × Expr)), q.length < k →
    ∀ (μ : Heap) (K : Kont) (n i : UInt32) (v : Val), FinDom μ → n ≠ 0 → K.NoCfin →
      FinsAlone (ℍ := ℍ) FR K →
      Path (ℍ := ℍ) μ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) q →
      UnwindTr (ℍ := ℍ) FR K₀ μ K (opPayload n i v) q := by
  intro k
  induction k with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ k ih =>
  intro q hlen μ K n i v hfd hn hK hfin hq
  by_cases hA : K.Catches n = true
  swap
  · exact .out (by simpa using hA)
  obtain ⟨Ko, f, Ki, rfl, hKi, hf⟩ := innerCatch_exists n K hA
  have hCo := (noCfin_comp _ _).1 hK
  rcases frame_of_unwind hf hn hCo.2 with ⟨r, rfl⟩ | ⟨x, rfl⟩
  · exact .caught hKi
  rcases q with _ | ⟨⟨μx, ex⟩, q₁⟩
  · exact .stop
  obtain ⟨hst, hq₁⟩ := hq.cons_inv
  have hIC : InnerCatch n ((K₀.comp Ko).comp (.appR (.app (.prim .ubind) x) Ki)) (K₀.comp Ko)
      (.app (.prim .ubind) x) Ki := ⟨rfl, hKi, hf⟩
  have hst' := hst
  rw [← Kont.plug_comp, ← Kont.comp_assoc] at hst'
  obtain ⟨Ko', f', Ki', a', hIC', hhead, hex⟩ := step1_raise (payloadName_opPayload n i v) hst'
  obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
  obtain ⟨hμx, N, D, rfl, hcase⟩ := head_ubind_raise hhead
  simp only at hμx hex hq₁
  subst μx ex
  rcases hcase with ⟨n', i', v', -, -, rfl⟩ | ⟨err, hp', -⟩
  swap
  · exact absurd (opPayload_inj hp').1 hn
  have hfins : (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).fins = D.1 :: Ko.fins :=
    fins_innerUbind hKi
  have hD := hfin D.1 (by rw [hfins]; exact List.mem_cons_self) μ hfd
  have hfino : FinsAlone (ℍ := ℍ) FR Ko :=
    fun D' h => hfin D' (by rw [hfins]; exact List.mem_cons_of_mem _ h)
  have ihU : ∀ q : List (Heap × Expr), q.length < k → ∀ (μ : Heap) (K : Kont) (n i : UInt32)
      (v : Val), FinDom μ → n ≠ 0 → K.NoCfin → FinsAlone (ℍ := ℍ) FR K →
      Path (ℍ := ℍ) μ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) q →
      UnwindTr (ℍ := ℍ) FR K₀ μ K (opPayload n i v) q :=
    fun q hq => ih q hq
  have hcfg : (K₀.comp Ko).plug (.seq (.app (.val D) (.val Val.unit))
      (raiseE (.val (opPayload n i v)))) =
      ((K₀.comp Ko).comp (pendK (opPayload n i v))).plug (.app (.val D) (.val .unit)) := by
    rw [Kont.plug_comp (K₀.comp Ko)]; rfl
  rw [hcfg] at hq₁ ⊢
  refine .fire hn hKi ?_
  exact pend_pfx hn hCo.1 hfino hD hfd k ihU q₁ (by simp at hlen; omega) μ _ (.refl _ _) hq₁

/-! ### The cancel, read prefix-closed -/

/-- The context a fired finaliser runs alone in during a cancel: the canceller's context `K₀`, the
delimiter, the region's frames `Ko` outside the finaliser, and the finaliser's `cfin err □`, `err`
the error kept so far. -/
abbrev finCtx (K₀ Ko : Kont) (err : Option Val) : Kont :=
  (K₀.comp (ccatchAt Ko)).comp (cfinK (cancelVal err))

/-- **A kept error of a name in `P`**: none, or a raise of a name in `P`.  `[spec §19]` -/
def ErrNamed (P : UInt32 → Prop) (err : Option Val) : Prop :=
  err = none ∨ ∃ m j w, err = some (opPayload m j w) ∧ P m

theorem errNamed_or {P : UInt32 → Prop} {e err : Option Val} (he : ErrNamed P e)
    (herr : ErrNamed P err) : ErrNamed P (e.or err) := by
  rcases he with rfl | ⟨m, j, w, rfl, hm⟩
  · exact herr
  · exact .inr ⟨m, j, w, rfl, hm⟩

theorem errNamed_next {P : UInt32 → Prop} {err : Option Val} (herr : ErrNamed P err)
    {m j : UInt32} (w : Val) (hm : P m) : ErrNamed P (errNext err m j w) :=
  errNamed_or herr (.inr ⟨m, j, w, rfl, hm⟩)

theorem kcfinNamed_comp {P : UInt32 → Prop} : ∀ (K₁ K₂ : Kont),
    KCfinNamed P (K₁.comp K₂) ↔ KCfinNamed P K₁ ∧ KCfinNamed P K₂ := by
  intro K₁ K₂
  induction K₁ with
  | hole => simp [Kont.comp, KCfinNamed]
  | appR f K ih => simp only [Kont.comp, KCfinNamed, ih]; tauto
  | _ => simp_all [Kont.comp, KCfinNamed]

/-- A dead region keeps the region's `cfin` frames, and the errors they keep. -/
theorem kcfinNamed_dead {P : UInt32 → Prop} : ∀ {K : Kont}, KCfinNamed P K → KCfinNamed P K.dead
  | .hole, h => h
  | .appR f K, h => by
      simp only [Kont.dead]
      split
      · exact kcfinNamed_dead h.2
      · exact ⟨h.1, kcfinNamed_dead h.2⟩
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => kcfinNamed_dead (K := K) h

mutual
/-- **A cancel trace** of the cancel `raise (0, (0, err))` under the region's frames `Kc` still to
unwind, inside `ccatch`, in the canceller's context `K₀`, `err` the error kept so far: the path
`q` from `(μ, K₀[ccatch Kc[raise (0, (0, err))]])` follows it.  The innermost frame of `Kc` that
stops the cancel decides.  None: `ccatch` answers the canceller, `()` at `none` and the kept error
re-raised otherwise, an error of a name in `P` (`answer`, `[cancel]`, `[cancel-raise]`); after the
answer anything may follow.  A finaliser frame `ubind (N, D)`: it fires (`[finalise-cancel]`), and
`D ()` runs alone under `cfin err` (`FinTr`).  A running finaliser's `cfin e`, a finaliser of an
earlier cancel whose continuation this cancel tears down: the cancel passes it in one step
(`[cfin-cancel]`), the earlier error `e` first (`pend`).  A trace stops anywhere: before a step of
the cancel (`stop`) or while a finaliser runs (`FinTr.running`).  `[spec §19]` -/
inductive CancelTr (FR P : UInt32 → Prop) (K₀ : Kont) :
    Heap → Kont → Option Val → List (Heap × Expr) → Prop
  | stop {μ : Heap} {Kc : Kont} {err : Option Val} : CancelTr FR P K₀ μ Kc err []
  | answer {μ : Heap} {Kc : Kont} {err : Option Val} {q : List (Heap × Expr)}
      (hK : Kc.Catches 0 = false) (hE : ErrNamed P err) :
      CancelTr FR P K₀ μ Kc err ((μ, K₀.plug (cancelAnswer err)) :: q)
  | fire {μ : Heap} {Ko Ki : Kont} {N D : Val} {err : Option Val} {q : List (Heap × Expr)}
      (hKi : Ki.Catches 0 = false) (h : FinTr FR P K₀ Ko err μ (.app (.val D) (.val .unit)) q) :
      CancelTr FR P K₀ μ (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)) err
        ((μ, (finCtx K₀ Ko err).plug (.app (.val D) (.val .unit))) :: q)
  | pend {μ : Heap} {Ko Ki : Kont} {e err : Option Val} {q : List (Heap × Expr)}
      (hKi : Ki.Catches 0 = false) (h : CancelTr FR P K₀ μ Ko (e.or err) q) :
      CancelTr FR P K₀ μ (Ko.comp (.appR (.app (.prim .cfin) (cancelVal e).1) Ki)) err
        ((μ, K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal (e.or err))))))) :: q)
/-- **A cancel trace while a fired finaliser runs alone** under `cfin err`, `Ko` the region's frames
outside it.  If it returns, `[cfin-ret]` hands the cancel on, the kept error unchanged
(`returned`).  If a raise of a name in `FR` escapes it, `[cfin-raise]` hands the cancel on keeping
the first error (`raised`).  `[spec §19]` -/
inductive FinTr (FR P : UInt32 → Prop) (K₀ : Kont) :
    Kont → Option Val → Heap → Expr → List (Heap × Expr) → Prop
  | running {Ko : Kont} {err : Option Val} {μ μ' : Heap} {t t' : Expr} {q : List (Heap × Expr)}
      (h : Alone (ℍ := ℍ) (finCtx K₀ Ko err) μ t q μ' t') : FinTr FR P K₀ Ko err μ t q
  | returned {Ko : Kont} {err : Option Val} {μ μ' : Heap} {t : Expr} {w : Val}
      {q q₂ : List (Heap × Expr)}
      (h : Alone (ℍ := ℍ) (finCtx K₀ Ko err) μ t q μ' (.val w))
      (h₂ : CancelTr FR P K₀ μ' Ko err q₂) :
      FinTr FR P K₀ Ko err μ t
        (q ++ (μ', K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal err)))))) :: q₂)
  | raised {Ko K' : Kont} {err : Option Val} {μ μ' : Heap} {t : Expr} {m j : UInt32} {w : Val}
      {q q₂ : List (Heap × Expr)}
      (h : Alone (ℍ := ℍ) (finCtx K₀ Ko err) μ t q μ' (K'.plug (raiseE (.val (opPayload m j w)))))
      (hK' : K'.Catches m = false) (hm : m ≠ 0) (hFR : FR m)
      (h₂ : CancelTr FR P K₀ μ' Ko (errNext err m j w) q₂) :
      FinTr FR P K₀ Ko err μ t
        (q ++ (μ', K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal (errNext err m j w))))))) ::
          q₂)
end

/-- A step of the finaliser, read alone, goes in front of the cancel trace of what follows. -/
theorem FinTr.cons {FR P : UInt32 → Prop} {K₀ Ko : Kont} {err : Option Val} {μ μ₁ : Heap}
    {t t₁ : Expr} {q : List (Heap × Expr)} (hs : Step1 (ℍ := ℍ) μ t μ₁ t₁)
    (h : FinTr (ℍ := ℍ) FR P K₀ Ko err μ₁ t₁ q) :
    FinTr (ℍ := ℍ) FR P K₀ Ko err μ t ((μ₁, (finCtx K₀ Ko err).plug t₁) :: q) := by
  cases h with
  | running ha => exact .running (.cons hs ha)
  | returned ha h₂ => exact .returned (.cons hs ha) h₂
  | raised ha hK' hm hFR h₂ => exact .raised (.cons hs ha) hK' hm hFR h₂

/-- **A cancel while a fired finaliser runs alone under `cfin`**, given the cancel through the rest
of the region on shorter paths.  While the finaliser steps, the run is its run alone; at a value,
`[cfin-ret]` hands the cancel on; at a raise that escapes it, `[cfin-raise]` does, the first error
kept. -/
theorem fin_pfx {FR P : UInt32 → Prop} (hFRP : ∀ m, FR m → P m) {K₀ Ko : Kont}
    {err : Option Val} (herr : ErrNamed P err) {μf : Heap} {D : Expr}
    (hD : FinAlone (ℍ := ℍ) FR μf D) (hfd : FinDom μf) (k : ℕ)
    (ihC : ∀ q : List (Heap × Expr), q.length < k → ∀ (μ : Heap) (err' : Option Val),
      FinDom μ → ErrNamed P err' →
      Path (ℍ := ℍ) μ (K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal err')))))) q →
      CancelTr (ℍ := ℍ) FR P K₀ μ Ko err' q) :
    ∀ (q : List (Heap × Expr)), q.length < k → ∀ (μ : Heap) (t : Expr),
      Steps (ℍ := ℍ) μf D μ t → Path (ℍ := ℍ) μ ((finCtx K₀ Ko err).plug t) q →
      FinTr (ℍ := ℍ) FR P K₀ Ko err μ t q := by
  intro q
  induction q with
  | nil => intro _ μ t _ _; exact .running .nil
  | cons x q₁ ih =>
      intro hlen μ t hrun hq
      have hfdμ : FinDom μ := finDom_steps hrun hfd
      obtain ⟨μx, ex⟩ := x
      obtain ⟨hst, hq₁⟩ := hq.cons_inv
      simp only at hst hq₁
      have hctx : ∀ a : Expr, (finCtx K₀ Ko err).plug a =
          (K₀.comp (ccatchAt Ko)).plug (cfinE (cancelVal err) a) := by
        intro a; rw [Kont.plug_comp]; rfl
      rcases hD.cases hrun with rfl | ⟨K', m, j, w, rfl, hK', hm0, hm⟩ | ⟨μ₂, t₂, ht⟩
      · -- the finaliser returned: `[cfin-ret]`
        rw [hctx] at hst
        obtain ⟨h1, h2⟩ := step1_det (Head.cfret (ℍ := ℍ) μ err Val.unit) rfl hst
        subst μx ex
        have hq₁' : Path (ℍ := ℍ) μ (K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal err))))))
            q₁ := by
          rw [Kont.plug_comp] at hq₁; exact hq₁
        rw [Kont.plug_comp]
        exact .returned (q := []) (w := Val.unit) .nil
          (ihC q₁ (by simp at hlen; omega) μ err hfdμ herr hq₁')
      · -- a raise escaped the finaliser: `[cfin-raise]`
        rw [hctx] at hst
        obtain ⟨h1, h2⟩ := step1_det (Head.cferr (ℍ := ℍ) μ err m j w K' hm0 hK') rfl hst
        subst μx ex
        have hq₁' : Path (ℍ := ℍ) μ
            (K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal (errNext err m j w))))))) q₁ := by
          rw [Kont.plug_comp] at hq₁; exact hq₁
        rw [Kont.plug_comp]
        exact .raised (q := []) .nil hK' hm0 hm
          (ihC q₁ (by simp at hlen; omega) μ _ hfdμ (errNamed_next herr w (hFRP m hm)) hq₁')
      · -- the finaliser steps: the run's step is its step alone
        obtain ⟨t', rfl, hs'⟩ := step1_plug_of_step _ ht hst
        exact FinTr.cons hs' (ih (by simp at hlen ⊢; omega) _ t' (hrun.trans (.one hs')) hq₁)

/-- **The cancel, read prefix-closed**: at a cancel `raise (0, (0, err))` under the region's frames
`Kc`, inside `ccatch`, from a memory with finitely many cells, when `Kc` holds no `ccatch` frame and
no handler of `0`, its running finalisers keep errors of names in `P`, `err` is one, and each of its
finalisers runs alone from every finite memory, raising only names in `FR ⊆ P`: every path is a
prefix of the cancel trace of `Kc`.  `[spec §19]` -/
theorem cancel_pfx {FR P : UInt32 → Prop} (hFRP : ∀ m, FR m → P m) (K₀ : Kont) :
    ∀ (k : ℕ) (q : List (Heap × Expr)), q.length < k →
    ∀ (μ : Heap) (Kc : Kont) (err : Option Val), FinDom μ → Kc.NoCC → Kc.HasHnd 0 = false →
      KCfinNamed P Kc → ErrNamed P err → FinsAlone (ℍ := ℍ) FR Kc →
      Path (ℍ := ℍ) μ (K₀.plug (ccatchE (Kc.plug (raiseE (.val (cancelVal err)))))) q →
      CancelTr (ℍ := ℍ) FR P K₀ μ Kc err q := by
  intro k
  induction k with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ k ih =>
  intro q hlen μ Kc err hfd hC hH hN herr hfin hq
  rcases q with _ | ⟨⟨μx, ex⟩, q₁⟩
  · exact .stop
  obtain ⟨hst, hq₁⟩ := hq.cons_inv
  simp only at hst hq₁
  have hst' : Step1 (ℍ := ℍ) μ ((K₀.comp (ccatchAt Kc)).plug (raiseE (.val (cancelVal err)))) μx
      ex := by
    rw [Kont.plug_comp]; exact hst
  obtain ⟨Ko', f', Ki', a', hIC', hhead, hex⟩ := step1_raise (payloadName_cancelVal err) hst'
  by_cases hA : Kc.Catches 0 = true
  swap
  · -- no frame is left: `ccatch` answers the canceller
    simp only [Bool.not_eq_true] at hA
    have hIC : InnerCatch 0 (K₀.comp (ccatchAt Kc)) K₀ (.prim .ccatch) Kc :=
      ⟨rfl, hA, by simp [FrameCatches, Kont.Catches]⟩
    obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
    have hcase : μx = μ ∧ a' = cancelAnswer err := by
      clear hq hq₁ hst hst' ih hIC hIC' hex
      generalize hX : Expr.app (.prim .ccatch) (Kc.plug (raiseE (.val (cancelVal err)))) = X
        at hhead
      cases hhead with
      | cancel K₀' hK₀' =>
          simp only [ccatchE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
          obtain ⟨-, hp⟩ := plug_raise_inj hX
          obtain rfl := cancelVal_inj hp
          exact ⟨rfl, rfl⟩
      | creraise E K₀' hK₀' =>
          simp only [ccatchE, Expr.app.injEq, Expr.val, Val.prim, true_and] at hX
          obtain ⟨-, hp⟩ := plug_raise_inj hX
          obtain rfl := cancelVal_inj hp
          exact ⟨rfl, rfl⟩
      | _ => simp_all [hndE, ubindE, cfinE]
    obtain ⟨rfl, rfl⟩ := hcase
    subst hex
    exact .answer hA herr
  -- the innermost frame that stops the cancel
  obtain ⟨Ko, f, Ki, rfl, hKi, hf⟩ := innerCatch_exists 0 Kc hA
  have hH' : (Kont.appR f Ki).HasHnd 0 = false ∧ Ko.HasHnd 0 = false := by
    rw [hasHnd_comp, Bool.or_eq_false_iff] at hH; exact ⟨hH.2, hH.1⟩
  have hCo := (noCC_comp _ _).1 hC
  have hNo := (kcfinNamed_comp _ _).1 hN
  have hIC : InnerCatch 0 (K₀.comp (ccatchAt (Ko.comp (.appR f Ki)))) (K₀.comp (ccatchAt Ko)) f
      Ki := ⟨by rw [Kont.comp_assoc]; rfl, hKi, hf⟩
  obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC hIC'
  rcases frame_of_cancel hf hH'.1 hCo.2 with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · -- a finaliser frame: `[finalise-cancel]` fires it
    obtain ⟨hμx, N, D, rfl, hcase⟩ := head_ubind_raise hhead
    rcases hcase with ⟨n', i', v', hn', hp', -⟩ | ⟨err', hp', rfl⟩
    · exact absurd (opPayload_inj hp').1.symm hn'
    obtain rfl := cancelVal_inj hp'
    subst μx ex
    have hfins : (Ko.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) Ki)).fins =
        D.1 :: Ko.fins := fins_innerUbind hKi
    have hD := hfin D.1 (by rw [hfins]; exact List.mem_cons_self) μ hfd
    have hfino : FinsAlone (ℍ := ℍ) FR Ko :=
      fun D' h => hfin D' (by rw [hfins]; exact List.mem_cons_of_mem _ h)
    have hcfg : (K₀.comp (ccatchAt Ko)).plug (cfinE (cancelVal err) (.app (.val D) (.val .unit))) =
        (finCtx K₀ Ko err).plug (.app (.val D) (.val .unit)) := by
      rw [Kont.plug_comp (K₀.comp (ccatchAt Ko))]; rfl
    rw [hcfg] at hq₁ ⊢
    refine .fire hKi ?_
    exact fin_pfx hFRP herr hD hfd k
      (fun q' hq' μ' err' hfd' herr' hp' =>
        ih q' hq' μ' Ko err' hfd' hCo.1 hH'.2 hNo.1 herr' hfino hp')
      q₁ (by simp at hlen; omega) μ _ (.refl _ _) hq₁
  · -- a running finaliser's `cfin` frame: `[cfin-cancel]` passes it, the earlier error first
    obtain ⟨hμx, e', rfl, hcase⟩ := head_cfin_raise hhead
    rcases hcase with ⟨m, j, w, hm, hp', -⟩ | ⟨err', hp', rfl⟩
    · exact absurd (opPayload_inj hp').1.symm hm
    obtain rfl := cancelVal_inj hp'
    subst μx ex
    have he' : ErrNamed P e' := hNo.2.1 e' rfl
    have hfins : (Ko.comp (.appR (.app (.prim .cfin) (cancelVal e').1) Ki)).fins = Ko.fins :=
      fins_innerCfin hKi
    have hfino : FinsAlone (ℍ := ℍ) FR Ko := fun D' h => hfin D' (by rw [hfins]; exact h)
    have hcfg : (K₀.comp (ccatchAt Ko)).plug (raiseE (.val (cancelVal (e'.or err)))) =
        K₀.plug (ccatchE (Ko.plug (raiseE (.val (cancelVal (e'.or err)))))) := by
      rw [Kont.plug_comp]; rfl
    rw [hcfg] at hq₁ ⊢
    exact .pend hKi (ih q₁ (by simp at hlen; omega) μ Ko (e'.or err) hfd hCo.1 hH'.2 hNo.1
      (errNamed_or he' herr) hfino hq₁)

/-! ### What typing gives about a fired finaliser -/

/-- `ARun.rest` at an end that takes no step. -/
theorem arun_rest_irr {A : Alloc} {i j j₁ : Nat} {μ μ' μ₁ : Heap} {e e₁ t : Expr}
    (hirr : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) A j μ' t k₂ μ₂ e₂)
    (h' : ARun (ℍ := ℍ) A i μ e j₁ μ₁ e₁) :
    ARun (ℍ := ℍ) A i μ e j μ' t → ARun (ℍ := ℍ) A j₁ μ₁ e₁ j μ' t := by
  induction h' with
  | refl => exact id
  | more s' _ ih =>
      intro h
      cases h with
      | refl => exact (hirr _ _ _ s').elim
      | more s t =>
          obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s'
          exact ih t

/-- **A run from a configuration `wpG` quantifies over continues to an end its post admits**, when
that end takes no step: the run is a prefix of `wpG`'s run under the allocator that replays it
(`steps_replay`). -/
theorem wpG_seg {ls : List SRec} {e : Expr} {Φ : List SRec → Expr → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} {μ : Heap} (hw : wpG (ℍ := ℍ) ls e Φ ρ)
    (hirr : ∀ ls' t ρ', Φ ls' t ρ' → ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂)
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) μ e μ₁ e₁) :
    ∃ (t : Expr) (μ' : Heap) (ls' : List SRec) (ρ' : WRes),
      Steps (ℍ := ℍ) μ₁ e₁ μ' t ∧ Φ ls' t ρ' := by
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨ρ', -, -, -, -, t, μ₀, μ', -, ls', -, -, -, h₄, -, -, ⟨k', h₇⟩, -, -, -, -, -, -, -,
    hΦ⟩ := hw ρf fρ ps hf hc hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₄ hμ
  have hirr' : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) (Alloc.replay cs) k' μ' t k₂ μ₂ e₂ :=
    fun _ _ _ hst => hirr _ _ _ hΦ _ _ _ hst.toStep1
  exact ⟨t, μ', ls', ρ', (arun_rest_irr hirr' hrun h₇).toSteps, hΦ⟩

/-- An end `wpG`'s post at an operation table admits takes no step: a value, or an operation its
context catches nothing of (`opPlug_no_step`). -/
theorem post_irr {T : OpTab} {Q : List SRec → Val → WProp} {Φ : List SRec → Expr → WProp}
    {ls : List SRec} {t : Expr} {ρ : WRes} (h : valPost Q ls t ρ ∨ opTable T ls t Φ ρ) :
    ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂ := by
  intro μ₁ μ₂ e₂ hst
  rcases h with ⟨v, rfl, -⟩ | ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · exact BoCa.BoLo.no_step_val hst
  · obtain ⟨⟨rfl, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK hst
  · obtain ⟨⟨rfl, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    exact opPlug_no_step (r := true) (payloadName_opPayload n i v) hK hst

/-- **A memory with finitely many cells is the lowering of a world** at no frame record: the world
that owns each cell, built by `TW.alloc` from `∅` (`alloc_world`). -/
theorem ownWorld_of_list :
    ∀ (d : List Loc) (μ : Heap), (∀ ℓ, μ ℓ ≠ none → ℓ ∈ d) →
      ∃ W : WRes, TW W [] [] ∧ ResU.Lower W μ ∧ ResU.Hash PMap.empty W
  | [], μ, hd => by
      have hμ : μ = fun _ => none := by
        funext ℓ
        by_contra h
        exact absurd (hd ℓ h) List.not_mem_nil
      subst hμ
      exact ⟨PMap.empty, TW.empty, Fig16.BoLo.lower_empty, Fig16.LogRel.hash_empty⟩
  | a :: d, μ, hd => by
      have hd' : ∀ ℓ, μ.del a ℓ ≠ none → ℓ ∈ d := by
        intro ℓ h
        by_cases hℓ : ℓ = a
        · subst hℓ; rw [BoCa.BoLo.Heap.del_same] at h; exact absurd rfl h
        · rw [BoCa.BoLo.Heap.del_other hℓ] at h
          rcases List.mem_cons.1 (hd ℓ h) with h' | h'
          · exact absurd h' hℓ
          · exact h'
      obtain ⟨W', hT', hlow', hh'⟩ := ownWorld_of_list d (μ.del a) hd'
      cases hμa : μ a with
      | none =>
          have : μ.del a = μ := by
            funext ℓ
            by_cases hℓ : ℓ = a
            · subst hℓ; rw [BoCa.BoLo.Heap.del_same, hμa]
            · rw [BoCa.BoLo.Heap.del_other hℓ]
          rw [this] at hlow'
          exact ⟨W', hT', hlow', hh'⟩
      | some v =>
          obtain ⟨x, σ', -, hfx, hσ', hT, hlow, -, -⟩ :=
            alloc_world (ρf := PMap.empty) (ps := []) (rs := []) v hh' (compS_empty_left W') hT'
              hlow' (BoCa.BoLo.Heap.del_same _ _)
          have hx := eq_of_compS_empty_left hσ'
          have hup : (μ.del a).upd a v = μ := by
            funext ℓ
            by_cases hℓ : ℓ = a
            · subst hℓ; rw [BoCa.BoLo.Heap.upd_same, hμa]
            · rw [BoCa.BoLo.Heap.upd_other hℓ, BoCa.BoLo.Heap.del_other hℓ]
          rw [hup] at hlow
          exact ⟨σ', hT, hlow, by rw [hx]; exact hfx⟩

/-- **The world that owns a memory with finitely many cells.** -/
theorem ownWorld {μ : Heap} (h : FinDom μ) :
    ∃ W : WRes, TW W [] [] ∧ ResU.Lower W μ ∧ ResU.Hash PMap.empty W := by
  obtain ⟨d, hd⟩ := h
  exact ownWorld_of_list d μ hd

/-- **A closed computation of `F_S 1`, every operation of `S` abortive and of a name in `FR` other
than `0`, runs alone from every finite memory**: every run of it continues to `()` or to a raise of
an operation of `S` that its context catches nothing of.  The memory's cells are `wpG`'s frame
(`ownWorld`); the run is a prefix of `wpG`'s run (`wpG_seg`), which ends at a value of `1` or at a
stop of `S`'s table, and that table admits no `perform`.  `[spec §19, §27]` -/
theorem finAlone_of_derives {S : Row} {FR : UInt32 → Prop}
    (hS : ∀ n i o, Row.find S n i = some o → o.abort = true ∧ n ≠ 0 ∧ FR n) {D : Expr}
    (h : CDerives LifeCtx.empty [] D (.comp (CTy.effOf S .unit))) {μ : Heap} (hfin : FinDom μ) :
    FinAlone (ℍ := ℍ) FR μ D := by
  intro μ₁ e₁ hs
  have hrel : cC (ℍ := ℍ) (CTy.effOf S .unit) [] LSub.empty D PMap.empty := by
    have hwp := fundamentalC (ℍ := ℍ) h LSub.empty [] [] PMap.empty Adequacy.models_empty
      (gDenC_nil _ _)
    have he : substAll [] D = D := Adequacy.psub_nil 0 D
    rw [he] at hwp
    exact hwp
  obtain ⟨W, hT, hlow, hh⟩ := ownWorld hfin
  have hw := ewp_unfold (opTable_mono _) ((cC_effOf S .unit [] LSub.empty D PMap.empty
    (Row.divB_of_find_abort fun n i o hf => (hS n i o hf).1)).mp hrel)
  obtain ⟨t, μ', ls', ρ', hrest, hΦ⟩ := wpG_seg hw (fun _ _ _ hp => post_irr hp)
    (ResU.hash_symm hh) (ResU.comp_empty_right W) hT (fun x hx => absurd hx List.not_mem_nil) hlow
    hs
  refine ⟨μ', t, hrest, ?_⟩
  rcases hΦ with ⟨v, rfl, hv⟩ | ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · left
    have hv' : v = Val.unit := hv.2
    subst hv'
    rfl
  · exfalso
    obtain ⟨⟨-, -, hen, hab⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp hen
    have := (hS n i o hf).1
    simp [OpSig.ent, this] at hab
  · right
    obtain ⟨⟨rfl, hK, hen, -⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, -⟩ := Option.map_eq_some_iff.mp hen
    obtain ⟨-, hn, hFR⟩ := hS n i o hf
    exact ⟨K, n, i, v, rfl, hK, hn, hFR⟩

/-- A finaliser that runs alone and lets no raise escape runs to `()`. -/
theorem FinAlone.finOK {μ : Heap} {D : Expr} (h : FinAlone (ℍ := ℍ) (fun _ => False) μ D) :
    FinOK (ℍ := ℍ) μ D := fun μ₁ t hs => by
  obtain ⟨μ', t', h', hend⟩ := h μ₁ t hs
  rcases hend with rfl | ⟨-, -, -, -, -, -, -, h⟩
  · exact ⟨μ', h'⟩
  · exact h.elim

/-- **A closed computation at a row that has no operation runs to `()` from every finite memory**:
`F_S 1`, `S` finding nothing (`F 1` among them).  `[spec §19, §24]` -/
theorem finOK_of_derives {S : Row} (hS : ∀ n i, Row.find S n i = none) {D : Expr}
    (h : CDerives LifeCtx.empty [] D (.comp (CTy.effOf S .unit))) {μ : Heap} (hfin : FinDom μ) :
    FinOK (ℍ := ℍ) μ D :=
  (finAlone_of_derives (FR := fun _ => False) (fun n i o hf => by rw [hS n i] at hf; cases hf) h
    hfin).finOK

/-- `finE D`: the finaliser `D` of a frame `ubind (N, D)` applied to `()`, read as its body when `D`
is a λ.  `[spec §19]` -/
def finE : Expr → Expr
  | .lam b => b.subst 0 Val.unit
  | e => .app e (.val .unit)

/-- **A finaliser typed at a row of abortive operations of names in `FR`**, the condition S5 reads
of a fired finaliser: `D ()`, read as `finE D`, is a closed computation of `F_S 1`, every operation
of `S` abortive and of a name in `FR` other than `0`.  At `FR = ∅` it is a closed computation of
`F 1` (option A, `finRow_A`).  `[spec §19, §27]` -/
def FinRow (FR : UInt32 → Prop) (D : Expr) : Prop :=
  ∃ S : Row, (∀ n i o, Row.find S n i = some o → o.abort = true ∧ n ≠ 0 ∧ FR n) ∧
    CDerives LifeCtx.empty [] (finE D) (.comp (CTy.effOf S .unit))

/-- At option A, a finaliser typed at `F 1`. -/
theorem finRow_A {D : Expr} (h : CDerives LifeCtx.empty [] (finE D) (.comp (.ret .unit))) :
    FinRow (fun _ => False) D :=
  ⟨[], fun _ _ _ hf => by simp [Row.find] at hf, h⟩

/-- **A finaliser typed at a row of abortive operations runs alone from every finite memory**
(`finAlone_of_derives`); at a λ, `D ()` first takes its β-step, its only step. -/
theorem finAlone_of_finRow {FR : UInt32 → Prop} {D : Expr} (h : FinRow FR D) {μ : Heap}
    (hfin : FinDom μ) : FinAlone (ℍ := ℍ) FR μ (.app D (.val .unit)) := by
  obtain ⟨S, hS, hd⟩ := h
  have hA := finAlone_of_derives (ℍ := ℍ) hS hd hfin
  cases D with
  | lam b =>
      intro μ₁ t hs
      have hβ := step1Only_plug (ℍ := ℍ) (Head.beta μ b Val.unit) rfl .hole
      rcases hβ.steps hs with ⟨h1, h2⟩ | hs'
      · subst μ₁ t
        obtain ⟨μ', t', h1, h2⟩ := hA μ (b.subst 0 Val.unit) (.refl _ _)
        exact ⟨μ', t', .more (Step1.head (Head.beta μ b Val.unit)) h1, h2⟩
      · exact hA μ₁ t hs'
  | _ => exact hA

/-- **A finaliser that lets no raise escape runs to `()` from every finite memory** (option A): a
finaliser typed at a row admitting no operation of a name in `∅`, so at a row that finds nothing.
`[spec §19, §24]` -/
theorem finOK_of_finRow {D : Expr} (h : FinRow (fun _ => False) D) {μ : Heap} (hfin : FinDom μ) :
    FinOK (ℍ := ℍ) μ (.app D (.val .unit)) :=
  (finAlone_of_finRow h hfin).finOK

/-! ### S5: the unwind and the cancel of a run, prefix-closed -/

/-- **The unwind, read prefix-closed** (S5): at a configuration a run from the empty memory
reaches, a raise `raise (n, …)`, `n ≠ 0`, pending under a context `K` with no running finaliser's
`cfin` frame, each of whose finalisers is typed at a row of abortive operations of names in `FR`
(`FinRow`): every path from there is a prefix of the unwind trace (`UnwindTr`).  `K`'s finalisers
fire innermost first, each by `[finalise]` and then running alone; one that returns hands the raise
on, and one whose raise escapes supersedes it.  The trace is over where a handler of the raise's
name catches it or where the raise leaves `K`.  `[spec §19]` -/
theorem unwind_prefix {e : Expr} {FR : UInt32 → Prop} {μ : Heap} {K₀ K : Kont} {n i : UInt32}
    {v : Val} (hreach : Steps (ℍ := ℍ) Adequacy.emptyMem e μ
      (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))))
    (hn : n ≠ 0) (hK : K.NoCfin) (hfin : ∀ D ∈ K.fins, FinRow FR D) {q : List (Heap × Expr)}
    (hq : Path (ℍ := ℍ) μ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) q) :
    UnwindTr (ℍ := ℍ) FR K₀ μ K (opPayload n i v) q :=
  unwind_pfx K₀ (q.length + 1) q (Nat.lt_succ_self _) μ K n i v
    (finDom_steps hreach finDom_empty) hn hK (fun D hD _ hμ => finAlone_of_finRow (hfin D hD) hμ)
    hq

/-- **The cancel, read prefix-closed** (S5): in a run of a term typed by a tied derivation, from
the empty memory, a configuration `c₀` cancels a continuation, `kappa H K` or
`kappaC hasCancel ℓ H K` (its cell), and a run from `c₀` reaches the start of its cancel run,
`K₀[cancelOf K]` (after the three administrative steps, and at the cell after `ℓ`'s release).  When
each of `K`'s finalisers is typed at a row of abortive operations of names in `FR`, names of `Ξ`:
every path from there is a prefix of the cancel trace of the dead region `K†` with nothing kept
(`CancelTr`).  The cancel is not interceptable: `K†` holds no handler and no `ccatch` frame
(`hasHnd_dead`, `noCC_dead`), so it stops only at `K`'s finalisers, which it fires innermost first,
each running alone, and at the running finalisers' `cfin` frames, which it passes (`[cfin-cancel]`);
the first kept error wins; and the canceller gets `()` or the kept error, an error of a name of `Ξ`,
re-raised. `[spec §19, §27]` -/
theorem cancel_prefix {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) {FR : UInt32 → Prop} (hFR : ∀ m, FR m → Ξ.Names m)
    {μ₀ μ : Heap} {K₀ : Kont} {H : Val} {K : Kont} {c₀ : Expr}
    (hc₀ : c₀ = K₀.plug (.app (kappa H K) (.val (Val.inj₂ .unit))) ∨
      ∃ hasCancel ℓ, c₀ = K₀.plug (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₂ .unit))))
    (h₀ : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₀ c₀)
    (hc : Steps (ℍ := ℍ) μ₀ c₀ μ (K₀.plug (cancelOf K)))
    (hfin : ∀ D ∈ K.fins, FinRow FR D) {q : List (Heap × Expr)}
    (hq : Path (ℍ := ℍ) μ (K₀.plug (cancelOf K)) q) :
    CancelTr (ℍ := ℍ) FR Ξ.Names K₀ μ K.dead none q := by
  have hN : KCfinNamed Ξ.Names K := cancelsNamed_of_derivesAt (ℍ := ℍ) h μ₀ c₀ h₀ K₀ H K hc₀
  have hfins : FinsAlone (ℍ := ℍ) FR K.dead := by
    intro D hD μ' hμ'
    rw [fins_dead] at hD
    exact finAlone_of_finRow (hfin D hD) hμ'
  exact cancel_pfx hFR K₀ (q.length + 1) q (Nat.lt_succ_self _) μ K.dead none
    (finDom_steps (h₀.trans hc) finDom_empty) (noCC_dead K) (hasHnd_dead 0 K)
    (kcfinNamed_dead hN) (.inl rfl) hfins hq

/-! ### Programs: the hypotheses met -/

namespace CancelIntercept

/-- `(raise 1) then x. x unwind raise 2`: the finaliser's raise of `2` supersedes the pending raise
of `1`. -/
def supersedeE : Expr := (uF (raiseU 2) .hole).plug (raiseU 1)

/-- The finaliser `λ_. raise 2` is typed at the row of an abortive `2`. -/
theorem finRow_raiseU2 : FinRow (· = 2) (finV (raiseU 2)).1 := by
  refine ⟨[rSig 2], fun n i o hf => ?_, ?_⟩
  · obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, by decide, rfl⟩
  · show CDerives LifeCtx.empty [] (raiseU 2) (.comp (CTy.effOf [rSig 2] .unit))
    exact .effRaise (o := rSig 2) rfl rfl .unit (.unitI .nil)

/-- The finalisers of `K m`, the region of `progT`: the one finaliser `λ_. raise m`. -/
theorem fins_K (m : UInt32) : (K m).fins = [(finV (raiseU m)).1] := rfl

/-- **`unwind_prefix` at `supersedeE`**: from the raise of `1` under the finaliser frame, every path
is a prefix of the unwind trace at finalisers that raise `2`. -/
theorem supersede_prefix {q : List (Heap × Expr)}
    (hq : Path (ℍ := ℍ) Adequacy.emptyMem supersedeE q) :
    UnwindTr (ℍ := ℍ) (· = 2) .hole Adequacy.emptyMem (uF (raiseU 2) .hole) (opPayload 1 0 Val.unit)
      q := by
  have hC : (uF (raiseU 2) .hole).NoCfin := by
    refine ⟨fun s h => ?_, trivial⟩
    simp only [Expr.app.injEq] at h
    exact absurd h.1 (fun h' => by cases h')
  refine unwind_prefix (e := supersedeE) (K₀ := .hole) (.refl _ _) (by decide) hC
    (fun D hD => ?_) hq
  · have hfins : (uF (raiseU 2) .hole).fins = [(finV (raiseU 2)).1] := rfl
    rw [hfins, List.mem_singleton] at hD
    subst hD
    exact finRow_raiseU2

/-- `ubind` occurs applied in the term. -/
def _root_.BoCa.Expr.hasUbind : Expr → Bool
  | .app (.prim .ubind) _ => true
  | .app a b | .pair a b | .seq a b | .letpair a b => a.hasUbind || b.hasUbind
  | .inj₁ a | .inj₂ a | .lam a => a.hasUbind
  | .case a b c => a.hasUbind || b.hasUbind || c.hasUbind
  | _ => false

theorem hasUbind_app_right (f : Expr) {Y : Expr} (h : Y.hasUbind = true) :
    (Expr.app f Y).hasUbind = true := by
  unfold Expr.hasUbind
  split
  · rfl
  · rename_i a b heq
    simp only [Expr.app.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [h]
  all_goals simp_all

theorem hasUbind_app_left {f : Expr} (Y : Expr) (h : f.hasUbind = true) :
    (Expr.app f Y).hasUbind = true := by
  unfold Expr.hasUbind
  split
  · rfl
  · rename_i a b heq
    simp only [Expr.app.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [h]
  all_goals simp_all

/-- A context keeps a `ubind` its hole holds. -/
theorem hasUbind_plug : ∀ (K : Kont) {X : Expr}, X.hasUbind = true → (K.plug X).hasUbind = true
  | .hole, _, h => h
  | .appR f K, _, h => hasUbind_app_right f (hasUbind_plug K h)
  | .appL K _, _, h => hasUbind_app_left _ (hasUbind_plug K h)
  | .pairL K _, _, h | .letpair K _, _, h | .seq K _, _, h => by
      simp [Kont.plug, Expr.hasUbind, hasUbind_plug K h]
  | .pairR _ K, _, h => by simp [Kont.plug, Expr.hasUbind, hasUbind_plug K h]
  | .case K _ _, _, h => by simp [Kont.plug, Expr.hasUbind, hasUbind_plug K h]
  | .inj₁ K, _, h | .inj₂ K, _, h => by simp [Kont.plug, Expr.hasUbind, hasUbind_plug K h]

/-- **Every run of `supersedeE` is a prefix of its three configurations**: `[finalise]`, then
the β-step of `λ_. raise 2`, then `raise 2; raise 1`, which has no step. -/
theorem supersedeE_runs {μ μ' : Heap} {c : Expr} (h : Steps (ℍ := ℍ) μ supersedeE μ' c) :
    μ' = μ ∧ (c = supersedeE ∨
      c = (pendK (opPayload 1 0 Val.unit)).plug (.app (.val (finV (raiseU 2))) (.val .unit)) ∨
      c = (pendK (opPayload 1 0 Val.unit)).plug (raiseU 2)) := by
  have h₁ := step1Only_plug (ℍ := ℍ) (Head.ufin μ idV (finV (raiseU 2)) 1 0 Val.unit .hole
    (by decide) rfl) rfl .hole
  rcases h₁.steps h with ⟨rfl, rfl⟩ | h
  · exact ⟨rfl, .inl rfl⟩
  have h₂ := step1Only_plug (ℍ := ℍ) (Head.beta μ (raiseU 2) Val.unit) rfl
    (pendK (opPayload 1 0 Val.unit))
  rcases h₂.steps h with ⟨rfl, rfl⟩ | h
  · exact ⟨rfl, .inr (.inl rfl)⟩
  have h' : Steps (ℍ := ℍ) μ ((pendK (opPayload 1 0 Val.unit)).plug
      (raiseE (.val (opPayload 2 0 Val.unit)))) μ' c := h
  obtain ⟨rfl, rfl⟩ := steps_irr (raise_irr (K := pendK (opPayload 1 0 Val.unit)) rfl) h'
  exact ⟨rfl, .inr (.inr rfl)⟩

/-- **A fired finaliser of `supersedeE` runs alone** to an uncaught raise of `2`: its only
finaliser frame is the one it starts in. -/
theorem finAloneAt_supersedeE : FinAloneAt (ℍ := ℍ) (· ≠ 0) supersedeE := by
  intro μ K₀ K N D n i v hreach hK μ' t hD hirr
  have hX : (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v))))).hasUbind = true :=
    hasUbind_app_left _ rfl
  obtain ⟨rfl, hc | hc | hc⟩ := supersedeE_runs hreach
  · have hD' : D = finV (raiseU 2) := by
      cases K₀ with
      | hole =>
          simp only [Kont.plug, supersedeE, ubindE, Expr.app.injEq] at hc
          exact (valPair_inj hc.1.2).2
      | appR f K₀' =>
          exfalso
          simp only [Kont.plug, supersedeE, ubindE, Expr.app.injEq] at hc
          have hnv : ¬ IsVal (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v))))) :=
            fun h => by cases h
          have h0 := plug_primApp hc.2 hnv
          subst h0
          simp only [Kont.plug, raiseU, BoCa.BoLo.raiseE, Expr.app.injEq] at hc
          exact absurd hc.2.1 (fun h => by cases h)
      | appL K₀' w =>
          exfalso
          simp only [Kont.plug, supersedeE, ubindE, Expr.app.injEq] at hc
          have hw : IsVal (raiseU 1) := hc.2 ▸ w.2
          cases hw
      | _ => simp [Kont.plug, supersedeE, ubindE] at hc
    subst hD'
    obtain ⟨μ'', t', hrest, hend⟩ :=
      finAlone_of_finRow (ℍ := ℍ) finRow_raiseU2 finDom_empty μ' t hD
    obtain ⟨rfl, rfl⟩ := steps_irr hirr hrest
    rcases hend with rfl | ⟨K', m, j, w, rfl, hK', hm0, -⟩
    · exact .inl IsVal.unit
    · exact .inr ⟨K', m, j, w, rfl, hK', hm0⟩
  · exact absurd (hc ▸ hasUbind_plug K₀ hX) (by decide)
  · exact absurd (hc ▸ hasUbind_plug K₀ hX) (by decide)

/-- **`finaliserOrder_at` at `supersedeE`**: every complete unwind its runs reach fires the
finaliser, whose raise of `2` supersedes the raise of `1`. -/
theorem supersede_finaliserOrder : FinaliserOrder (ℍ := ℍ) supersedeE :=
  finaliserOrder_at finAloneAt_supersedeE

/-- The effect context of `progOutT`: `1 : 1 ↠^unr 1` and `2 : 1 ↠^unr 0`. -/
def Ξ₁₂ : EffCtx := fun n => if n = 1 then [(.unr, .unit, .unit)] else
  if n = 2 then [(.unr, .unit, .zero)] else []

theorem opAt_rSig2 : OpAt Ξ₁₂ (rSig 2) := ⟨by decide, by simp [Ξ₁₂, rSig], by simp [Ξ₁₂, rSig]⟩

theorem opAt_pSig1 (F : CTy) : OpAt Ξ₁₂ (pSig 1 F) :=
  ⟨by simp [pSig], by simp [Ξ₁₂, pSig], by simp [Ξ₁₂, pSig]⟩

theorem rowAt_two (F : CTy) : RowAt Ξ₁₂ [rSig 2, pSig 1 F] := by
  refine rowAt_of_sigsAt fun o ho => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact opAt_rSig2
  · exact opAt_pSig1 F

theorem rowAt_two' (F : CTy) : RowAt Ξ₁₂ [pSig 1 F, rSig 2] := by
  refine rowAt_of_sigsAt fun o ho => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact opAt_pSig1 F
  · exact opAt_rSig2

theorem rowAt_r2 : RowAt Ξ₁₂ [rSig 2] := rowAt_left (S' := [pSig 1 (.ret .unit)]) (rowAt_two _)

theorem rowAt_p1 (F : CTy) : RowAt Ξ₁₂ [pSig 1 F] := rowAt_left (S' := [rSig 2]) (rowAt_two' F)

/-- `progT`'s `[then]`, tied to `Ξ₁₂` (`d_then₂`). -/
theorem dAt_then₂ {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂ Δ [] ((uF (raiseU 2) .hole).plug (performU 1))
      (.comp (CTy.effOf [rSig 2, pSig 1 (finR 2)] .unit)) := by
  show CDerivesAt Ξ₁₂ Δ [] (thenE (.var 0) (raiseU 2) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 2) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit)) (rowAt_p1 _) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 2) rowAt_r2 rfl rfl .unit (.unitI (.cons .nil))

/-- `hnd (2, H₂) [·]` around `progT`'s `[then]`, tied (`d_inner₂`). -/
theorem dAt_inner₂ {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂ Δ [] ((K 2).plug (performU 1)) (.comp (CTy.effOf [pSig 1 (finR 2)] .unit)) := by
  show CDerivesAt Ξ₁₂ Δ [] (hndExpr 2 [.unr] (.pair (.val idV) (.pair (.val (constC Val.unit))
    (.val Val.unit))) ((uF (raiseU 2) .hole).plug (performU 1))) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    (rowAt_two _) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_idV _ .unit)
      (.tensorI .nil (d_constC_raise _ (.unitI (.cons .nil))) (.unitI .nil))) rfl)
    (by decide) (by simp [pSig]) (by simp) rfl dAt_then₂

/-- **`progT` is typed by a tied derivation** at `Ξ₁₂`, at the row holding `2` (`d_progT`). -/
theorem dAt_progT {Δ : LifeCtx} : CDerivesAt Ξ₁₂ Δ [] progT (.comp (CTy.effOf [rSig 2] .unit)) := by
  show CDerivesAt Ξ₁₂ Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT)
    (.val Val.unit))) ((K 2).plug (performU 1))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 2)
    (rowAt_two' _) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_idV _ .unit)
      (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil))) rfl)
    (by decide) (by simp [rSig]) (by simp) rfl ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (finR 2).rowOf ++ [rSig 2] = [rSig 2, rSig 2] from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · refine .effSub (RowLe.of_mem fun o ho => ?_) dAt_inner₂
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 1 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- **`progOutT` is typed by a tied derivation** at `Ξ₁₂`, at `F (1 ⊕ 1)` (`d_progOutT`). -/
theorem dAt_progOutT {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂ Δ [] progOutT (.comp (.ret (.sum .unit .unit))) := by
  show CDerivesAt Ξ₁₂ Δ [] (hndExpr 2 [.unr] (.pair (.val injlV)
    (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit))) progT)
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    rowAt_r2 .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_injlV _ .unit .unit)
      (.tensorI .nil (d_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil))) rfl)
    (by decide) (by simp) (by simp) rfl dAt_progT

/-- The canceller's context in `progOutT`: the live handler of `2`. -/
abbrev K₂ₒ : Kont := hF (hU 2 injlV (constC (Val.inj₂ Val.unit))) .hole

/-- **`progOutT`'s run reaches the cancel of `κ`**: `H₁T`'s clause cancels the continuation of
`perform 1`, whose region is `K 2`. -/
theorem progOutT_cancels (μ : Heap) :
    Steps (ℍ := ℍ) μ progOutT μ
      (K₂ₒ.plug (.app (kappa H₁T (K 2)) (.val (Val.inj₂ .unit)))) := by
  let κv : Val := ⟨kappa H₁T (K 2), isVal_kappa _ _⟩
  show Steps μ (K₂ₒ.plug (hndE (hU 1 idV cancelCT) ((K 2).plug (performU 1)))) μ _
  refine Steps.plug K₂ₒ ?_
  refine .more (st .hole (Head.hop μ 1 0 (qualsVal [.unr]) idV (Val.pair cancelCT Val.unit)
    cancelCT Val.unit (K 2) (hcl cancelCT) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  show Steps μ (.app (.val (Val.lam (.app (.var 0) (.val (Val.inj₂ Val.unit)))))
    (Expr.subst 0 Val.unit (Expr.shift 1 0 κv.1))) μ _
  rw [subst_shift_one]
  exact .one (st .hole (Head.beta μ _ κv))

/-- **`cancel_prefix` at `progOutT`**: from the start of its cancel run, every path is a prefix of
the cancel trace of the dead region `(K 2)†`, whose finaliser raises `2`, at the names of
`Ξ₁₂`. -/
theorem progOutT_cancel_prefix {q : List (Heap × Expr)}
    (hq : Path (ℍ := ℍ) Adequacy.emptyMem (K₂ₒ.plug (cancelOf (K 2))) q) :
    CancelTr (ℍ := ℍ) (· = 2) Ξ₁₂.Names K₂ₒ Adequacy.emptyMem (K 2).dead none q := by
  refine cancel_prefix (dAt_progOutT (Δ := LifeCtx.empty)) (fun m hm => ?_) (.inl rfl)
    (progOutT_cancels Adequacy.emptyMem) (Steps.plug K₂ₒ (kappa_cancel_steps _ _ _))
    (fun D hD => ?_) hq
  · subst hm; decide
  · rw [fins_K, List.mem_singleton] at hD
    subst hD
    exact finRow_raiseU2

/-! #### At a cancellable raise: a context with no unrestricted abortive operation

`progOutTA` is `progOutT` with its raise of `2` cancellable (`rSigA 2`), every handler of `2` at the
tag `cancel`.  Its effect context `Ξ₁₂A`, `1 : 1 ↠^unr 1` and `2 : 1 ↠^cancel 0`, has no
unrestricted abortive operation (`noUnrExn_Ξ₁₂A`, decision 63's restriction), so a tied derivation
at it has the shape the checker gives every program it accepts (`checkProgram_tiedAt`).  A tied
derivation types it (`dAt_progOutTA`), its run cancels `κ` (`progOutTA_cancels`), and its region's
finaliser raises `2`: it meets `cancel_prefix`'s hypotheses (`progOutTA_cancel_prefix`). -/

/-- The effect context of `progOutTA`: `1 : 1 ↠^unr 1` and `2 : 1 ↠^cancel 0`. -/
def Ξ₁₂A : EffCtx := fun n => if n = 1 then [(.unr, .unit, .unit)] else
  if n = 2 then [(.cancel, .unit, .zero)] else []

/-- **`Ξ₁₂A` has no unrestricted abortive operation**: `1` resumes, and `2` is cancellable. -/
theorem noUnrExn_Ξ₁₂A : Ξ₁₂A.NoUnrExn := by
  intro n p hp hq
  unfold Ξ₁₂A at hp
  split at hp
  · simp only [List.mem_singleton] at hp; subst hp; rfl
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; simp at hq
    · cases hp

theorem opAt_rSigA2 : OpAt Ξ₁₂A (rSigA 2) :=
  ⟨by decide, by simp [Ξ₁₂A, rSigA], by simp [Ξ₁₂A, rSigA]⟩

theorem opAt_pSig1A (F : CTy) : OpAt Ξ₁₂A (pSig 1 F) :=
  ⟨by simp [pSig], by simp [Ξ₁₂A, pSig], by simp [Ξ₁₂A, pSig]⟩

theorem rowAt_twoA (F : CTy) : RowAt Ξ₁₂A [rSigA 2, pSig 1 F] := by
  refine rowAt_of_sigsAt fun o ho => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact opAt_rSigA2
  · exact opAt_pSig1A F

theorem rowAt_twoA' (F : CTy) : RowAt Ξ₁₂A [pSig 1 F, rSigA 2] := by
  refine rowAt_of_sigsAt fun o ho => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact opAt_pSig1A F
  · exact opAt_rSigA2

theorem rowAt_r2A : RowAt Ξ₁₂A [rSigA 2] :=
  rowAt_left (S' := [pSig 1 (.ret .unit)]) (rowAt_twoA _)

theorem rowAt_p1A (F : CTy) : RowAt Ξ₁₂A [pSig 1 F] :=
  rowAt_left (S' := [rSigA 2]) (rowAt_twoA' F)

/-- `progTA`'s `[then]`, tied to `Ξ₁₂A`: `perform 1 then x. x unwind raise 2` at `{2, 1⟨{2}⟩}`,
the raise cancellable. -/
theorem dAt_then₂A {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂A Δ [] ((uF (raiseU 2) .hole).plug (performU 1))
      (.comp (CTy.effOf [rSigA 2, pSig 1 (finRA 2)] .unit)) := by
  show CDerivesAt Ξ₁₂A Δ [] (thenE (.var 0) (raiseU 2) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSigA 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSigA, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finRA 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSigA 2, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finRA 2) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSigA 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun hc => by simp [capB, rSigA, VTy.isZero] at hc⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit)) (rowAt_p1A _) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSigA 2) rowAt_r2A rfl rfl .unit (.unitI (.cons .nil))

/-- `hnd (2, H₂) [·]` around `progTA`'s `[then]`, tied, `H₂`'s tag `cancel`. -/
theorem dAt_inner₂A {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂A Δ [] ((KA 2).plug (performU 1))
      (.comp (CTy.effOf [pSig 1 (finRA 2)] .unit)) := by
  show CDerivesAt Ξ₁₂A Δ [] (hndExpr 2 [.cancel] (.pair (.val idV) (.pair (.val (constC Val.unit))
    (.val Val.unit))) ((uF (raiseU 2) .hole).plug (performU 1))) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.cancel, .unit, .zero)]) (fs := finsNil)
    (rowAt_twoA _) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_idV _ .unit)
      (.tensorI .nil (d_constC_raise _ (.unitI (.cons .nil))) (.unitI .nil))) rfl)
    (by decide) (by simp [pSig]) (by simp) rfl dAt_then₂A

/-- **`progTA` is typed by a tied derivation** at `Ξ₁₂A`, at the row holding the cancellable `2`. -/
theorem dAt_progTA {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂A Δ [] progTA (.comp (CTy.effOf [rSigA 2] .unit)) := by
  show CDerivesAt Ξ₁₂A Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT)
    (.val Val.unit))) ((KA 2).plug (performU 1))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finRA 2)
    (rowAt_twoA' _) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_idV _ .unit)
      (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil))) rfl)
    (by decide) (by simp [rSigA]) (by simp) rfl ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (finRA 2).rowOf ++ [rSigA 2] = [rSigA 2, rSigA 2] from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨rSigA 2, rfl, OpSig.LeF.refl _⟩
  · refine .effSub (RowLe.of_mem fun o ho => ?_) dAt_inner₂A
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 1 (finRA 2), rfl, OpSig.LeF.refl _⟩

/-- **`progOutTA` is typed by a tied derivation** at `Ξ₁₂A`, at `F (1 ⊕ 1)`. -/
theorem dAt_progOutTA {Δ : LifeCtx} :
    CDerivesAt Ξ₁₂A Δ [] progOutTA (.comp (.ret (.sum .unit .unit))) := by
  show CDerivesAt Ξ₁₂A Δ [] (hndExpr 2 [.cancel] (.pair (.val injlV)
    (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit))) progTA)
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.cancel, .unit, .zero)]) (fs := finsNil)
    rowAt_r2A .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_injlV _ .unit .unit)
      (.tensorI .nil (d_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil))) rfl)
    (by decide) (by simp) (by simp) rfl dAt_progTA

/-- The canceller's context in `progOutTA`: the live cancellable handler of `2`. -/
abbrev K₂ₒA : Kont := hF (hQ 2 .cancel injlV (constC (Val.inj₂ Val.unit))) .hole

/-- The finalisers of `KA m`: the one finaliser `λ_. raise m`. -/
theorem fins_KA (m : UInt32) : (KA m).fins = [(finV (raiseU m)).1] := rfl

/-- **`progOutTA`'s run reaches the cancel of `κ`**: `H₁T`'s clause cancels the continuation of
`perform 1`, whose region is `KA 2`. -/
theorem progOutTA_cancels (μ : Heap) :
    Steps (ℍ := ℍ) μ progOutTA μ
      (K₂ₒA.plug (.app (kappa H₁T (KA 2)) (.val (Val.inj₂ .unit)))) := by
  let κv : Val := ⟨kappa H₁T (KA 2), isVal_kappa _ _⟩
  show Steps μ (K₂ₒA.plug (hndE (hU 1 idV cancelCT) ((KA 2).plug (performU 1)))) μ _
  refine Steps.plug K₂ₒA ?_
  refine .more (st .hole (Head.hop μ 1 0 (qualsVal [.unr]) idV (Val.pair cancelCT Val.unit)
    cancelCT Val.unit (KA 2) (hcl cancelCT) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  show Steps μ (.app (.val (Val.lam (.app (.var 0) (.val (Val.inj₂ Val.unit)))))
    (Expr.subst 0 Val.unit (Expr.shift 1 0 κv.1))) μ _
  rw [subst_shift_one]
  exact .one (st .hole (Head.beta μ _ κv))

/-- **`cancel_prefix` at `progOutTA`**, a program whose effect context has no unrestricted abortive
operation: from the start of its cancel run, every path is a prefix of the cancel trace of the
dead region `(KA 2)†`, whose finaliser raises `2`, at the names of `Ξ₁₂A`. -/
theorem progOutTA_cancel_prefix {q : List (Heap × Expr)}
    (hq : Path (ℍ := ℍ) Adequacy.emptyMem (K₂ₒA.plug (cancelOf (KA 2))) q) :
    CancelTr (ℍ := ℍ) (· = 2) Ξ₁₂A.Names K₂ₒA Adequacy.emptyMem (KA 2).dead none q := by
  refine cancel_prefix (dAt_progOutTA (Δ := LifeCtx.empty)) (fun m hm => ?_) (.inl rfl)
    (progOutTA_cancels Adequacy.emptyMem) (Steps.plug K₂ₒA (kappa_cancel_steps _ _ _))
    (fun D hD => ?_) hq
  · subst hm; decide
  · rw [fins_KA, List.mem_singleton] at hD
    subst hD
    exact finRow_raiseU2

end CancelIntercept

end BoCa.Fig16.LogRel.Core

end
