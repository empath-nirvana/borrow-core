import Core.TreeWp
import Support.Model.Tree.World.ExtF

/-!
# The step-indexed relation with operations, over the tree world: `cerwpT`  `[spec §62]`

`cerwpT Tb Q Fb F n w ls O e`: `twp` at `F` whose postcondition is a value in `Q` or a stop the
table `Tb` allows, the stop owing the continuation below the index. A stop leaves a continuation
share and owes the continuation at every lower index (`cerwpTC`). It is Core's step-indexed
relation with operations read at the tree world:

* **A stop hands the table the base frame condition `Fb`**, not the one current at the stop: the
  continuation resumes at `fdAt en v Fb O′`, the base and the resumer's guarantee at the records
  the resumed run owns. A run resumed many times carries no history of what earlier resumers
  guaranteed: its frame condition at each resume reads only its records at that resume.

* **The resume world is any extension of the stop's world**, with the share, the list and the
  records the continuation owns re-read there (`contShareT`): the continuation is a Kripke wand.
  At `RR.refl` the resume is at the stop's own world, list and records.
* **The resume list is any list keeping the re-readings of the stop list's records the share
  reads** (`KeepRel`, `Support/Model/Tree/World/ExtF.lean`, departure D13 of
  `docs/new-core/scope-781.md` §8): a resumer whose world holds records opened since the stop, or
  no longer holds records the share does not read, ended by another branch, resumes at its own
  list. The stop list's re-reading with `extFT` against it (D10) is one such list
  (`contShareT_resume_ext`), the stop's re-read list another (`contShareT_resume_rr`).
* **The share keeps the operation's qualifier** (`contShareT`'s first and last clauses). At an
  unrestricted operation the share is empty; at an operation that is not strictly linear the share
  carries the entry's cancel obligation `fin`, run at the continuation's dead context from
  `raise (cancel)`. At a strictly linear (`lin`) operation it carries no cancel obligation: the
  continuation can only be resumed.
* **Owned records** (`O`, `oc`): `oc` says what the stopped branch may own at the stop, read at
  the stop's world.
* The resumer's guarantee `fd` and the payload-dependent answer `PBv` are read at the resume
  world; `fd` also reads the records the resumed run owns (`fdAt`), re-read at the world the frame
  is checked at, one list by `RecsRR.func` (`fdAt_iff`).

`opTableT` admits only non-abortive entries (`en.abort = false`), so a run at it never ends at a
raise or an abortive operation. Resuming a stored continuation inside a lend opened after the stop
(a graft) is a resume at the grafted world: `contShareT_resume` is that step, by the definition of
the share.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ccatchE)
/-! ### Tables -/

/-- A world-indexed predicate over values at a step index, reading the list. -/
abbrev TVProp : Type := Nat → (w : TWd) → List (SRecT w.K) → Val → TRes w.K → Prop

/-- An operation's entry over the tree world. -/
structure OpEntT where
  q : Qual
  abort : Bool
  PA : TVProp
  /-- The answer, read at the payload. -/
  PBv : Val → TVProp
  /-- Whether the continuation's cancel branch is owed: at a cancellable entry (`q ≠ lin`), the
  unwinding `ccatch (K†[raise …])` is owed as a continuation, like a resume (`contShareT`). -/
  fin : Bool
  /-- What the resumer guarantees of the frame at the resume, read at the payload and at the
  records the resumed run owns there. -/
  fd : Val → (w : TWd) → List (FrameRecT w.K) → TRes w.K → Prop
  /-- What the stopped branch may own at the stop. -/
  oc : (w : TWd) → List (FrameRecT w.K) → Prop

abbrev OpTabT := UInt32 → UInt32 → Option OpEntT

/-- What a stop owes: a continuation at a frame condition, a world, the records it owns, an
index, a list. -/
abbrev ContT : Type :=
  TFrame → (w : TWd) → List (FrameRecT w.K) → Nat → List (SRecT w.K) → Expr → TRes w.K → Prop

/-- A table: the stop at `t` at the world `w`, under `F`, at `k`, the list and the records owned,
owing `Ψ`. -/
abbrev TableT : Type :=
  TFrame → Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Expr → ContT →
    TRes w.K → Prop

/-- A postcondition over values. -/
abbrev TPostV : Type :=
  Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Val → TRes w.K → Prop

/-- A record list's re-reading is single-valued. -/
theorem RecsRR.func {K K' : WCactus} {Θ' : CodeTy} {O : List (FrameRecT K)} :
    ∀ {O₁ O₂ : List (FrameRecT K')}, RecsRR Θ' O O₁ → RecsRR Θ' O O₂ → O₁ = O₂ := by
  induction O with
  | nil => intro O₁ O₂ h₁ h₂; cases h₁; cases h₂; rfl
  | cons r O ih =>
      intro O₁ O₂ h₁ h₂
      cases h₁ with
      | cons a₁ t₁ =>
      cases h₂ with
      | cons a₂ t₂ => rw [RecRR.func a₁ a₂, ih t₁ t₂]

/-- **The frame condition at a resume**: `F`, and the resumer's guarantee read at the resumed run's
own records `O′`, re-read at the frame's world. -/
def fdAt (en : OpEntT) (v : Val) (F : TFrame) {w' : TWd} (O' : List (FrameRecT w'.K)) : TFrame :=
  fun w'' ρf => F w'' ρf ∧ ∀ O'' : List (FrameRecT w''.K), RecsRR w''.Θ O' O'' → en.fd v w'' O'' ρf

/-- **At the run's re-read records, `fdAt` is the guarantee at them**: the re-reading is
single-valued (`RecsRR.func`). -/
theorem fdAt_iff {en : OpEntT} {v : Val} {F : TFrame} {w' w'' : TWd}
    {O' : List (FrameRecT w'.K)} {O'' : List (FrameRecT w''.K)} (hO : RecsRR w''.Θ O' O'')
    (ρf : TRes w''.K) : fdAt en v F O' w'' ρf ↔ F w'' ρf ∧ en.fd v w'' O'' ρf :=
  ⟨fun ⟨hF, h⟩ => ⟨hF, h O'' hO⟩, fun ⟨hF, h⟩ => ⟨hF, fun _ h₂ => RecsRR.func hO h₂ ▸ h⟩⟩

/-- **The continuation's share at the tree world**: at every extension of the stop's world, on
the share's and the owned records' re-readings there, at every list `ls′` keeping the re-readings
of the records of the stop list `ls` the share reads (`KeepRel`), resumed at every answer at every
`k′ < k` under a frame meeting `F` and the entry's `fd`. At a cancellable entry (`q ≠ lin`, `fin`)
its cancel branch is owed the same way: the unwinding of `K` with its handler frames and cancel
delimiters removed (`K†`) is a run of the task, which may stop again at an operation (an effectful
finaliser) and come back as a stored continuation.

The resume list's condition reads only the stop list's records the share is relevant to: another
branch may end a record of its own that was open at the stop, and the share still resumes
(departure D13). -/
def contShareT (en : OpEntT) (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (K : Kont) (v : Val) (Ψ : ContT) : TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ →
    RecsRR w'.Θ O O' →
    (∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → Ψ (fdAt en v F O') w' O' k' ls'
        (K.plug (.val a)) σ') ∧
    (en.q ≠ .lin → en.fin = true → ∀ k', k' < k → Ψ (fdAt en v F O') w' O' k' ls'
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ')

/-- A stop at a non-abortive operation the table allows. -/
def opTableT (T : OpTabT) : TableT := fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ en.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.PA k w ls v ρa ∧ contShareT en F k w ls O K v Ψ ρk

/-- A table reads what is owed only below the index it stops at. -/
def TableT.Local (Tb : TableT) : Prop :=
  ∀ F k w ls O t (Ψ Ψ' : ContT) ρ,
    (∀ F' w' O' k', k' < k → ∀ ls' e ρ', Ψ F' w' O' k' ls' e ρ' → Ψ' F' w' O' k' ls' e ρ') →
    Tb F k w ls O t Ψ ρ → Tb F k w ls O t Ψ' ρ

theorem opTableT_local (T : OpTabT) : (opTableT T).Local := by
  intro F k w ls O t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩ := h
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu,
    fun w' ρ' ls' O' hE hr hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      hΨ _ _ _ k' hk _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).1 k' hk a σ σ' hB hcσ),
      fun hq hf k' hk => hΨ _ _ _ k' hk _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).2 hq hf k' hk)⟩⟩

/-! ### The relation -/

/-- A value in `Q`, or a stop the table allows. -/
def cerwpPostT (Tb : TableT) (Q : TPostV) (Ψ : ContT) (F : TFrame) : TPost :=
  fun k w ls O t ρ => (∃ v : Val, t = v.1 ∧ Q k w ls O v ρ) ∨ Tb F k w ls O t Ψ ρ

/-- **`cerwp` over the tree world**, at the base frame condition `Fb` and the present one `F`.
The run is `twp` at `F`; a stop hands the table `Fb`, so the continuation resumes at the
resumer's guarantee over `Fb` (`fdAt en v Fb O′`), and is again `cerwpT` at the base `Fb`. A
resumed run's frame condition is the base and what its resumer guarantees of the records it owns
at that resume, never what earlier resumers guaranteed of records it has since ended. -/
def cerwpT (Tb : TableT) (Q : TPostV) (Fb : TFrame) : TFrame → Nat → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Expr → TRes w.K → Prop
  | F, n, w, ls, O, e => twp (ℍ := ℍ) F (cerwpPostT Tb Q (fun F' w' O' k' ls' e' =>
      if _h : k' < n then cerwpT Tb Q Fb F' k' w' ls' O' e' else fun _ => False) Fb) n w ls O e
termination_by _ n => n

/-- What `cerwpT` at the base `Fb` at `N` owes below it. -/
def cerwpTC (Tb : TableT) (Q : TPostV) (Fb : TFrame) (N : Nat) : ContT := fun F' w' O' k' ls' e' =>
  if k' < N then cerwpT (ℍ := ℍ) Tb Q Fb F' k' w' ls' O' e' else fun _ => False

theorem cerwpT_eq (Tb : TableT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd)
    (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (e : Expr) :
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e =
      twp (ℍ := ℍ) F (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q Fb n) Fb) n w ls O e := by
  rw [cerwpT]
  congr 1

/-- **A table includes another**: every stop the first allows owing `Ψ`, the second allows owing
any `Ψ'` that `Ψ` gives below the stop's index. -/
def TableT.Incl (Tb₁ Tb₂ : TableT) : Prop :=
  ∀ F k w ls O t (Ψ Ψ' : ContT) ρ,
    (∀ F' w' O' k', k' < k → ∀ ls' e ρ', Ψ F' w' O' k' ls' e ρ' → Ψ' F' w' O' k' ls' e ρ') →
    Tb₁ F k w ls O t Ψ ρ → Tb₂ F k w ls O t Ψ' ρ

/-- An operation table whose entries another's contain is included in it. -/
theorem opTableT_incl {T₁ T₂ : OpTabT} (h : ∀ n i en, T₁ n i = some en → T₂ n i = some en) :
    TableT.Incl (opTableT T₁) (opTableT T₂) := by
  intro F k w ls O t Ψ Ψ' ρ hΨ ht
  obtain ⟨K, m, i, v, en, h₁, h₂, h₃, rest⟩ := ht
  exact opTableT_local T₂ F k w ls O t Ψ Ψ' ρ hΨ ⟨K, m, i, v, en, h₁, h₂, h m i en h₃, rest⟩

/-- **A run verified at a table is verified at every table including it**, by strong induction on
the index: each stop the smaller table allows the larger allows, owing the continuation again at
the larger table. -/
theorem cerwpT_table_mono {Tb₁ Tb₂ : TableT} (hI : TableT.Incl Tb₁ Tb₂) {Q : TPostV}
    {Fb : TFrame} : ∀ (n : Nat) (F : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K),
      cerwpT (ℍ := ℍ) Tb₁ Q Fb F n w ls O e ρ → cerwpT (ℍ := ℍ) Tb₂ Q Fb F n w ls O e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F w ls O e ρ h
  rw [cerwpT_eq] at h ⊢
  refine twp_mono_le (fun k hk w' ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hI Fb k w' ls' O' t _ _ ρ' (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) F' w'' ls'' O'' e'' ρ'' hΨ

theorem cerwpT_unfold_at {Tb : TableT} (hTb : Tb.Local) {Q : TPostV} {Fb F : TFrame}
    {n N : Nat} (hnN : n ≤ N) {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {e : Expr} {ρ : TRes w.K} (h : cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ) :
    twp (ℍ := ℍ) F (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q Fb N) Fb) n w ls O e ρ := by
  rw [cerwpT_eq] at h
  refine twp_mono_le (fun k hk w' ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb Fb k w' ls' O' t _ _ ρ' (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem cerwpT_fold_at {Tb : TableT} (hTb : Tb.Local) {Q : TPostV} {Fb F : TFrame}
    {n N : Nat} (hnN : n ≤ N) {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q Fb N) Fb) n w ls O e ρ) :
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ := by
  rw [cerwpT_eq]
  refine twp_mono_le (fun k hk w' ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb Fb k w' ls' O' t _ _ ρ' (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem cerwpT_zero {Tb : TableT} {Q : TPostV} {Fb F : TFrame} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} :
    cerwpT (ℍ := ℍ) Tb Q Fb F 0 w ls O e ρ := by
  rw [cerwpT_eq]; exact twp_zero

/-- **`cerwpT` is monotone along world extension**, with the list and records re-read. -/
theorem cerwpT_kripke {Tb : TableT} {Q : TPostV} {Fb F : TFrame} {n : Nat} {w w₁ : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ls₁ : List (SRecT w₁.K)}
    {O₁ : List (FrameRecT w₁.K)} {e : Expr} {ρ : TRes w.K} {ρ₁ : TRes w₁.K} (hE : w.Ext w₁ ρ)
    (hr : RRw (w := w) (w' := w₁) ρ ρ₁) (hl : SRecsRR w₁.Θ ls ls₁) (hO : RecsRR w₁.Θ O O₁)
    (h : cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ) : cerwpT (ℍ := ℍ) Tb Q Fb F n w₁ ls₁ O₁ e ρ₁ := by
  rw [cerwpT_eq] at h ⊢
  exact twp_kripke hE hr hl hO h

/-- A deterministic step in front of a `cerwpT`, paid. -/
theorem cerwpT_step {Tb : TableT} (hL : Tb.Local) {Q : TPostV} {Fb F : TFrame} {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e e' : Expr} {ρ : TRes w.K}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e' ρ) :
    cerwpT (ℍ := ℍ) Tb Q Fb F (n + 1) w ls O e ρ :=
  cerwpT_fold_at hL le_rfl (twp_step hdet (cerwpT_unfold_at hL (Nat.le_succ n) h))

/-- A value in the postcondition, at every extension. -/
theorem cerwpT_val {Tb : TableT} {Q : TPostV} {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v : Val} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      Q n w₀ ls₀ O₀ v ρ₀) :
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O v.1 ρ := by
  rw [cerwpT_eq]
  exact twp_here (fun μ => final_val μ v) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO =>
    Or.inl ⟨v, rfl, h w₀ ρ₀ ls₀ O₀ hE hr hl hO⟩

/-- **A stop at a non-abortive operation the table allows**, at every extension of the world. -/
theorem cerwpT_perform {T : OpTabT} {Q : TPostV} {Fb F : TFrame} (K : Kont) {m i : UInt32}
    {v : Val} {en : OpEntT} (hK : K.HasHnd m = false) (hT : T m i = some en)
    (ha : en.abort = false) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      en.oc w₀ O₀ ∧ ∃ ρa ρk : TRes w₀.K, ResUT.CompS ρa ρk ρ₀ ∧ en.PA n w₀ ls₀ v ρa ∧
        contShareT en Fb n w₀ ls₀ O₀ K v (cerwpTC (ℍ := ℍ) (opTableT T) Q Fb n) ρk) :
    cerwpT (ℍ := ℍ) (opTableT T) Q Fb F n w ls O (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [cerwpT_eq]
  refine twp_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK)
    fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => Or.inr ?_
  obtain ⟨hoc, ρa, ρk, hc, hA, hs⟩ := h w₀ ρ₀ ls₀ O₀ hE hr hl hO
  exact ⟨K, m, i, v, en, rfl, hK, hT, ha, hoc, ρa, ρk, hc, hA, hs⟩

/-! ### The resume -/

/-- **Resuming a stored continuation at a grown world**, with the share and owned records
re-read there, at any list keeping the records of the stop list the share reads: records opened
by others since the stop may be added, and records the share does not read dropped or ended. -/
theorem contShareT_resume {en : OpEntT} {F : TFrame} {k : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ls' : List (SRecT w'.K)}
    {O' : List (FrameRecT w'.K)} {K : Kont} {v : Val} {Ψ : ContT} {ρ : TRes w.K}
    {ρ' : TRes w'.K} (h : contShareT en F k w ls O K v Ψ ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hx : KeepRel w'.Θ ls ls' ρ)
    (hO : RecsRR w'.Θ O O') {k' : Nat} (hk : k' < k) {a : Val} {σ σ' : TRes w'.K}
    (hB : en.PBv v k' w' ls' a σ) (hc : ResUT.CompS ρ' σ σ') :
    Ψ (fdAt en v F O') w' O' k' ls' (K.plug (.val a)) σ' :=
  (h.2 w' ρ' ls' O' hE hr hx hO).1 k' hk a σ σ' hB hc

/-- **A share captured at `w` is a share at every extension of `w`**, on its re-reading, at any
list there keeping the records of `ls` the share reads. -/
theorem contShareT_kripke {en : OpEntT} {F : TFrame} {k : Nat} {w w₁ : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ls₁ : List (SRecT w₁.K)}
    {O₁ : List (FrameRecT w₁.K)} {K : Kont} {v : Val} {Ψ : ContT} {ρ : TRes w.K}
    {ρ₁ : TRes w₁.K} (h : contShareT en F k w ls O K v Ψ ρ) (hE : w.Ext w₁ ρ)
    (hr : RRw (w := w) (w' := w₁) ρ ρ₁) (hl : KeepRel w₁.Θ ls ls₁ ρ) (hO : RecsRR w₁.Θ O O₁)
    (hu : en.q = .unr → ρ₁ = PMap.empty) : contShareT en F k w₁ ls₁ O₁ K v Ψ ρ₁ :=
  ⟨hu, fun w' ρ' ls' O' hE' hr' hx hO' => h.2 w' ρ' ls' O' (hE.trans hr hE')
    (RRw.trans hE'.1 hr hr') (hl.trans hE'.1 hr hx) (hO.trans hE'.1 hO')⟩

/-- **The whole-list resume condition is admitted**: a resume at a re-reading `lsR` of the stop
list and any list `extFT` allows against it (the condition before D13) is a resume the share
admits (`keepRel_of_extFT`). -/
theorem contShareT_resume_ext {en : OpEntT} {F : TFrame} {k : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {lsR ls' : List (SRecT w'.K)}
    {O' : List (FrameRecT w'.K)} {K : Kont} {v : Val} {Ψ : ContT} {ρ : TRes w.K}
    {ρ' : TRes w'.K} (h : contShareT en F k w ls O K v Ψ ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hl : SRecsRR w'.Θ ls lsR) (hx : extFT lsR ls' ρ')
    (hO : RecsRR w'.Θ O O') {k' : Nat} (hk : k' < k) {a : Val} {σ σ' : TRes w'.K}
    (hB : en.PBv v k' w' ls' a σ) (hc : ResUT.CompS ρ' σ σ') :
    Ψ (fdAt en v F O') w' O' k' ls' (K.plug (.val a)) σ' :=
  contShareT_resume h hE hr (keepRel_of_extFT hl hr hx) hO hk hB hc

/-- **The tree world's own extension is admitted**: a resume at the re-reading of the stop's
list, the only list `TWd.Ext` and `SRecsRR` give, is a resume the share admits. -/
theorem contShareT_resume_rr {en : OpEntT} {F : TFrame} {k : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ls' : List (SRecT w'.K)}
    {O' : List (FrameRecT w'.K)} {K : Kont} {v : Val} {Ψ : ContT} {ρ : TRes w.K}
    {ρ' : TRes w'.K} (h : contShareT en F k w ls O K v Ψ ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hl : SRecsRR w'.Θ ls ls') (hO : RecsRR w'.Θ O O')
    {k' : Nat} (hk : k' < k) {a : Val} {σ σ' : TRes w'.K} (hB : en.PBv v k' w' ls' a σ)
    (hc : ResUT.CompS ρ' σ σ') :
    Ψ (fdAt en v F O') w' O' k' ls' (K.plug (.val a)) σ' :=
  contShareT_resume h hE hr (KeepRel.of_srecsRR hl ρ) hO hk hB hc

end BoCa.Fig16.Tree.Wp

end
