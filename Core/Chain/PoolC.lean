import Core.Chain.SI.CaptureAdequacy
import Core.Chain.SI.HandleN

/-!
# Pool-scheduler adequacy over the Capture relation  `[spec §62]`

**The guarantee** (`PoolSchedAdequacyC`, `poolSchedAdequacyC`). A closed program `(hnd H e₀) s₀`,
`H = hndVal n₀ qs hr hs` a scheduler meeting `SchedOKC` whose answers are functions of its state
(`PoolAnsC`), `s₀` the empty pool and `e₀` a task at `cerwp` at the scheduler's table, is safe or
diverges: every configuration it reaches steps or is a value, a value is reached only at the empty
memory, and every `free` finds its cell.

This is `PoolSchedAdequacyN` (`Core/Chain/PoolN.lean`) over `cerwp` (`SI/CaptureE.lean`), whose
stops keep lends open. What `cerwp` adds, and the pool carries:

* **Frame conditions.** A stopped task's continuation is resumed under the frame condition its run
  had, strengthened by its entry's `fd` at the payload (`contShareC`). A stored task records that
  condition (`StoredC.F`); a move that resumes it proves the condition of what it keeps beside it:
  the rest of the pool and the scheduler's bag. The scheduler's invariant `Inv` is read at the
  frame condition of the task whose answer is being applied, so a scheduler can say which frame
  conditions its tasks may carry when (`Core/Chain/PoolJoinC.lean`: a task resumed from a join is
  the only task).
* **Owned records.** Each stored task owns the records its stop owned (`StoredC.O`); the
  scheduler's run owns the running task's records and the pool's, kept pairwise apart (`RDisj`).
* **No garbage.** What a task holds when it ends is in its answer: the scheduler keeps it in a
  **bag** `D`, a resource beside the pool that `Inv` constrains. A resume may hand part of the bag
  to the resumed task as its answer's resource (a join hands back the borrows its children left).

**A scheduler answer** `f` is in `PoolAnsC Qc Q H Inv F` when, applied to any pool and bag meeting
`Inv F` whose entries answer in `PoolAnsC` below the index they are held at (`GoodC`), beside the
pool's and the bag's resource, it answers the program's `Q` at the empty table, under the empty
frame. Nothing fixes how many tasks the scheduler holds, in what order, or which it resumes or
cancels.

**What the scheduler must satisfy** is `SchedOKC` at `Qo = PoolAnsC Qc Q H Inv`: the premises of
`cerwp_schedHandle_le`, the `[handle]` rule for a scheduler at `cerwp` whose clauses get the stopped
task's continuation as `KapRelC`. A clause proves its case by the pool's moves: run a task under
the scheduler beside the pool and the bag (`poolAnsC_run_le`), park the stopped task
(`poolAnsC_park`), resume the top with part of the bag (`poolAnsC_resume`), cancel it
(`poolAnsC_cancel`), or the same at the second entry (`poolAnsC_resumeSnd`, `poolAnsC_cancelSnd`).

**How it is proved.** `cerwp_schedHandle_le` gives the handled task's answer in `PoolAnsC`; the pool
and the bag are framed beside the handled run (`cerwp_frameBindD`, at the empty table, so the run
never stops); applying the answer to the empty pool and bag answers `Q`, and `cerwp_adequacy`
closes the program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-! ### Tables -/

/-- `OpTabC.Down`'s cancel obligations, down any distance. -/
theorem OpTabC.Down.fin_le {T : OpTabC} (hT : T.Down) {n i : UInt32} {en : OpEntC}
    (hn : T n i = some en) {P : Nat → List SRec → Expr → WProp} (hP : en.fin = some P)
    {m k : Nat} (h : m ≤ k) {ls : List SRec} {e : Expr} {ρ : WRes} (hk : P k ls e ρ) :
    P m ls e ρ := by
  induction h with
  | refl => exact hk
  | step _ ih => exact ih (hT.fin _ _ _ _ hn hP _ _ _ _ hk)

/-- `T₁`'s stops up to `N` are `T₂`'s. -/
def InclLeC (N : Nat) (T₁ T₂ : OpTabC) : Prop :=
  ∀ (F : WRes → Prop) k, k ≤ N → ∀ ls O t (Ψ Ψ' : ContC) ρ,
    (∀ F' O' k', k' < k → ∀ ls e ρ, Ψ F' O' k' ls e ρ → Ψ' F' O' k' ls e ρ) →
    opTableC T₁ F k ls O t Ψ ρ → opTableC T₂ F k ls O t Ψ' ρ

/-- **A run at a table whose stops up to `N` are another's** is a run at the other. -/
theorem cerwp_tab_mono_le {T₁ T₂ : OpTabC} {N : Nat} (hI : InclLeC N T₁ T₂) {Q : PostCV} :
    ∀ n, n ≤ N → ∀ (F : WRes → Prop) ls O e ρ, cerwp (ℍ := ℍ) (opTableC T₁) Q F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC T₂) Q F n ls O e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN F ls O e ρ h
  rw [cerwp_eq] at h ⊢
  refine crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hI F k (by omega) ls' O' t _ _ ρ' (fun F' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) (by omega) F' ls'' O'' e'' ρ'' hΨ

/-- `T₁` is part of `T₂`: every entry of `T₁` is `T₂`'s at its key. -/
def OpTabC.Sub (T₁ T₂ : OpTabC) : Prop := ∀ m i en, T₁ m i = some en → T₂ m i = some en

theorem OpTabC.Sub.inclLe {T₁ T₂ : OpTabC} (h : T₁.Sub T₂) (N : Nat) : InclLeC N T₁ T₂ := by
  intro F k _ ls O t Ψ Ψ' ρ hΨ ht
  obtain ⟨K, n, i, v, en, hp⟩ := ht
  obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
  exact opTableC_local T₂ F k ls O t Ψ Ψ' ρ hΨ
    ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h n i en h₃, h₄, h₅⟩ ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩

/-- **A run at a part of a table** is a run at the table. -/
theorem cerwp_tab_sub {T₁ T₂ : OpTabC} (h : T₁.Sub T₂) {Q : PostCV} {F : WRes → Prop} {n : Nat}
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (he : cerwp (ℍ := ℍ) (opTableC T₁) Q F n ls O e ρ) :
    cerwp (ℍ := ℍ) (opTableC T₂) Q F n ls O e ρ :=
  cerwp_tab_mono_le (h.inclLe n) n le_rfl F ls O e ρ he

theorem OpTabC.emptyC_sub (T : OpTabC) : OpTabC.emptyC.Sub T := fun _ _ _ h => by cases h

/-! ### Owned records read by membership -/

/-- **`cerwp` reads the records it owns only through their members.** -/
theorem cerwp_perm {Tb : TableC} {Q : PostCV} {F : WRes → Prop} {n : Nat} {ls : List SRec}
    {O O' : List FrameRec} (hO : ∀ p, p ∈ O ↔ p ∈ O') {e : Expr} {ρ : WRes}
    (h : cerwp (ℍ := ℍ) Tb Q F n ls O e ρ) : cerwp (ℍ := ℍ) Tb Q F n ls O' e ρ := by
  rw [cerwp_eq] at h ⊢
  intro ρf fρ ps psF μ hF hf hc hS
  exact h ρf fρ ps psF μ hF hf hc ⟨fun p => (hS.1 p).trans (by rw [hO]),
    fun p hp => hS.2 p ((hO p).mp hp)⟩

/-- A postcondition read at the empty table: values only. -/
theorem cerwpE_post_mono {Q Q' : PostCV} (hQ : ∀ k ls O v ρ, Q k ls O v ρ → Q' k ls O v ρ)
    {F : WRes → Prop} {n : Nat} {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F n ls O e ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q' F n ls O e ρ := by
  rw [cerwp_eq] at h ⊢
  refine crwpG_mono (fun k ls' O' t ρ' ht => ?_) h
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact Or.inl ⟨v, rfl, hQ _ _ _ _ _ hv⟩
  · exact (opTableC_emptyC_false ht).elim

/-! ### The frame at the empty table, the records kept apart -/

/-- `crwpG_frame` with what it reads off the inner run's records: the records the framed run
ends owning are apart from the frame's. -/
theorem crwpG_frameD {F F₁ : WRes → Prop} {P : PostC} (R : List SRec → WRes → Prop)
    (hR : ∀ ls ls' ρ, R ls ρ → R ls' ρ) {n : Nat} {ls : List SRec} {O₁ O₂ : List FrameRec}
    (hO : ∀ p ∈ O₁, p ∉ O₂) {e : Expr} {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hF : ∀ ρf y, F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ₂ y → F₁ y)
    (hwp : crwpG (ℍ := ℍ) F₁ P n ls O₁ e ρ₁) (hR₂ : R ls ρ₂) :
    crwpG (ℍ := ℍ) F (fun k ls' O' t => fun ρ' => ∃ O₁', O' = O₁' ++ O₂ ∧
      (∀ p ∈ O₁', p ∉ O₂) ∧ (P k ls' O₁' t ⋆ R ls') ρ') n ls (O₁ ++ O₂) e ρ := by
  intro ρf fρ ps psF μ hFρ hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  have hS₁ : Split ps O₁ (O₂ ++ psF) := by
    refine ⟨fun p => ?_, fun p hp hp' => ?_⟩
    · rw [hS.1 p, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hp' with h | h
      · exact hO p hp h
      · exact hS.2 p (List.mem_append_left _ hp) h
  obtain ⟨ρ', fρ', ps', O₁', ls', g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩ :=
    hwp y fρ ps (O₂ ++ psF) μ (hF ρf y hFρ hf hy) hy₁ hyfρ hS₁ hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  have hvW : ResU.Valid fρ' := by obtain ⟨σ, hσ, -⟩ := g₃; exact ⟨σ, hσ⟩
  refine ⟨W, fρ', ps', O₁' ++ O₂, ls', ⟨(ResU.CompS.comm hfW).1, fρ', ResU.CompS.comm hfW, hvW⟩,
    hfW, g₃, ⟨fun p => ?_, fun p hp hp' => ?_⟩, g₅, g₆, O₁', rfl,
    fun p hp hp' => g₄.2 p hp (List.mem_append_left _ hp'), ρ', ρ₂, ResU.CompS.comm hW, g₇,
    hR ls ls' ρ₂ hR₂⟩
  · rw [g₄.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₄.2 p h (List.mem_append_right _ hp')
    · exact hS.2 p (List.mem_append_right _ h) hp'

/-- **A task run beside a resource at the empty table, then the rest**: `cerwp_frameBindE` with the
records the task ends owning apart from the frame's. -/
theorem cerwp_frameBindD {Q Q₁ : PostCV} {F F₁ : WRes → Prop} (R : WRes → Prop) (K : Kont)
    {n : Nat} {ls : List SRec} {O₁ O₂ : List FrameRec} (hO : ∀ p ∈ O₁, p ∉ O₂) {e : Expr}
    {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hF : ∀ ρf y, F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ₂ y → F₁ y)
    (h : cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q₁ F₁ n ls O₁ e ρ₁) (hR : R ρ₂)
    (hK : ∀ k ls' O₁' (v : Val) ρa ρb ρ', k ≤ n → (∀ p ∈ O₁', p ∉ O₂) → Q₁ k ls' O₁' v ρa →
      R ρb → ResU.CompS ρa ρb ρ' →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F k ls' (O₁' ++ O₂) (K.plug v.1) ρ') :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F n ls (O₁ ++ O₂) (K.plug e) ρ := by
  have hL := opTableC_local OpTabC.emptyC
  rw [cerwp_eq] at h ⊢
  refine crwpG_bind K (crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_)
    (crwpG_frameD (fun _ => R) (fun _ _ _ h => h) hO hcρ hF h hR))
  obtain ⟨O₁', rfl, hap, ρa, ρb, hc, ht, hRb⟩ := ht
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact cerwp_unfold_at hL hk (hK k ls' O₁' v ρa ρb ρ' hk hap hv hRb hc)
  · exact (opTableC_emptyC_false ht).elim

/-! ### `κ` as a scheduler's clause receives it -/

/-- The frame condition a stopped task is resumed under: its run's, and its entry's at the
payload. -/
def FdAnd (F : WRes → Prop) (en : OpEntC) (v : Val) : WRes → Prop := fun ρf => F ρf ∧ en.fd v ρf

/-- **A cancellable entry's cancel obligation at `cerwp`**: the cancel run caught at `ccatch`,
owning nothing, at the empty table, at every frame condition, answering `Qc`. -/
def PcanC (Qc : PostCV) : Nat → List SRec → Expr → WProp := fun k ls e ρ =>
  ∀ F : WRes → Prop, cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qc F k ls [] (ccatchE e) ρ

/-- **`κ` as a scheduler's clause receives it** (`KapRelN` at `cerwp`): resumed at every answer in
the entry's `PBv`, at every `k′ < k` and every list, under the frame condition the stopped run had
with the entry's `fd`, owning the records the stop owned, answering the scheduler's `Qo` at that
frame condition; and, at a cancellable entry, cancelled at every frame condition, answering `Qc`. -/
def KapRelC (Qo : (WRes → Prop) → PostCV) (Qc : PostCV) (en : OpEntC) (F : WRes → Prop) (k : Nat)
    (O : List FrameRec) (v κ : Val) : WProp := fun ρ =>
  ∀ (ls' : List SRec) k', k' < k →
    (∀ w : Val, (en.PBv v k' ls' w ─⋆
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (Qo (FdAnd F en v)) (FdAnd F en v) k' ls' O
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) ρ) ∧
    (en.q ≠ .lin → ∀ F' : WRes → Prop,
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qc F' k' ls' [] (.app κ.1 (.val (Val.inj₂ .unit))) ρ)

theorem kapRelC_le {Qo : (WRes → Prop) → PostCV} {Qc : PostCV} {en : OpEntC} {F : WRes → Prop}
    {k k' : Nat} (hk : k' ≤ k) {O : List FrameRec} {v κ : Val} {ρ : WRes}
    (h : KapRelC (ℍ := ℍ) Qo Qc en F k O v κ ρ) : KapRelC (ℍ := ℍ) Qo Qc en F k' O v κ ρ :=
  fun ls' k'' hk'' => h ls' k'' (by omega)

/-! ### What the scheduler must satisfy -/

/-- **A top-level scheduler `hnd (n₀, (qs, (h_ret, hs)))` at `cerwp`, meeting its clauses at the
stops up to `N`**, for tasks at the table `T` answering `Qin`, its answers `Qo F` at the frame
condition `F` of the run they come from, cancel runs answering `Qc`.

* `T` is downward closed and every operation of `T` is the scheduler's (`n₀`);
* every entry is non-abortive and not unrestricted, its qualifier tagged in `qs`, resumed at every
  list;
* a cancellable entry's cancel obligation is `PcanC Qc`, and its stop owns no record;
* `Qo F` and `Qc` are downward closed;
* the return clause, and every operation's clause, at the empty table, at every frame condition. -/
structure SchedOKCLe (N : Nat) (T : OpTabC) (n₀ : UInt32) (qs hr hs : Val) (Qin : PostCV)
    (Qo : (WRes → Prop) → PostCV) (Qc : PostCV) : Prop where
  down : T.Down
  names : ∀ m i en, T m i = some en → m = n₀
  ent : ∀ i en, T n₀ i = some en → en.abort = false ∧ en.q ≠ .unr ∧
    capTag qs.1 i.toNat = en.q.tag ∧ ∀ ls ls' ρ, en.wc ls ls' ρ
  fin : ∀ i en, T n₀ i = some en → en.q ≠ .lin →
    en.fin = some (PcanC (ℍ := ℍ) Qc) ∧ ∀ O, en.oc O → O = []
  qdown : ∀ F, (Qo F).Down
  qcdown : Qc.Down
  ret : ∀ (F : WRes → Prop) k, k ≤ N → ∀ ls O (v : Val) ρ, Qin k ls O v ρ →
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (Qo F) F k ls O (.app (.val hr) (.val v)) ρ
  op : ∀ i en, T n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
    ∀ (F : WRes → Prop) k, k ≤ N → ∀ ls O (v κ : Val) ρ, en.oc O →
      (en.PA k ls v ⋆ KapRelC (ℍ := ℍ) Qo Qc en F k O v κ) ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (Qo F) F k ls O
        (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **A scheduler meeting its clauses at every stop index**, proved by strong induction on `N`
when a clause runs a task under its own scheduler. -/
def SchedOKC (T : OpTabC) (n₀ : UInt32) (qs hr hs : Val) (Qin : PostCV)
    (Qo : (WRes → Prop) → PostCV) (Qc : PostCV) : Prop :=
  ∀ N, SchedOKCLe (ℍ := ℍ) N T n₀ qs hr hs Qin Qo Qc

/-- **`[handle]` for a scheduler at `cerwp`**, at every index up to `N`: `cerwp_gen`'s cases, by
induction on the index, the clause given `κ` as `KapRelC`. Resuming `κ` runs `hnd H K[w]`, which
the induction hypothesis covers below the stop's index; cancelling it runs the entry's cancel
obligation. -/
theorem cerwp_schedHandle_le {N : Nat} {T : OpTabC} {n₀ : UInt32} {qs hr hs : Val}
    {Qin : PostCV} {Qo : (WRes → Prop) → PostCV} {Qc : PostCV}
    (hS : SchedOKCLe (ℍ := ℍ) N T n₀ qs hr hs Qin Qo Qc) :
    ∀ n, n ≤ N → ∀ (F : WRes → Prop) ls O e ρ, cerwp (ℍ := ℍ) (opTableC T) Qin F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (Qo F) F n ls O
        (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin := opTableC_local T
  have hLout := opTableC_local OpTabC.emptyC
  have hDout := opTableC_down opTabC_emptyC_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN F ls O e ρ h
  set H := hndVal n₀ qs hr hs with hH
  have hPD := cerwpPost_down hDout (hS.qdown F)
  rw [cerwp_eq]
  show crwpG (ℍ := ℍ) F _ n ls O ((hndK H).plug e) ρ
  refine crwpG_bind (hndK H) ?_
  refine crwpG_mono_le (fun k hk ls' O' t σ ht => ?_) (cerwp_unfold_at hLin le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact crwpG_det (hPD _ F) (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (cerwp_unfold_at hLout hk (hS.ret F k (by omega) ls' O' v σ hv))
  · obtain ⟨⟨rfl, hK₁, hT, -, hoc⟩, ρa, ρk, hcak, hA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain rfl := hS.names m i en hT
    obtain ⟨-, hq, htag, hwc⟩ := hS.ent i en hT
    obtain ⟨c, hc, hob⟩ := hS.op i en hT
    refine crwpG_det (hPD _ F)
      (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
    rw [htag, kappaAt_cell hq]
    refine cerwp_unfold_at hLout hk (cerwp_kappaCell hLout hDout (hS.qdown F) _ H K₁
      (.appR (.val c) (.pairR v .hole)) (fun ℓ ρ' hc₂ => ?_))
    obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
    have hA' : en.PA (k - 1) ls' v ρa := by
      cases k with
      | zero => exact hA
      | succ k₀ => exact hS.down.pa _ _ _ hT _ _ _ _ hA
    refine hob F (k - 1) (by omega) ls' O' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ ρ' hoc
      ⟨ρa, y, hy₂, hA', fun ls'' k' hk' => ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' F' => ?_⟩⟩
    · -- resumed: the cell freed, `hnd H K₁[w]` from the share, by the induction hypothesis
      obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
      have h₁ := (hcont ls'' (hwc _ _ _)).1 k' (by omega) w τ₁ z hB hz
      simp only [cerwpC, show k' < n by omega, if_true] at h₁
      have h₂ := ih k' (by omega) (by omega) _ ls'' O' _ z h₁
      refine cerwp_kappaC_resume hLout hDout (hS.qdown _) _ ℓ H K₁ w
        (ResU.CompS.comm hzτ) ?_
      exact cerwp_le hLout hDout (hS.qdown _) (Nat.sub_le k' 1) h₂
    · -- cancelled: the cell freed, the entry's cancel obligation
      have hcc : cellCancel en.q = true := by
        cases e : en.q with
        | lin => exact absurd e hq'
        | cancel => rfl
        | unr => exact absurd e hq
      show cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qc F' k' ls'' []
        (.app (kappaC (cellCancel en.q) ℓ H K₁) (.val (Val.inj₂ .unit))) y
      rw [hcc]
      obtain ⟨hfin, -⟩ := hS.fin i en hT hq'
      have hP := (hcont ls'' (hwc _ _ _)).2 hq' _ hfin
      have hP' := hS.down.fin_le hT hfin (show k' - 1 ≤ k by omega) hP
      exact cerwp_kappaC_cancel hLout hDout hS.qcdown ℓ H K₁ (ResU.CompS.comm hy₁) (hP' F')

/-! ### The pool -/

/-- **A stored task**: what its continuation answers when resumed, at each frame condition (`Q`),
its entry, the frame condition its run had at the stop, the index of the stop, the records the
stop owned, the payload, its continuation, a condition the scheduler keeps on its share, and the
tag the scheduler's code stores beside it. -/
structure StoredC where
  Q : (WRes → Prop) → PostCV
  en : OpEntC
  F : WRes → Prop
  k : Nat
  O : List FrameRec
  v : Val
  κ : Val
  R : WRes → Prop
  tag : Val

/-- **The scheduler's stored tasks** as a list value, `inj₁ ((tag, κ), rest)` or `inj₂ ()`. -/
def poolValC : List StoredC → Val
  | [] => Val.inj₂ Val.unit
  | s :: ss => Val.inj₁ (Val.pair (Val.pair s.tag s.κ) (poolValC ss))

/-- **The scheduler's state**: its own handler value beside its stored tasks. -/
def stateValC (H : Val) (ss : List StoredC) : Val := Val.pair H (poolValC ss)

/-- **A stored task's share**: its continuation as a clause receives it, meeting the scheduler's
condition. -/
def EntryC (Qc : PostCV) (t : StoredC) : WProp := fun ρ =>
  KapRelC (ℍ := ℍ) t.Q Qc t.en t.F t.k t.O t.v t.κ ρ ∧ t.R ρ

/-- **The pool**: the separating conjunction of the stored tasks' shares. -/
def PoolC (Qc : PostCV) : List StoredC → WProp
  | [] => fun ρ => ρ = PMap.empty
  | t :: ts => EntryC (ℍ := ℍ) Qc t ⋆ PoolC Qc ts

/-- The records the stored tasks own. -/
def recsC : List StoredC → List FrameRec
  | [] => []
  | t :: ts => t.O ++ recsC ts

theorem mem_recsC {p : FrameRec} : ∀ {ts : List StoredC}, p ∈ recsC ts ↔ ∃ t ∈ ts, p ∈ t.O
  | [] => by simp [recsC]
  | t :: ts => by
      rw [recsC, List.mem_append, mem_recsC]
      constructor
      · rintro (h | ⟨u, hu, h⟩)
        · exact ⟨t, List.mem_cons_self, h⟩
        · exact ⟨u, List.mem_cons_of_mem _ hu, h⟩
      · rintro ⟨u, hu, h⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact .inl h
        · exact .inr ⟨u, hu, h⟩

/-- Lists of records pairwise apart. -/
def RDisj (l : List (List FrameRec)) : Prop := l.Pairwise (fun a b => ∀ p ∈ a, p ∉ b)

theorem RDisj.head {O : List FrameRec} {ts : List StoredC} (h : RDisj (O :: ts.map StoredC.O)) :
    ∀ p ∈ O, p ∉ recsC ts := by
  intro p hp hp'
  obtain ⟨t, ht, hpt⟩ := mem_recsC.mp hp'
  exact (List.pairwise_cons.mp h).1 t.O (List.mem_map.mpr ⟨t, ht, rfl⟩) p hp hpt

theorem RDisj.tail {O : List FrameRec} {L : List (List FrameRec)} (h : RDisj (O :: L)) :
    RDisj L := (List.pairwise_cons.mp h).2

theorem RDisj.cons {O : List FrameRec} {ts : List StoredC} (hO : ∀ p ∈ O, p ∉ recsC ts)
    (h : RDisj (ts.map StoredC.O)) : RDisj (O :: ts.map StoredC.O) := by
  refine List.pairwise_cons.mpr ⟨fun b hb p hp hpb => ?_, h⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  exact hO p hp (mem_recsC.mpr ⟨t, ht, hpb⟩)

theorem RDisj.drop2 {a b : List FrameRec} {L : List (List FrameRec)} (h : RDisj (a :: b :: L)) :
    RDisj (a :: L) :=
  List.Pairwise.sublist (List.Sublist.cons₂ a (List.sublist_cons_self b L)) h

theorem RDisj.swap {a b : List FrameRec} {L : List (List FrameRec)} (h : RDisj (a :: b :: L)) :
    RDisj (b :: a :: L) :=
  List.Pairwise.perm h (List.Perm.swap b a L) (by intro x y h p hp hp'; exact h p hp' hp)

theorem recsC_swap (t u : StoredC) (ts : List StoredC) (p : FrameRec) :
    p ∈ recsC (u :: t :: ts) ↔ p ∈ recsC (t :: u :: ts) := by
  simp only [recsC, List.mem_append]; tauto

theorem poolC_nil {Qc : PostCV} : PoolC (ℍ := ℍ) Qc [] PMap.empty := rfl

/-- **Exchange the two top entries**: the same resource. -/
theorem PoolC.swap {Qc : PostCV} {t u : StoredC} {ts : List StoredC} {ρ : WRes}
    (h : PoolC (ℍ := ℍ) Qc (t :: u :: ts) ρ) : PoolC (ℍ := ℍ) Qc (u :: t :: ts) ρ := by
  obtain ⟨a, bc, hc, ha, b, c, hbc, hb, hcp⟩ := h
  obtain ⟨ac, hac, hx⟩ := compS_lcomm hbc hc
  exact ⟨b, ac, hx, hb, a, c, hac, ha, hcp⟩

/-- The pool beside the bag, the two top entries exchanged. -/
theorem PoolC.swapD {Qc : PostCV} {t u : StoredC} {ts : List StoredC} {D ρ : WRes}
    (h : (PoolC (ℍ := ℍ) Qc (t :: u :: ts) ⋆ fun x => x = D) ρ) :
    (PoolC (ℍ := ℍ) Qc (u :: t :: ts) ⋆ fun x => x = D) ρ := by
  obtain ⟨a, b, hc, ha, hb⟩ := h
  exact ⟨a, b, hc, ha.swap, hb⟩

/-! ### Scheduler answers -/

/-- **A scheduler answer at index `k`**, from a run at the frame condition `F` owning `O`: `f`
applied to any pool and bag meeting `Inv F` whose entries are held at index at least `k` and
answer in `PoolAnsC` below `k`, beside the pool's and the bag's resource, the records apart,
answers `Q` at the empty table under the empty frame. -/
def PoolAnsAtC (Qc Q : PostCV) (H : Val) (Inv : (WRes → Prop) → List StoredC → WRes → Prop) :
    (F : WRes → Prop) → (k : Nat) → List SRec → List FrameRec → Val → WRes → Prop
  | F, k, ls, O, f, ρ =>
    ∀ (ts : List StoredC) (D σ ρ' : WRes), Inv F ts D →
      (∀ t ∈ ts, k ≤ t.k ∧ ∀ (j : Nat) (_hj : j < k) (F' : WRes → Prop) (ls' : List SRec)
        (O' : List FrameRec) (v : Val) (ρ'' : WRes), t.Q F' j ls' O' v ρ'' →
        ∀ (j' : Nat) (_hj' : j' ≤ j), PoolAnsAtC Qc Q H Inv F' j' ls' O' v ρ'') →
      (PoolC (ℍ := ℍ) Qc ts ⋆ fun x => x = D) σ → ResU.CompS ρ σ ρ' →
      RDisj (O :: ts.map StoredC.O) →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k ls (O ++ recsC ts)
        (.app f.1 (stateValC H ts).1) ρ'
termination_by _ k => k

/-- **A scheduler answer**: `PoolAnsAtC` at every index up to `k`. -/
def PoolAnsC (Qc Q : PostCV) (H : Val) (Inv : (WRes → Prop) → List StoredC → WRes → Prop)
    (F : WRes → Prop) : PostCV :=
  fun k ls O f ρ => ∀ j ≤ k, PoolAnsAtC (ℍ := ℍ) Qc Q H Inv F j ls O f ρ

theorem poolAnsC_down (Qc Q : PostCV) (H : Val) (Inv : (WRes → Prop) → List StoredC → WRes → Prop)
    (F : WRes → Prop) : (PoolAnsC (ℍ := ℍ) Qc Q H Inv F).Down :=
  fun _ _ _ _ _ h j hj => h j (by omega)

/-- **A stored task good at `k`**: held at index at least `k`, and answering a scheduler answer
at every index below `k`. -/
def GoodC (Qc Q : PostCV) (H : Val) (Inv : (WRes → Prop) → List StoredC → WRes → Prop) (k : Nat)
    (t : StoredC) : Prop :=
  k ≤ t.k ∧ ∀ j, j < k → ∀ (F' : WRes → Prop) (ls' : List SRec) (O' : List FrameRec) (v : Val)
    (ρ'' : WRes), t.Q F' j ls' O' v ρ'' → PoolAnsC (ℍ := ℍ) Qc Q H Inv F' j ls' O' v ρ''

theorem GoodC.le {Qc Q : PostCV} {H : Val} {Inv : (WRes → Prop) → List StoredC → WRes → Prop}
    {k k' : Nat} {t : StoredC} (h : GoodC (ℍ := ℍ) Qc Q H Inv k t) (hk : k' ≤ k) :
    GoodC (ℍ := ℍ) Qc Q H Inv k' t :=
  ⟨by have := h.1; omega, fun j hj => h.2 j (by omega)⟩

theorem poolAnsAtC_iff {Qc Q : PostCV} {H : Val} {Inv : (WRes → Prop) → List StoredC → WRes → Prop}
    {F : WRes → Prop} {k : Nat} {ls : List SRec} {O : List FrameRec} {f : Val} {ρ : WRes} :
    PoolAnsAtC (ℍ := ℍ) Qc Q H Inv F k ls O f ρ ↔
      ∀ (ts : List StoredC) (D σ ρ' : WRes), Inv F ts D →
        (∀ t ∈ ts, GoodC (ℍ := ℍ) Qc Q H Inv k t) →
        (PoolC (ℍ := ℍ) Qc ts ⋆ fun x => x = D) σ → ResU.CompS ρ σ ρ' →
        RDisj (O :: ts.map StoredC.O) →
        cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k ls (O ++ recsC ts)
          (.app f.1 (stateValC H ts).1) ρ' := by
  rw [PoolAnsAtC]
  constructor
  · intro h ts D σ ρ' hi hg
    exact h ts D σ ρ' hi fun t ht => ⟨(hg t ht).1,
      fun j hj F' ls' O' v ρ'' hq => (hg t ht).2 j hj F' ls' O' v ρ'' hq⟩
  · intro h ts D σ ρ' hi hg
    exact h ts D σ ρ' hi fun t ht => ⟨(hg t ht).1,
      fun j hj F' ls' O' v ρ'' hq => (hg t ht).2 j hj F' ls' O' v ρ'' hq⟩

/-! ### The pool's moves -/

/-- **Run**: a task `e` at the scheduler's table, at a frame condition `F` its frame (the pool and
the bag) meets, run under the scheduler beside the pool and the bag, the state applied to what it
answers. -/
theorem poolAnsC_run_le {N : Nat} {T : OpTabC} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qc Q : PostCV} {Inv : (WRes → Prop) → List StoredC → WRes → Prop}
    (hS : SchedOKCLe (ℍ := ℍ) N T n₀ qs hr hs Qin
      (PoolAnsC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv) Qc)
    {F : WRes → Prop} {ts : List StoredC} {D : WRes} {k : Nat} (hkN : k ≤ N)
    (hg : ∀ u ∈ ts, GoodC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv F ts D)
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ₁ σ ρ : WRes}
    (hP : (PoolC (ℍ := ℍ) Qc ts ⋆ fun x => x = D) σ) (hc : ResU.CompS ρ₁ σ ρ)
    (hd : RDisj (O :: ts.map StoredC.O)) (hF : F σ)
    (he : cerwp (ℍ := ℍ) (opTableC T) Qin F k ls O e ρ₁) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k ls (O ++ recsC ts)
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateValC (hndVal n₀ qs hr hs) ts).1) ρ := by
  have h₁ := cerwp_schedHandle_le hS k hkN F ls O e ρ₁ he
  refine cerwp_frameBindD (fun x => x = σ) (Kont.appL .hole (stateValC (hndVal n₀ qs hr hs) ts))
    hd.head hc (fun ρf y hρf _ hy => ?_) h₁ rfl
    (fun k₁ ls' O₁' v ρa ρb ρ' hk₁ hap hq hR hc' => ?_)
  · subst hρf
    obtain rfl := eq_of_compS_empty_left hy
    exact hF
  · subst hR
    exact poolAnsAtC_iff.mp (hq k₁ le_rfl) ts D _ ρ' hi (fun u hu => (hg u hu).le hk₁) hP hc'
      (RDisj.cons hap hd.tail)

/-- **Park**: the stopped task's continuation, as its clause receives it, joins the pool at its
top, good at every index up to its stop's, its share meeting `R`; the bag is kept. -/
theorem poolAnsC_park {Qc Q : PostCV} {H : Val} {Inv : (WRes → Prop) → List StoredC → WRes → Prop}
    {en : OpEntC} {F : WRes → Prop} {k : Nat} {O : List FrameRec} {v κ : Val}
    (R : WRes → Prop) (tag : Val) {ρk σ ρ D : WRes}
    (hκ : KapRelC (ℍ := ℍ) (PoolAnsC (ℍ := ℍ) Qc Q H Inv) Qc en F k O v κ ρk) (hR : R ρk)
    {j : Nat} (hj : j ≤ k) {ts : List StoredC} (hg : ∀ t ∈ ts, GoodC (ℍ := ℍ) Qc Q H Inv j t)
    (hP : (PoolC (ℍ := ℍ) Qc ts ⋆ fun x => x = D) σ) (hc : ResU.CompS ρk σ ρ) :
    (PoolC (ℍ := ℍ) Qc (⟨PoolAnsC (ℍ := ℍ) Qc Q H Inv, en, F, k, O, v, κ, R, tag⟩ :: ts) ⋆
      fun x => x = D) ρ ∧
    ∀ t ∈ (⟨PoolAnsC (ℍ := ℍ) Qc Q H Inv, en, F, k, O, v, κ, R, tag⟩ :: ts : List StoredC),
      GoodC (ℍ := ℍ) Qc Q H Inv j t := by
  obtain ⟨a, b, hab, ha, rfl⟩ := hP
  obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hab hc
  refine ⟨⟨x, b, hxρ, ⟨ρk, a, hx, ⟨hκ, hR⟩, ha⟩, rfl⟩, fun t ht => ?_⟩
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨hj, fun _ _ _ _ _ _ _ h => h⟩
  · exact hg t ht

/-- **Resume the top**: the pool's top task resumed at an answer `a` its entry accepts, with part
`σa` of the bag as the answer's resource; its frame (the rest of the pool and of the bag) meets
its frame condition; the rest of the pool, with the rest of the bag, meeting `Inv` at that
condition, handed to what it answers. -/
theorem poolAnsC_resume {Qc Q : PostCV} {H : Val}
    {Inv : (WRes → Prop) → List StoredC → WRes → Prop} {t : StoredC} {ts : List StoredC} {k' : Nat}
    (hg : ∀ u ∈ t :: ts, GoodC (ℍ := ℍ) Qc Q H Inv (k' + 1) u) {ls : List SRec}
    {D σa D' ρ : WRes} (hP : (PoolC (ℍ := ℍ) Qc (t :: ts) ⋆ fun x => x = D) ρ)
    (hD : ResU.CompS σa D' D) {a : Val} (hB : t.en.PBv t.v k' ls a σa)
    (hF : ∀ σr, PoolC (ℍ := ℍ) Qc ts σr → ∀ y, ResU.CompS σr D' y → FdAnd t.F t.en t.v y)
    (hi : Inv (FdAnd t.F t.en t.v) ts D') (hd : RDisj ((t :: ts).map StoredC.O)) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k' ls (recsC (t :: ts))
      (.app (.app (.app t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateValC H ts).1) ρ := by
  obtain ⟨p, d, hpd, ⟨ρt, ρr, hcp, ⟨hκ, -⟩, hPr⟩, rfl⟩ := hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).1; omega
  -- `(ρt ● ρr) ● (σa ● D') = (ρt ● σa) ● (ρr ● D')`
  obtain ⟨x₁, hx₁, hx₁ρ⟩ := compS_reassoc hcp hpd
  obtain ⟨y, hy, hσy⟩ := compS_lcomm hD hx₁
  obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hσy hx₁ρ
  have hres := (hκ ls k' hk).1 a σa x hB hx
  have hd' : RDisj (t.O :: ts.map StoredC.O) := by simpa using hd
  show cerwp (ℍ := ℍ) _ _ _ _ _ (t.O ++ recsC ts) ((Kont.appL .hole (stateValC H ts)).plug _) _
  refine cerwp_frameBindD (fun z => z = y) (Kont.appL .hole (stateValC H ts)) hd'.head hxρ
    (fun ρf z hρf _ hz => ?_) hres rfl (fun k₁ ls' O₁' v ρa ρb ρ' hk₁ hap hq hR hc' => ?_)
  · subst hρf
    obtain rfl := eq_of_compS_empty_left hz
    exact hF ρr hPr _ hy
  · subst hR
    have hfa := (hg t List.mem_cons_self).2 k₁ (by omega) _ ls' O₁' v ρa hq
    exact poolAnsAtC_iff.mp (hfa k₁ le_rfl) ts D' _ ρ' hi
      (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega)) ⟨ρr, D', hy, hPr, rfl⟩ hc'
      (RDisj.cons hap hd'.tail)

/-- **Cancel the top**: the pool's top task, at a cancellable entry, its stop owning no record, its
cancel branch run under the scheduler beside the rest of the pool and the bag, at a frame
condition they meet. -/
theorem poolAnsC_cancel {N : Nat} {T : OpTabC} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qc Q : PostCV} {Inv : (WRes → Prop) → List StoredC → WRes → Prop}
    (hS : SchedOKCLe (ℍ := ℍ) N T n₀ qs hr hs Qin
      (PoolAnsC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv) Qc)
    (hQc : ∀ k ls O v ρ, Qc k ls O v ρ → Qin k ls O v ρ)
    {t : StoredC} {ts : List StoredC} {k' : Nat} (hkN : k' ≤ N)
    (hg : ∀ u ∈ t :: ts, GoodC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv (k' + 1) u)
    {ls : List SRec} {D ρ : WRes} (hP : (PoolC (ℍ := ℍ) Qc (t :: ts) ⋆ fun x => x = D) ρ)
    (hq : t.en.q ≠ .lin) (hO : t.O = []) {F' : WRes → Prop} (hi : Inv F' ts D)
    (hF : ∀ σ, (PoolC (ℍ := ℍ) Qc ts ⋆ fun x => x = D) σ → F' σ)
    (hd : RDisj (ts.map StoredC.O)) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k' ls (recsC (t :: ts))
      (.app (hndE (hndVal n₀ qs hr hs) (.app t.κ.1 (.val (Val.inj₂ .unit))))
        (stateValC (hndVal n₀ qs hr hs) ts).1) ρ := by
  obtain ⟨p, d, hpd, ⟨ρt, ρr, hcp, ⟨hκ, -⟩, hPr⟩, hdD⟩ := hP
  have hdD' : d = D := hdD
  rw [hdD'] at hpd
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).1; omega
  obtain ⟨x₁, hx₁, hx₁ρ⟩ := compS_reassoc hcp hpd
  have hcan := (hκ ls k' hk).2 hq F'
  have he : cerwp (ℍ := ℍ) (opTableC T) Qin F' k' ls [] (.app t.κ.1 (.val (Val.inj₂ .unit))) ρt :=
    cerwp_tab_sub (OpTabC.emptyC_sub T) (cerwpE_post_mono hQc hcan)
  have hP' : (PoolC (ℍ := ℍ) Qc ts ⋆ fun x => x = D) x₁ := ⟨ρr, D, hx₁, hPr, rfl⟩
  have h := poolAnsC_run_le hS hkN (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega))
    hi hP' hx₁ρ (RDisj.cons (fun _ h => by cases h) hd) (hF _ hP') he
  show cerwp (ℍ := ℍ) _ _ _ _ _ (t.O ++ recsC ts) _ _
  rw [hO]
  exact h

/-- **Resume the second**: the pool's second task resumed, the first kept at the top of the rest
(`PoolC.swapD`, `cerwp_perm`). A park that resumes another task and keeps the parked one in its
place is this move after `poolAnsC_park`. -/
theorem poolAnsC_resumeSnd {Qc Q : PostCV} {H : Val}
    {Inv : (WRes → Prop) → List StoredC → WRes → Prop} {t u : StoredC} {ts : List StoredC}
    {k' : Nat} (hg : ∀ x ∈ t :: u :: ts, GoodC (ℍ := ℍ) Qc Q H Inv (k' + 1) x) {ls : List SRec}
    {D σa D' ρ : WRes} (hP : (PoolC (ℍ := ℍ) Qc (t :: u :: ts) ⋆ fun x => x = D) ρ)
    (hD : ResU.CompS σa D' D) {a : Val} (hB : u.en.PBv u.v k' ls a σa)
    (hF : ∀ σr, PoolC (ℍ := ℍ) Qc (t :: ts) σr → ∀ y, ResU.CompS σr D' y →
      FdAnd u.F u.en u.v y)
    (hi : Inv (FdAnd u.F u.en u.v) (t :: ts) D') (hd : RDisj ((t :: u :: ts).map StoredC.O)) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k' ls
      (recsC (t :: u :: ts))
      (.app (.app (.app u.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateValC H (t :: ts)).1) ρ :=
  cerwp_perm (recsC_swap t u ts) (poolAnsC_resume
    (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx)) (PoolC.swapD hP) hD hB hF hi
    (by simpa using (show RDisj (t.O :: u.O :: ts.map StoredC.O) by simpa using hd).swap))

/-- **Cancel the second**: the pool's second task cancelled, the first kept at the top of the
rest. A clause that parks the task it stopped and cancels another is this move after
`poolAnsC_park`. -/
theorem poolAnsC_cancelSnd {N : Nat} {T : OpTabC} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qc Q : PostCV} {Inv : (WRes → Prop) → List StoredC → WRes → Prop}
    (hS : SchedOKCLe (ℍ := ℍ) N T n₀ qs hr hs Qin
      (PoolAnsC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv) Qc)
    (hQc : ∀ k ls O v ρ, Qc k ls O v ρ → Qin k ls O v ρ)
    {t u : StoredC} {ts : List StoredC} {k' : Nat} (hkN : k' ≤ N)
    (hg : ∀ x ∈ t :: u :: ts, GoodC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv (k' + 1) x)
    {ls : List SRec} {D ρ : WRes} (hP : (PoolC (ℍ := ℍ) Qc (t :: u :: ts) ⋆ fun x => x = D) ρ)
    (hq : u.en.q ≠ .lin) (hO : u.O = []) {F' : WRes → Prop} (hi : Inv F' (t :: ts) D)
    (hF : ∀ σ, (PoolC (ℍ := ℍ) Qc (t :: ts) ⋆ fun x => x = D) σ → F' σ)
    (hd : RDisj ((t :: ts).map StoredC.O)) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun y => y = PMap.empty) k' ls
      (recsC (t :: u :: ts))
      (.app (hndE (hndVal n₀ qs hr hs) (.app u.κ.1 (.val (Val.inj₂ .unit))))
        (stateValC (hndVal n₀ qs hr hs) (t :: ts)).1) ρ :=
  cerwp_perm (recsC_swap t u ts) (poolAnsC_cancel hS hQc hkN
    (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx)) (PoolC.swapD hP) hq hO hi hF hd)

/-! ### The headline -/

/-- **Pool-scheduler adequacy over the Capture relation.** A closed program `(hnd H e₀) s₀`, `s₀`
the empty pool: the task `e₀` at `cerwp` at the scheduler's table `T`, from the empty list,
records and resource, under the trivial frame condition, at every index; the scheduler
`H = hndVal n₀ qs hr hs` meeting `SchedOKC` with its answers functions of its state
(`PoolAnsC Qc Q H Inv`, for any invariant `Inv` the empty pool and bag meet at the trivial frame
condition); the program's answers owning no record and holding only `imm` cells. -/
def PoolSchedAdequacyC : Prop :=
  ∀ (T : OpTabC) (n₀ : UInt32) (qs hr hs : Val) (Qin Qc Q : PostCV)
    (Inv : (WRes → Prop) → List StoredC → WRes → Prop) (e₀ : Expr),
    (∀ k ls O v ρ, Q k ls O v ρ → O = [] ∧ AllImm ρ) → Inv (fun _ => True) [] PMap.empty →
    SchedOKC (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAnsC (ℍ := ℍ) Qc Q (hndVal n₀ qs hr hs) Inv) Qc →
    (∀ n, cerwp (ℍ := ℍ) (opTableC T) Qin (fun _ => True) n [] [] e₀ (PMap.empty : WRes)) →
    OrDiverges (ℍ := ℍ)
      (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateValC (hndVal n₀ qs hr hs) []).1)

theorem poolSchedAdequacyC : PoolSchedAdequacyC (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ _ _ hQ hInv hS he => cerwp_adequacy hQ fun n =>
    poolAnsC_run_le (hS n) le_rfl (fun _ h => by cases h) hInv
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, poolC_nil, rfl⟩
      (ResU.comp_empty_right _) (List.pairwise_singleton _ _) trivial (he n)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
