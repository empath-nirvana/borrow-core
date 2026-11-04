import HandleSpike.Handle

/-!
# Spike (#792): the cancel branch owed parametrically in the canceller

The change: `contShareT`'s cancel clause owes the unwinding `ccatch (K†[raise cancel])` not at
`Ψ` (the stopper's own continuation relation) and not at one fixed relation (`Fix.lean`), but
**at every canceller**: at every table `T′` and base frame condition `Fb′` meeting the entry's
canceller conditions, it is `cerwpP T′ Qunit Fb′`, answering `()` and holding nothing.

An entry's canceller condition (`CancelOK`) is: `T′` has the stopper's own table's entries at the
operations the finaliser may perform (`OpEntP.cn`), and `T′`'s payload relations are downward
closed. The stopper's own table is the share's parameter, so the entry need not name itself.

Because the cancel's table varies, the relation is defined directly by strong recursion on the
index (`cerwpP`), as `cerwpT`, the cancel clause owing `cerwpP T′ Qunit Fb′` below the index.
`twp` and `EndT` are unchanged.

`cerwpP_handle` is `[handle]` for every handler, forwarding cancellable operations included: a
forwarded stop's cancel is owed at the same canceller-parametric relation inside and outside the
handler, of the same unwinding (`dead_hndK`); a stop at the handler's own name is cancelled by the
clause under the handler again (`KapP`'s cancel clause, as `KapSchedT`'s), the unwinding run at the
inner table (the handler is its canceller) and the handler around it by the induction hypothesis
at `Qunit`. The one condition on forwarding: a forwarded entry's finaliser operations are the
outer table's too (`K†` removed the handler being passed).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike.Param
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE freeE)

/-! ### Entries, tables, the share -/

/-- An entry, and the operations its continuation's finaliser may perform (`cn`): a canceller's
table must agree with the stopper's there. -/
structure OpEntP where
  e : OpEntT
  cn : UInt32 → UInt32 → Prop

abbrev OpTabP := UInt32 → UInt32 → Option OpEntP

def OpTabP.empty : OpTabP := fun _ _ => none

/-- Every entry's payload relation is downward closed in the index. -/
def PADown (T : OpTabP) : Prop :=
  ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.e.PA (k + 1) w ls v ρ → en.e.PA k w ls v ρ

/-- **The canceller's condition**: its table `T′` has the stopper's `T`'s entries at the
finaliser's operations, and is downward closed. -/
def CancelOK (cn : UInt32 → UInt32 → Prop) (T T' : OpTabP) : Prop :=
  (∀ m i en, cn m i → T m i = some en → T' m i = some en) ∧ PADown T'

/-- The cancel's answer: `()`, owning nothing. -/
def Qunit : TPostV := fun _ _ _ O v ρ => v = Val.unit ∧ O = [] ∧ ρ = PMap.empty

theorem Qunit_down : Qunit.Down := fun _ _ _ _ _ _ h => h

/-- What a cancel is owed at: a canceller table and base, then a continuation relation. -/
abbrev ContP : Type := OpTabP → TFrame → ContT

/-- `κ`'s cancel branch: the unwinding of the dead region. -/
def cancelE (K : Kont) : Expr := ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))

/-- **`contShareT` with the cancel owed at every canceller.** -/
def contShareP (T : OpTabP) (en : OpEntP) (F : TFrame) (k : Nat) (w : TWd)
    (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (K : Kont) (v : Val) (Ψ : ContT)
    (Ψc : ContP) : TRes w.K → Prop := fun ρ =>
  (en.e.q = .unr → ρ = PMap.empty) ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ →
    RecsRR w'.Θ O O' →
    (∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.e.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → Ψ (fdAt en.e v F O') w' O' k' ls' (K.plug (.val a)) σ') ∧
    (en.e.q ≠ .lin → en.e.fin = true → ∀ k', k' < k → ∀ (T' : OpTabP) (Fb' : TFrame),
      CancelOK en.cn T T' → (∀ w₀ ρf, ResUT.Valid ρf → Fb' w₀ ρf) →
      Ψc T' Fb' (fdAt en.e v Fb' O') w' O' k' ls' (cancelE K) ρ')

/-- A stop at a non-abortive operation of `T`, its share `contShareP`. -/
def opTableP (T : OpTabP) (Ψc : ContP) : TableT := fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntP),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.e.abort = false ∧ en.e.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.e.PA k w ls v ρa ∧ contShareP T en F k w ls O K v Ψ Ψc ρk

/-- **`cerwpT` with the canceller-parametric share**, by strong recursion on the index. -/
def cerwpP : OpTabP → TPostV → TFrame → TFrame → Nat → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Expr → TRes w.K → Prop
  | T, Q, Fb, F, n, w, ls, O, e => twp (ℍ := ℍ) F (cerwpPostT
      (opTableP T (fun T' Fb' F' w' O' k' ls' e' =>
        if _h : k' < n then cerwpP T' Qunit Fb' F' k' w' ls' O' e' else fun _ => False))
      Q (fun F' w' O' k' ls' e' =>
        if _h : k' < n then cerwpP T Q Fb F' k' w' ls' O' e' else fun _ => False) Fb) n w ls O e
termination_by _ _ _ _ n => n

def cerwpPC (T : OpTabP) (Q : TPostV) (Fb : TFrame) (N : Nat) : ContT :=
  fun F' w' O' k' ls' e' =>
  if k' < N then cerwpP (ℍ := ℍ) T Q Fb F' k' w' ls' O' e' else fun _ => False

def cerwpPK (N : Nat) : ContP := fun T' Fb' F' w' O' k' ls' e' =>
  if k' < N then cerwpP (ℍ := ℍ) T' Qunit Fb' F' k' w' ls' O' e' else fun _ => False

/-- What `cerwpP` at `n` is: `twp` at the table owing both relations below `n`. -/
abbrev PostP (T : OpTabP) (Q : TPostV) (Fb : TFrame) (N : Nat) : TPost :=
  cerwpPostT (opTableP T (cerwpPK (ℍ := ℍ) N)) Q (cerwpPC (ℍ := ℍ) T Q Fb N) Fb

theorem cerwpP_eq (T : OpTabP) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd)
    (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (e : Expr) :
    cerwpP (ℍ := ℍ) T Q Fb F n w ls O e = twp (ℍ := ℍ) F (PostP (ℍ := ℍ) T Q Fb n) n w ls O e := by
  rw [cerwpP]
  rfl

/-- The table reads both relations only below the stop's index. -/
theorem opTableP_local {T : OpTabP} {Ψc Ψc' : ContP} {F : TFrame} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {t : Expr} {Ψ Ψ' : ContT} {ρ : TRes w.K}
    (hΨ : ∀ F' w' O' k', k' < k → ∀ ls' e ρ', Ψ F' w' O' k' ls' e ρ' → Ψ' F' w' O' k' ls' e ρ')
    (hΨc : ∀ T' Fb' F' w' O' k', k' < k → ∀ ls' e ρ', Ψc T' Fb' F' w' O' k' ls' e ρ' →
      Ψc' T' Fb' F' w' O' k' ls' e ρ')
    (h : opTableP T Ψc F k w ls O t Ψ ρ) : opTableP T Ψc' F k w ls O t Ψ' ρ := by
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩ := h
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu,
    fun w' ρ' ls' O' hE hr hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      hΨ _ _ _ k' hk _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).1 k' hk a σ σ' hB hcσ),
      fun hq hf k' hk T' Fb' hT' hFb' =>
        hΨc _ _ _ _ _ k' hk _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).2 hq hf k' hk T' Fb' hT' hFb')⟩⟩

theorem postP_le {T : OpTabP} {Q : TPostV} {Fb : TFrame} {n N : Nat} (hnN : n ≤ N) :
    ∀ k, k ≤ n → ∀ w ls O t ρ, PostP (ℍ := ℍ) T Q Fb n k w ls O t ρ →
      PostP (ℍ := ℍ) T Q Fb N k w ls O t ρ := by
  intro k hk w ls O t ρ ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (opTableP_local (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_)
      (fun T' Fb' F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    · simp only [cerwpPC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
      exact hΨ
    · simp only [cerwpPK, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
      exact hΨ

theorem postP_ge {T : OpTabP} {Q : TPostV} {Fb : TFrame} {n N : Nat} (hnN : n ≤ N) :
    ∀ k, k ≤ n → ∀ w ls O t ρ, PostP (ℍ := ℍ) T Q Fb N k w ls O t ρ →
      PostP (ℍ := ℍ) T Q Fb n k w ls O t ρ := by
  intro k hk w ls O t ρ ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (opTableP_local (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_)
      (fun T' Fb' F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    · simp only [cerwpPC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
      exact hΨ
    · simp only [cerwpPK, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
      exact hΨ

theorem cerwpP_unfold_at {T : OpTabP} {Q : TPostV} {Fb F : TFrame} {n N : Nat} (hnN : n ≤ N)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : cerwpP (ℍ := ℍ) T Q Fb F n w ls O e ρ) :
    twp (ℍ := ℍ) F (PostP (ℍ := ℍ) T Q Fb N) n w ls O e ρ := by
  rw [cerwpP_eq] at h
  exact twp_mono_le (postP_le hnN) h

theorem cerwpP_fold_at {T : OpTabP} {Q : TPostV} {Fb F : TFrame} {n N : Nat} (hnN : n ≤ N)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F (PostP (ℍ := ℍ) T Q Fb N) n w ls O e ρ) :
    cerwpP (ℍ := ℍ) T Q Fb F n w ls O e ρ := by
  rw [cerwpP_eq]
  exact twp_mono_le (postP_ge hnN) h

theorem postP_down {T : OpTabP} {Q : TPostV} (hQ : Q.Down) (hPA : PADown T) {Ψc : ContP}
    {Ψ : ContT} {F : TFrame} : (cerwpPostT (opTableP T Ψc) Q Ψ F).Down := by
  intro k w ls O t ρ h
  rcases h with ⟨v, hv, hq⟩ | ⟨K, m, i, v, en, ht, hK, hT, ha, hoc, ρa, ρk, hc, hA, hsh⟩
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ _ _ hq⟩
  · exact Or.inr ⟨K, m, i, v, en, ht, hK, hT, ha, hoc, ρa, ρk, hc, hPA m i en hT _ _ _ _ _ hA,
      hsh.1, fun w' ρ' ls' O' hE hr hx hO => ⟨fun k' hk' a σ σ' hB hcσ =>
        (hsh.2 w' ρ' ls' O' hE hr hx hO).1 k' (by omega) a σ σ' hB hcσ,
        fun hq hf k' hk' => (hsh.2 w' ρ' ls' O' hE hr hx hO).2 hq hf k' (by omega)⟩⟩

theorem cerwpP_det {T : OpTabP} {Q : TPostV} (hQ : Q.Down) (hPA : PADown T) {Fb F : TFrame}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e e' : Expr}
    {ρ : TRes w.K} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : cerwpP (ℍ := ℍ) T Q Fb F n w ls O e' ρ) : cerwpP (ℍ := ℍ) T Q Fb F n w ls O e ρ := by
  rw [cerwpP_eq] at h ⊢
  exact twp_det (postP_down hQ hPA) hdet h

theorem cerwpP_val {T : OpTabP} {Q : TPostV} {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v : Val} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      Q n w₀ ls₀ O₀ v ρ₀) :
    cerwpP (ℍ := ℍ) T Q Fb F n w ls O v.1 ρ := by
  rw [cerwpP_eq]
  exact twp_here (fun μ => final_val μ v) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO =>
    Or.inl ⟨v, rfl, h w₀ ρ₀ ls₀ O₀ hE hr hl hO⟩

/-- `()` owning nothing, at `Qunit`. -/
theorem cerwpP_unit {T : OpTabP} {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpP (ℍ := ℍ) T Qunit Fb F n w ls [] (Val.unit).1 PMap.empty :=
  cerwpP_val fun _ _ _ _ _ hr _ hO => by cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

theorem cerwpP_perform {T : OpTabP} {Q : TPostV} {Fb F : TFrame} (K : Kont) {m i : UInt32}
    {v : Val} {en : OpEntP} (hK : K.HasHnd m = false) (hT : T m i = some en)
    (ha : en.e.abort = false) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      en.e.oc w₀ O₀ ∧ ∃ ρa ρk : TRes w₀.K, ResUT.CompS ρa ρk ρ₀ ∧ en.e.PA n w₀ ls₀ v ρa ∧
        contShareP T en Fb n w₀ ls₀ O₀ K v (cerwpPC (ℍ := ℍ) T Q Fb n) (cerwpPK (ℍ := ℍ) n) ρk) :
    cerwpP (ℍ := ℍ) T Q Fb F n w ls O (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [cerwpP_eq]
  refine twp_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK)
    fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => Or.inr ?_
  obtain ⟨hoc, ρa, ρk, hc, hA, hs⟩ := h w₀ ρ₀ ls₀ O₀ hE hr hl hO
  exact ⟨K, m, i, v, en, rfl, hK, hT, ha, hoc, ρa, ρk, hc, hA, hs⟩

theorem cerwpP_frameCond_rel {T : OpTabP} {Q : TPostV} {Fb F F' : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hF : ∀ (w₀ : TWd) (O₀ : List (FrameRecT w₀.K)) ρf, RecsRR w₀.Θ O O₀ → F' w₀ ρf → F w₀ ρf)
    (h : cerwpP (ℍ := ℍ) T Q Fb F n w ls O e ρ) : cerwpP (ℍ := ℍ) T Q Fb F' n w ls O e ρ := by
  rw [cerwpP_eq] at h ⊢
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF'
  exact h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO (hF w₀ O₀ ρf hO hF')

/-- Resuming a share at a grown world (as `contShareT_resume`). -/
theorem contShareP_resume {T : OpTabP} {en : OpEntP} {F : TFrame} {k : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {K : Kont} {v : Val} {Ψ : ContT}
    {Ψc : ContP} {ρ : TRes w.K} (h : contShareP T en F k w ls O K v Ψ Ψc ρ) {ρ' : TRes w'.K}
    {ls' : List (SRecT w'.K)} {O' : List (FrameRecT w'.K)} (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hx : KeepRel w'.Θ ls ls' ρ) (hO : RecsRR w'.Θ O O')
    {k' : Nat} (hk : k' < k) {a : Val} {σ σ' : TRes w'.K} (hB : en.e.PBv v k' w' ls' a σ)
    (hc : ResUT.CompS ρ' σ σ') : Ψ (fdAt en.e v F O') w' O' k' ls' (K.plug (.val a)) σ' :=
  (h.2 w' ρ' ls' O' hE hr hx hO).1 k' hk a σ σ' hB hc

/-- **A run verified at a table is verified at every table including it**, by strong induction on
the index: a stop's resume is the induction hypothesis; its cancel is owed at every canceller of
the larger table, each a canceller of the smaller (`CancelOK` reads only inclusion). -/
theorem cerwpP_table_mono {T₁ T₂ : OpTabP} (hI : ∀ m i en, T₁ m i = some en → T₂ m i = some en)
    {Q : TPostV} {Fb : TFrame} : ∀ (n : Nat) (F : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K),
      cerwpP (ℍ := ℍ) T₁ Q Fb F n w ls O e ρ → cerwpP (ℍ := ℍ) T₂ Q Fb F n w ls O e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F w ls O e ρ h
  rw [cerwpP_eq] at h ⊢
  refine twp_mono_le (fun k hk w' ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ⟨K, m, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩
  · exact Or.inl ht
  refine Or.inr ⟨K, m, i, v, en, h₁, h₂, hI m i en h₃, h₄, h₅, ρa, ρk, hc, hA, hu,
    fun w'' ρ'' ls'' O'' hE hr hx hO => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
      fun hq hf k' hk' T' Fb' hT' hFb' => (hcont w'' ρ'' ls'' O'' hE hr hx hO).2 hq hf k' hk' T'
        Fb' ⟨fun m' i' en' hc' h' => hT'.1 m' i' en' hc' (hI m' i' en' h'), hT'.2⟩ hFb'⟩⟩
  have h₁ := (hcont w'' ρ'' ls'' O'' hE hr hx hO).1 k' hk' a σ σ' hB hcσ
  simp only [cerwpPC, show k' < n by omega, if_true] at h₁ ⊢
  exact ih k' (by omega) _ _ _ _ _ _ h₁

/-! ### The handler's interface -/

/-- **`κ` as a clause receives it**: resumed into the outer relation; at a cancellable entry,
its cancel branch run under the handler again, `hnd H (κ (inj₂ ()))`, also in the outer
relation (`KapSchedT`'s shape at the outer table `To`). -/
def KapP (To : OpTabP) (Qout : TPostV) (Fbo : TFrame) (M : BoCa.Loc → Prop) (en : OpEntP)
    (H : Val) (k : Nat) (w : TWd) (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (v κ : Val) :
    TRes w.K → Prop := fun ρ =>
  (en.e.q = .unr → ρ = PMap.empty) ∧ (∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K))
    (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.e.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → ∀ F' : TFrame, F'.Mono → (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpP (ℍ := ℍ) To Qout Fbo F' k' w' ls' O'
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) σ') ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    en.e.q ≠ .lin → en.e.fin = true → ∀ k', k' < k → ∀ F' : TFrame, F'.Mono →
      (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpP (ℍ := ℍ) To Qout Fbo F' k' w' ls' O'
        (hndE H (.app κ.1 (.val (Val.inj₂ .unit)))) ρ'

def RetP (To : OpTabP) (Qin Qout : TPostV) (Fbo : TFrame) (hr : Val) : Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v : Val) (ρ : TRes w.K), F.Mono →
    (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) → Qin k w ls O v ρ →
    cerwpP (ℍ := ℍ) To Qout Fbo F k w ls O (.app (.val hr) (.val v)) ρ

def ClauseP (To : OpTabP) (H : Val) (Qout : TPostV) (Fbo : TFrame) (en : OpEntP) (c : Val) :
    Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v κ : Val) (ρ : TRes w.K), F.Mono →
    en.e.oc w O → (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
    (∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧ en.e.PA k w ls v ρa ∧
      KapP (ℍ := ℍ) To Qout Fbo (recMask O) en H k w ls O v κ ρk) →
    cerwpP (ℍ := ℍ) To Qout Fbo F k w ls O (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **What a handler `hnd (n₀, (qs, (h_ret, hs)))` between `T` and `To` must satisfy**:

* (forwarding) every operation of `T` of another name is `To`'s, the same entry, and the entries
  of `T` at its finaliser's operations are `To`'s;
* the tags; every entry's `fd` is the join's;
* `Qout` and both tables downward closed;
* the return clause at the inner answer and at the cancel's answer `Qunit`;
* the clauses. -/
def HandleOKP (T To : OpTabP) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : TPostV) (Fbo : TFrame) :
    Prop :=
  (∀ m i en, m ≠ n₀ → T m i = some en →
    To m i = some en ∧ ∀ m' i' en', en.cn m' i' → T m' i' = some en' → To m' i' = some en') ∧
  (∀ i en, T n₀ i = some en → en.e.abort = false → capTag qs.1 i.toNat = en.e.q.tag) ∧
  (∀ m i en, T m i = some en → ∀ v w O ρf, en.e.fd v w O ρf ↔ fdJoinT v w O ρf) ∧
  Qout.Down ∧ PADown To ∧ PADown T ∧
  RetP (ℍ := ℍ) To Qin Qout Fbo hr ∧ RetP (ℍ := ℍ) To Qunit Qout Fbo hr ∧
  (∀ i en, T n₀ i = some en →
    ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ClauseP (ℍ := ℍ) To (hndVal n₀ qs hr hs) Qout Fbo en c)

/-! ### `[handle]` -/

/-- **`[handle]` for every handler at the canceller-parametric share**, forwarding cancellable
operations included, by induction on the index, the inner answer `Q` any the return clause
accepts (the cancel's run is the induction hypothesis at `Qunit`). -/
theorem cerwpP_handle {T To : OpTabP} {n₀ : UInt32} {qs hr hs : Val} {Qin Qout : TPostV}
    {Fbo : TFrame} (hOK : HandleOKP (ℍ := ℍ) T To n₀ qs hr hs Qin Qout Fbo) (hFbo : Fbo.Mono) :
    ∀ (n : Nat) (Q : TPostV), RetP (ℍ := ℍ) To Q Qout Fbo hr →
      ∀ (M : BoCa.Loc → Prop) (F Fb Fe : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K), F.Mono →
      (∀ w' ρf, F w' ρf → fdMask M w' ρf) → (∀ x, recMask O x → M x) →
      (∀ w' ρf, ResUT.Valid ρf → Fb w' ρf) → (∀ w' ρf, fdMask M w' ρf → Fe w' ρf) →
      cerwpP (ℍ := ℍ) T Q Fb Fe n w ls O e ρ →
      cerwpP (ℍ := ℍ) To Qout Fbo F n w ls O (hndE (hndVal n₀ qs hr hs) e) ρ := by
  obtain ⟨hfw, htag, hfd, hQd, hPA, hPAT, -, hretU, hop⟩ := hOK
  have hPd : ∀ (Ψc : ContP) (Ψ : ContT), (cerwpPostT (opTableP To Ψc) Qout Ψ Fbo).Down :=
    fun _ _ => postP_down hQd hPA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hret M F Fb Fe w ls O e ρ hFm hFM hOM hFb hFe h
  rw [cerwpP_eq] at h ⊢
  have hFe₀ : ∀ (m i : UInt32) (en : OpEntP), T m i = some en → ∀ (v : Val) (w'' : TWd)
      (O'' : List (FrameRecT w''.K)) w₃ ρf, fdMask (recMask O'') w₃ ρf →
      fdAt en.e v Fb O'' w₃ ρf :=
    fun m i en hT v w'' O'' w₃ ρf hf => ⟨hFb w₃ ρf hf.1,
      fun O₃ hO₃ => (hfd m i en hT v w₃ O₃ ρf).mpr (fdMask_le (fun x hx =>
        (recMask_rr hO₃ x).mpr hx) hf)⟩
  have hFe' : ∀ (m i : UInt32) (en : OpEntP), T m i = some en → ∀ (v : Val) (w' : TWd)
      (O' : List (FrameRecT w'.K)) (w'' : TWd) (O'' : List (FrameRecT w''.K)),
      RecsRR w''.Θ O' O'' → ∀ w₃ ρf, fdMask (recMask O') w₃ ρf → fdAt en.e v Fb O'' w₃ ρf :=
    fun m i en hT v w' O' w'' O'' hO w₃ ρf hf => hFe₀ m i en hT v w'' O'' w₃ ρf
      (fdMask_le (fun x hx => (recMask_rr hO x).mpr hx) hf)
  show twp (ℍ := ℍ) F _ n w ls O ((hndK (hndVal n₀ qs hr hs)).plug e) ρ
  refine twp_bind_fdAt hFm (fun w ρf hf => hFe w ρf (hFM w ρf hf)) (hndK (hndVal n₀ qs hr hs))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2.mono hOM) h
    (fun k hk w' ls' O' t ρ' hcov' _ hls' hO' ht => ?_)
  have hF'm : (F.and (fdMask (recMask O'))).Mono := TFrame.and_mono hFm (fdMask_mono _)
  have hF'M : ∀ w'' ρf, (F.and (fdMask (recMask O'))) w'' ρf → fdMask (recMask O') w'' ρf :=
    fun _ _ hf => hf.2
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    refine twpAt_of_twp (twp_det (hPd _ _)
      (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole) ?_)
    exact cerwpP_unfold_at hk (hret _ k w' ls' O' v ρ' hF'm hF'M hcov' hls' hO' hv)
  obtain ⟨K₁, m, i, v, en, rfl, hK₁, hTe, ha, hoc, ρa, ρk, hcak, hA, hsh⟩ := ht
  by_cases hm : m = n₀
  swap
  · -- an operation of another name passes outward, its cancel owed at the same cancellers
    obtain ⟨hTo, hcn⟩ := hfw m i en hm hTe
    have hK : ((hndK (hndVal n₀ qs hr hs)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
    have e₁ : ∀ x, (hndK (hndVal n₀ qs hr hs)).plug (K₁.plug x) =
        ((hndK (hndVal n₀ qs hr hs)).comp K₁).plug x := fun x => (Kont.plug_comp _ _ _).symm
    rw [e₁]
    refine twpAt_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr
      ⟨(hndK (hndVal n₀ qs hr hs)).comp K₁, m, i, v, en, rfl, hK, hTo, ha, hoc, ρa, ρk, hcak, hA,
        hsh.1, fun w'' ρk' ls'' O'' hE hr' hx hO => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
        fun hq hf k' hk' T' Fb' hT' hFb' => ?_⟩⟩)
    · have h₁ := contShareP_resume hsh hE hr' hx hO hk' hB hcσ
      simp only [cerwpPC, show k' < n by omega, if_true] at h₁ ⊢
      rw [← e₁]
      refine cerwpP_frameCond_rel (F := Fbo.and (fdMask (recMask O'')))
        (fun w₀ O₀ ρf hO₀ hf => ⟨hf.1, fdMask_le (fun x hx => (recMask_rr hO₀ x).mp hx)
          ((hfd m i en hTe v w₀ O₀ ρf).mp (hf.2 O₀ hO₀))⟩) ?_
      exact ih k' (by omega) Q hret (recMask O'') (Fbo.and (fdMask (recMask O''))) Fb
        (fdAt en.e v Fb O'') w'' ls'' O'' _ σ' (TFrame.and_mono hFbo (fdMask_mono _))
        (fun _ _ hf => hf.2) (fun _ hx => hx) hFb (hFe₀ m i en hTe v w'' O'') h₁
    · have hT'' : CancelOK en.cn T T' :=
        ⟨fun m' i' en' hc h' => hT'.1 m' i' en' hc (hcn m' i' en' hc h'), hT'.2⟩
      have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).2 hq hf k' hk' T' Fb' hT'' hFb'
      unfold cancelE at h₁ ⊢
      rwa [dead_comp, dead_hndK]
  subst hm
  obtain ⟨c, hc, hcl⟩ := hop i en hTe
  refine twpAt_of_twp (twp_det (hPd _ _)
    (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_)
  have hres : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
      (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
      KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' →
      ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w''.K), en.e.PBv v k' w'' ls'' a σ →
      ResUT.CompS ρk' σ σ' → ∀ F'' : TFrame, F''.Mono →
      (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
      cerwpP (ℍ := ℍ) To Qout Fbo F'' k' w'' ls'' O''
        (hndE (hndVal m qs hr hs) (K₁.plug (.val a))) σ' := by
    intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
    have h₁ := contShareP_resume hsh hE hr' hx hO hk' hB hcσ
    simp only [cerwpPC, show k' < n by omega, if_true] at h₁
    exact ih k' (by omega) Q hret (recMask O') F'' Fb (fdAt en.e v Fb O'') w'' ls'' O'' _ σ'
      hF''m hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb
      (hFe' m i en hTe v w' O' w'' O'' hO) h₁
  -- the cancel: the handler is the canceller, at its inner table `T`; then the handler around
  -- the unwinding, by the induction hypothesis at `Qunit`
  have hcan : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
      (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
      KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' → en.e.q ≠ .lin → en.e.fin = true →
      ∀ k', k' < k → ∀ F'' : TFrame, F''.Mono →
      (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
      cerwpP (ℍ := ℍ) To Qout Fbo F'' k' w'' ls'' O'' (hndE (hndVal m qs hr hs) (cancelE K₁))
        ρk' := by
    intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
    have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).2 hq hf k' hk' T Fb
      ⟨fun _ _ _ _ h => h, hPAT⟩ hFb
    simp only [cerwpPK, show k' < n by omega, if_true] at h₁
    exact ih k' (by omega) Qunit hretU (recMask O') F'' Fb (fdAt en.e v Fb O'') w'' ls'' O'' _
      ρk' hF''m hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb
      (hFe' m i en hTe v w' O' w'' O'' hO) h₁
  have hPdk := hPd (cerwpPK (ℍ := ℍ) n) (cerwpPC (ℍ := ℍ) To Qout Fbo n)
  rw [htag i en hTe ha, kappaAt_tag]
  cases hqq : en.e.q with
  | unr =>
      refine cerwpP_unfold_at hk (hcl _ k w' ls' O' v
        ⟨kappa (hndVal m qs hr hs) K₁, by unfold kappa; exact .lam⟩ ρ' hF'm hoc hF'M hcov' hls'
        hO' ⟨ρa, ρk, hcak, hA, ⟨hsh.1, ?_, ?_⟩⟩)
      · intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        have h₂ := hres w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        rw [cerwpP_eq] at h₂ ⊢
        exact twp_kappa_resume (hPd _ _) _ K₁ a h₂
      · intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
        have h₂ := hcan w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
        rw [cerwpP_eq] at h₂ ⊢
        exact twp_kappa_cancel_in (hPd _ _) _ K₁ (hndK _) h₂
  | lin | cancel =>
      refine twp_kappaCell hPdk _ _ K₁ (.appR (.val c) (.pairR v .hole)) fun l ρ₁ hc₁ => ?_
      obtain ⟨x, hx₂, hx₁⟩ :=
        (ResUT.CompS.assoc ρa ρk (ResUT.single l (CellUT.ownOf Val.unit)) ρ₁).mpr
          ⟨ρ', hcak, hc₁⟩
      have hρkl : ρk.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hx₂.1)
      have hxl : x.get l = some (CellUT.ownOf Val.unit) := by
        rw [ResUT.Comp.get_of_left_none hx₂ hρkl, ResUT.single_get_self]
      have hxd : x.del l = ρk := (eq_del_of_compS_single (ResUT.CompS.comm hx₂)).symm
      refine cerwpP_unfold_at hk (hcl _ k w' ls' O' v
        ⟨kappaC _ l (hndVal m qs hr hs) K₁, isVal_kappaC _ l _ K₁⟩ ρ₁ hF'm hoc hF'M
        (covR_compS_own hc₁ hcov') hls' hO'
        ⟨ρa, x, hx₁, hA, ⟨fun hu => (by rw [hqq] at hu; cases hu), ?_, ?_⟩⟩)
      swap
      · intro w'' ρx' ls'' O'' hE hr' hxF hO hq hf k' hk' F'' hF''m hF''M
        first
        | exact absurd hqq hq
        | have hρx'l := RR.own_fwd hr' hxl
          have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
          have h₂ := hcan w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
            (hxF.of_compS_left hx₂) hO hq hf k' hk' F'' hF''m hF''M
          rw [cerwpP_eq] at h₂ ⊢
          exact twp_kappaC_cancel_in (hPd _ _) l _ K₁ (hndK _) (compS_single_del hρx'l) h₂
      intro w'' ρx' ls'' O'' hE hr' hxF hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
      have hρx'l := RR.own_fwd hr' hxl
      have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
      obtain ⟨z, hz, hzσ⟩ :=
        (ResUT.CompS.assoc (ResUT.single l (CellUT.ownOf Val.unit)) (ρx'.del l) σ σ').mpr
          ⟨ρx', compS_single_del hρx'l, hcσ⟩
      have h₂ := hres w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
        (hxF.of_compS_left hx₂) hO k' hk' a σ z hB hz F'' hF''m hF''M
      rw [cerwpP_eq] at h₂ ⊢
      exact twp_kappaC_resume (hPd _ _) _ l _ K₁ a hzσ h₂

end BoCa.Fig16.Tree.Wp.HandleSpike.Param

end
