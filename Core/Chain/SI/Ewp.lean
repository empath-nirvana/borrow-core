import Core.Chain.SI.Frag

/-!
# Step-indexed relation: the effectful weakest precondition `ewp`

`ewp P Q n e σ`: the term `e`, owning exactly the fragment `σ`, is safe for `n` more steps of the
machine under every frame, and every way it stops within them is allowed:

* a value `v`, owning `σ`, in `Q n v σ`;
* `perform (m, (i, v))` under a context with no handler of `m` (a *stop*), at an operation of the
  protocol `P`: `σ` splits into the argument's part, in `PA`, and the continuation's part, which
  resumed at every answer `w` in `PB`, at every later index `k ≤ n − 1`, is in `ewp` again, and
  which, if the operation may be cancelled, meets the operation's cancel obligation on the
  cancelled region `K†[raise (0, (0, none))]` — the `&` of `κ`'s two branches, both from the same
  resources;
* `raise (m, (i, v))` under a context that catches nothing of `m`, at a raise of `P`, the whole
  fragment (the payload's and the abandoned context's) in its predicate;
* otherwise it steps, under every frame `σ_f` it is disjoint from, and every step keeps the frame
  and lands in `ewp` at `n − 1` (the later modality).

This is LinearActris's `WP₀` (§6.3) at one thread and our machine: the configuration's invariant
`I◦` is "the memory is `σ ⊎ σ_f`"; there is one thread, so no connectivity graph, and the
frame-preserving closure is built in by quantifying the frame. Linearity survives the index because
`σ` is exact at every index: the step index only decreases along the run, and nothing in the
definition lets a part of `σ` be forgotten. The answer `PB` sits in a contravariant position, so it
is read at every index `k ≤ n − 1` (the step-indexed `−∗`), which makes `ewp` downward closed
(`ewp_down`) without asking `PB` to be.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- An operation's entry in a protocol: its argument's and its answer's predicates, at a step
index, and its cancel obligation: `none` for an operation that must resume, else the predicate the
cancelled region `K†[raise (0, (0, none))]` must meet, owning the continuation's resources. -/
structure OpSpec where
  PA : Nat → Val → Heap → Prop
  PB : Nat → Val → Heap → Prop
  cancel : Option (Nat → Expr → Heap → Prop)

/-- A protocol: the operations a term may stop at, and the raises it may end at. -/
structure Prot where
  perf : UInt32 → UInt32 → Option OpSpec
  rais : UInt32 → UInt32 → Option (Nat → Val → Heap → Prop)

/-- A postcondition over values, at a step index. -/
abbrev Post := Nat → Val → Heap → Prop

/-- **The step-indexed `ewp`.** -/
def ewp (P : Prot) (Q : Post) : Nat → Expr → Heap → Prop
  | 0, _, _ => True
  | n + 1, e, σ =>
    (∃ v : Val, e = v.1 ∧ Q (n + 1) v σ) ∨
    (∃ (K : Kont) (m i : UInt32) (v : Val) (s : OpSpec),
      e = K.plug (performE (.val (opPayload m i v))) ∧ K.HasHnd m = false ∧
      P.perf m i = some s ∧
      ∃ σa σk, Disj σa σk ∧ σ = un σa σk ∧ s.PA n v σa ∧
        (∀ k, k ≤ n → ∀ w σw, Disj σk σw → s.PB k w σw →
          ewp P Q k (K.plug (.val w)) (un σk σw)) ∧
        (∀ C, s.cancel = some C → C n (K.dead.plug (raiseE (.val (cancelVal none)))) σk)) ∨
    (∃ (K : Kont) (m i : UInt32) (v : Val) (R : Nat → Val → Heap → Prop),
      e = K.plug (raiseE (.val (opPayload m i v))) ∧ K.Catches m = false ∧
      P.rais m i = some R ∧ R n v σ) ∨
    (¬ IsVal e ∧ ∀ σf, Disj σ σf → FinDom (un σ σf) →
      (∃ μ' e', Step1 (ℍ := ℍ) (un σ σf) e μ' e') ∧
      ∀ μ' e', Step1 (ℍ := ℍ) (un σ σf) e μ' e' →
        ∃ σ', Disj σ' σf ∧ μ' = un σ' σf ∧ ewp P Q n e' σ')
termination_by n => n


section
variable {P : Prot} {Q : Post}

theorem ewp_zero (e : Expr) (σ : Heap) : ewp (ℍ := ℍ) P Q 0 e σ := by
  rw [ewp]; trivial

theorem ewp_succ {n : Nat} {e : Expr} {σ : Heap} :
    ewp (ℍ := ℍ) P Q (n + 1) e σ ↔
    ((∃ v : Val, e = v.1 ∧ Q (n + 1) v σ) ∨
    (∃ (K : Kont) (m i : UInt32) (v : Val) (s : OpSpec),
      e = K.plug (performE (.val (opPayload m i v))) ∧ K.HasHnd m = false ∧
      P.perf m i = some s ∧
      ∃ σa σk, Disj σa σk ∧ σ = un σa σk ∧ s.PA n v σa ∧
        (∀ k, k ≤ n → ∀ w σw, Disj σk σw → s.PB k w σw →
          ewp (ℍ := ℍ) P Q k (K.plug (.val w)) (un σk σw)) ∧
        (∀ C, s.cancel = some C → C n (K.dead.plug (raiseE (.val (cancelVal none)))) σk)) ∨
    (∃ (K : Kont) (m i : UInt32) (v : Val) (R : Nat → Val → Heap → Prop),
      e = K.plug (raiseE (.val (opPayload m i v))) ∧ K.Catches m = false ∧
      P.rais m i = some R ∧ R n v σ) ∨
    (¬ IsVal e ∧ ∀ σf, Disj σ σf → FinDom (un σ σf) →
      (∃ μ' e', Step1 (ℍ := ℍ) (un σ σf) e μ' e') ∧
      ∀ μ' e', Step1 (ℍ := ℍ) (un σ σf) e μ' e' →
        ∃ σ', Disj σ' σf ∧ μ' = un σ' σf ∧ ewp (ℍ := ℍ) P Q n e' σ')) := by
  rw [ewp]

/-- A value in the postcondition. -/
theorem ewp_val {n : Nat} {v : Val} {σ : Heap} (h : Q n v σ) : ewp (ℍ := ℍ) P Q n v.1 σ := by
  cases n with
  | zero => exact ewp_zero _ _
  | succ n => exact ewp_succ.2 (.inl ⟨v, rfl, h⟩)

/-- A value's `ewp` is its postcondition. -/
theorem ewp_val_inv {n : Nat} {v : Val} {σ : Heap} (h : ewp (ℍ := ℍ) P Q (n + 1) v.1 σ) :
    Q (n + 1) v σ := by
  rcases ewp_succ.1 h with ⟨w, hw, hq⟩ | ⟨K, m, i, u, s, he, -⟩ | ⟨K, m, i, u, R, he, -⟩ |
    ⟨hnv, -⟩
  · rwa [Subtype.ext hw]
  · exact absurd he.symm (plug_perform_ne_val K _ v)
  · exact absurd he.symm (plug_raise_ne_val K _ v)
  · exact absurd v.2 hnv

/-! ### Downward closure -/

/-- A protocol's predicates that are read at the current index are downward closed. -/
structure Prot.Down (P : Prot) : Prop where
  pa : ∀ m i s, P.perf m i = some s → ∀ n v σ, s.PA (n + 1) v σ → s.PA n v σ
  canc : ∀ m i s C, P.perf m i = some s → s.cancel = some C → ∀ n e σ, C (n + 1) e σ → C n e σ
  rais : ∀ m i R, P.rais m i = some R → ∀ n v σ, R (n + 1) v σ → R n v σ

/-- A postcondition is downward closed. -/
def Post.Down (Q : Post) : Prop := ∀ n v σ, Q (n + 1) v σ → Q n v σ

/-- **`ewp` is downward closed.** -/
theorem ewp_down (hP : P.Down) (hQ : Q.Down) :
    ∀ n e σ, ewp (ℍ := ℍ) P Q (n + 1) e σ → ewp (ℍ := ℍ) P Q n e σ := by
  intro n
  induction n with
  | zero => intro e σ _; exact ewp_zero _ _
  | succ n ih =>
      intro e σ h
      rcases ewp_succ.1 h with ⟨v, hv, hq⟩ | ⟨K, m, i, v, s, he, hK, hs, σa, σk, hd, hσ, hA, hB, hC⟩ |
        ⟨K, m, i, v, R, he, hK, hR, hr⟩ | ⟨hnv, hst⟩
      · exact ewp_succ.2 (.inl ⟨v, hv, hQ _ _ _ hq⟩)
      · exact ewp_succ.2 (.inr (.inl ⟨K, m, i, v, s, he, hK, hs, σa, σk, hd, hσ,
          hP.pa _ _ _ hs _ _ _ hA, fun k hk => hB k (by omega),
          fun C hc => hP.canc _ _ _ _ hs hc _ _ _ (hC C hc)⟩))
      · exact ewp_succ.2 (.inr (.inr (.inl ⟨K, m, i, v, R, he, hK, hR,
          hP.rais _ _ _ hR _ _ _ hr⟩)))
      · refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv, fun σf hd hfd => ?_⟩)))
        obtain ⟨hred, hpres⟩ := hst σf hd hfd
        refine ⟨hred, fun μ' e' h' => ?_⟩
        obtain ⟨σ', hd', rfl, he'⟩ := hpres μ' e' h'
        exact ⟨σ', hd', rfl, ih _ _ he'⟩

theorem ewp_le (hP : P.Down) (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n) {e : Expr} {σ : Heap}
    (h : ewp (ℍ := ℍ) P Q n e σ) : ewp (ℍ := ℍ) P Q m e σ := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih (ewp_down hP hQ _ _ _ h)

end

/-! ### Monotonicity in the protocol and the postcondition -/

/-- `P'` allows every stop `P` does: the same operations, and weaker raises. -/
structure ProtLe (P P' : Prot) : Prop where
  perf : ∀ m i s, P.perf m i = some s → P'.perf m i = some s
  rais : ∀ m i R, P.rais m i = some R →
    ∃ R', P'.rais m i = some R' ∧ ∀ n v σ, R n v σ → R' n v σ

theorem ProtLe.refl (P : Prot) : ProtLe P P :=
  ⟨fun _ _ _ h => h, fun _ _ R h => ⟨R, h, fun _ _ _ h => h⟩⟩

theorem ewp_mono {P P' : Prot} {Q Q' : Post} (hPP : ProtLe P P')
    (hQQ : ∀ n v σ, Q n v σ → Q' n v σ) :
    ∀ n e σ, ewp (ℍ := ℍ) P Q n e σ → ewp (ℍ := ℍ) P' Q' n e σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e σ h
  cases n with
  | zero => exact ewp_zero _ _
  | succ n =>
  rcases ewp_succ.1 h with ⟨v, hv, hq⟩ | ⟨K, m, i, v, s, he, hK, hs, σa, σk, hd, hσ, hA, hB, hC⟩ |
    ⟨K, m, i, v, R, he, hK, hR, hr⟩ | ⟨hnv, hst⟩
  · exact ewp_succ.2 (.inl ⟨v, hv, hQQ _ _ _ hq⟩)
  · exact ewp_succ.2 (.inr (.inl ⟨K, m, i, v, s, he, hK, hPP.perf _ _ _ hs, σa, σk, hd, hσ, hA,
      fun k hk w σw hw hb => ih k (by omega) _ _ (hB k hk w σw hw hb), hC⟩))
  · obtain ⟨R', hR', hRR⟩ := hPP.rais _ _ _ hR
    exact ewp_succ.2 (.inr (.inr (.inl ⟨K, m, i, v, R', he, hK, hR', hRR _ _ _ hr⟩)))
  · refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv, fun σf hd hfd => ?_⟩)))
    obtain ⟨hred, hpres⟩ := hst σf hd hfd
    refine ⟨hred, fun μ' e' h' => ?_⟩
    obtain ⟨σ', hd', rfl, he'⟩ := hpres μ' e' h'
    exact ⟨σ', hd', rfl, ih n (by omega) _ _ he'⟩

/-! ### Steps -/

section
variable {P : Prot} {Q : Post}

/-- **A step that is its configuration's only one, at every memory, and keeps the memory.** -/
theorem ewp_det {n : Nat} {e e' : Expr} {σ : Heap}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : ewp (ℍ := ℍ) P Q n e' σ) : ewp (ℍ := ℍ) P Q (n + 1) e σ := by
  have hnv : ¬ IsVal e := fun hv => BoLo.no_step_val (w := ⟨e, hv⟩) (hdet emp).1
  refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv, fun σf hd _ => ?_⟩)))
  refine ⟨⟨_, _, (hdet _).1⟩, fun μ' e'' h' => ?_⟩
  obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ h'
  exact ⟨σ, hd, rfl, h⟩

/-- A head step that allocates nothing and keeps the memory, in a context. -/
theorem ewp_head {n : Nat} {a a' : Expr} {σ : Heap} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a')
    (ha : a.allocs = false) (K : Kont) (h : ewp (ℍ := ℍ) P Q n (K.plug a') σ) :
    ewp (ℍ := ℍ) P Q (n + 1) (K.plug a) σ :=
  ewp_det (fun μ => step1Only_plug (hh μ) ha K) h

/-- **Allocation**: the new cell joins the owned fragment, at every location free in it. -/
theorem ewp_alloc {n : Nat} {σ : Heap} (K : Kont) (v : Val)
    (h : ∀ ℓ, σ ℓ = none → ewp (ℍ := ℍ) P Q n (K.plug (.val (.loc ℓ))) (un (single ℓ v) σ)) :
    ewp (ℍ := ℍ) P Q (n + 1) (K.plug (.app (.val (.prim .alloc)) (.val v))) σ := by
  have hnv : ¬ IsVal (K.plug (.app (.val (.prim .alloc)) (.val v))) := fun hv => by
    have := K.isVal_of_plug hv
    simp [Expr.val, Val.prim] at this
  refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv, fun σf hd hfd => ?_⟩)))
  refine ⟨?_, fun μ' e' h' => ?_⟩
  · obtain ⟨ℓ, hℓ⟩ := BoLo.finDom_block hfd
    exact ⟨_, _, (step1_alloc_iff K v).2 ⟨ℓ, by simpa using hℓ 0, rfl, rfl⟩⟩
  · obtain ⟨ℓ, hℓ, rfl, rfl⟩ := (step1_alloc_iff K v).1 h'
    obtain ⟨h₁, h₂⟩ := un_eq_none.1 hℓ
    refine ⟨un (single ℓ v) σ, ?_, upd_un v hℓ, h ℓ h₁⟩
    exact disj_un_left.2 ⟨single_disj.2 h₂, hd⟩

/-- **Release** of an owned cell: it leaves the owned fragment. -/
theorem ewp_free {n : Nat} {σ : Heap} (K : Kont) {ℓ : Loc} {u : Val} (hσ : σ ℓ = none)
    (h : ewp (ℍ := ℍ) P Q n (K.plug (.val u)) σ) :
    ewp (ℍ := ℍ) P Q (n + 1) (K.plug (BoLo.freeE (.val (Val.loc ℓ)))) (un (single ℓ u) σ) := by
  have hnv : ¬ IsVal (K.plug (BoLo.freeE (.val (Val.loc ℓ)))) := fun hv => by
    have := K.isVal_of_plug hv
    simp [BoLo.freeE, Expr.val, Val.prim] at this
  refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv, fun σf hd hfd => ?_⟩)))
  have hget : un (un (single ℓ u) σ) σf ℓ = some u := by simp [un]
  refine ⟨⟨_, _, (step1_free_iff K ℓ).2 ⟨u, hget, rfl, rfl⟩⟩, fun μ' e' h' => ?_⟩
  obtain ⟨u', hu', rfl, rfl⟩ := (step1_free_iff K ℓ).1 h'
  rw [hget] at hu'
  cases hu'
  exact ⟨σ, (disj_un_left.1 hd).2, del_un hd hσ, h⟩

/-- To prove `ewp` at `k`, it is enough to prove it at `k = n + 1`. -/
theorem ewp_pred {k : Nat} {e : Expr} {σ : Heap}
    (h : ∀ n, k = n + 1 → ewp (ℍ := ℍ) P Q (n + 1) e σ) : ewp (ℍ := ℍ) P Q k e σ := by
  cases k with
  | zero => exact ewp_zero _ _
  | succ n => exact h n rfl

/-- The step clause of `K[e]` from that of `e`: every step of `K[e]` is a step of `e` under `K`,
and the frame `σ₂` that `K` holds rides along. -/
theorem ewp_ctx_step {P' : Prot} {Q' : Post} (K : Kont) {n : Nat} {e : Expr} {σ₁ σ₂ : Heap}
    (hd₁ : Disj σ₁ σ₂) (hnv : ¬ IsVal e)
    (hst : ∀ σf, Disj σ₁ σf → FinDom (un σ₁ σf) →
      (∃ μ' e', Step1 (ℍ := ℍ) (un σ₁ σf) e μ' e') ∧
      ∀ μ' e', Step1 (ℍ := ℍ) (un σ₁ σf) e μ' e' →
        ∃ σ', Disj σ' σf ∧ μ' = un σ' σf ∧ ewp (ℍ := ℍ) P Q n e' σ')
    (F : ∀ e' σ', Disj σ' σ₂ → ewp (ℍ := ℍ) P Q n e' σ' →
      ewp (ℍ := ℍ) P' Q' n (K.plug e') (un σ' σ₂)) :
    ewp (ℍ := ℍ) P' Q' (n + 1) (K.plug e) (un σ₁ σ₂) := by
  have hnv' : ¬ IsVal (K.plug e) := fun hv => hnv (K.isVal_of_plug hv)
  refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv', fun σf hd hfd => ?_⟩)))
  obtain ⟨hd12, hd2f⟩ := disj_un_left.1 hd
  have hd' : Disj σ₁ (un σ₂ σf) := disj_un_right.2 ⟨hd₁, hd12⟩
  have hμ : un (un σ₁ σ₂) σf = un σ₁ (un σ₂ σf) := un_assoc _ _ _
  rw [hμ] at hfd ⊢
  obtain ⟨⟨μ₁, e₁, hred⟩, hpres⟩ := hst (un σ₂ σf) hd' hfd
  refine ⟨⟨μ₁, K.plug e₁, hred.plug K⟩, fun μ' E hE => ?_⟩
  obtain ⟨e', rfl, he'⟩ := step1_plug_of_step K hred hE
  obtain ⟨σ', hdσ', rfl, hw⟩ := hpres μ' e' he'
  obtain ⟨hσ'2, hσ'f⟩ := disj_un_right.1 hdσ'
  exact ⟨un σ' σ₂, disj_un_left.2 ⟨hσ'f, hd2f⟩, (un_assoc _ _ _).symm, F e' σ' hσ'2 hw⟩

/-- **A stop at an operation** of the protocol. -/
theorem ewp_perform {n : Nat} (K : Kont) {m i : UInt32} {v : Val} {s : OpSpec}
    (hK : K.HasHnd m = false) (hs : P.perf m i = some s) {σa σk : Heap} (hd : Disj σa σk)
    (hA : s.PA n v σa)
    (hB : ∀ k, k ≤ n → ∀ w σw, Disj σk σw → s.PB k w σw →
      ewp (ℍ := ℍ) P Q k (K.plug (.val w)) (un σk σw))
    (hC : ∀ C, s.cancel = some C → C n (K.dead.plug (raiseE (.val (cancelVal none)))) σk) :
    ewp (ℍ := ℍ) P Q (n + 1) (K.plug (performE (.val (opPayload m i v)))) (un σa σk) :=
  ewp_succ.2 (.inr (.inl ⟨K, m, i, v, s, rfl, hK, hs, σa, σk, hd, rfl, hA, hB, hC⟩))

/-- **A stop at a raise** of the protocol. -/
theorem ewp_raise {n : Nat} (K : Kont) {m i : UInt32} {v : Val} {σ : Heap}
    {R : Nat → Val → Heap → Prop} (hK : K.Catches m = false) (hR : P.rais m i = some R)
    (hr : R n v σ) :
    ewp (ℍ := ℍ) P Q (n + 1) (K.plug (raiseE (.val (opPayload m i v)))) σ :=
  ewp_succ.2 (.inr (.inr (.inl ⟨K, m, i, v, R, rfl, hK, hR, hr⟩)))

end

/-! ### Bind -/

/-- The cancel obligations of the outer protocol follow from the inner ones, for a region extended
by `K` and owning `σ₂` more. -/
def CancelExt (c c' : Option (Nat → Expr → Heap → Prop)) (K : Kont) (σ₂ : Heap) : Prop :=
  ∀ C', c' = some C' → ∃ C, c = some C ∧
    ∀ k x σ, Disj σ σ₂ → C k x σ → C' k (K.dead.plug x) (un σ σ₂)

/-- What `bind` asks of the context `K`, framing `σ₂`, between the inner and the outer protocol:
each operation passes `K` (no handler of it) to an entry of the outer protocol with the same
argument and answer, whose cancel obligation follows; each raise passes `K` (nothing catches it)
to a weaker raise, `σ₂` abandoned with it. -/
structure BindOK (K : Kont) (σ₂ : Heap) (P P' : Prot) : Prop where
  perf : ∀ m i s, P.perf m i = some s → K.HasHnd m = false ∧
    ∃ s', P'.perf m i = some s' ∧ s'.PA = s.PA ∧ s'.PB = s.PB ∧ CancelExt s.cancel s'.cancel K σ₂
  rais : ∀ m i R, P.rais m i = some R → K.Catches m = false ∧
    ∃ R', P'.rais m i = some R' ∧ ∀ k v σ, Disj σ σ₂ → R k v σ → R' k v (un σ σ₂)

/-- **Bind, with the frame rule.** `e` runs in `K`, which holds `σ₂` alongside; at every value in
`Q`, `K[v]` goes on. -/
theorem ewp_bind {P P' : Prot} {Q Q' : Post} (K : Kont) {σ₂ : Heap} (hK : BindOK K σ₂ P P') :
    ∀ n e σ₁, Disj σ₁ σ₂ →
      (∀ k, k ≤ n → ∀ v σ, Disj σ σ₂ → Q k v σ → ewp (ℍ := ℍ) P' Q' k (K.plug v.1) (un σ σ₂)) →
      ewp (ℍ := ℍ) P Q n e σ₁ → ewp (ℍ := ℍ) P' Q' n (K.plug e) (un σ₁ σ₂) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e σ₁ hd₁ hval h
  cases n with
  | zero => exact ewp_zero _ _
  | succ n =>
  rcases ewp_succ.1 h with ⟨v, rfl, hq⟩ | ⟨K₀, m, i, v, s, rfl, hK₀, hs, σa, σk, hd, rfl, hA, hB, hC⟩ |
    ⟨K₀, m, i, v, R, rfl, hK₀, hR, hr⟩ | ⟨hnv, hst⟩
  · exact hval _ le_rfl v σ₁ hd₁ hq
  · obtain ⟨hKm, s', hs', hPA, hPB, hCE⟩ := hK.perf _ _ _ hs
    obtain ⟨hda₂, hdk₂⟩ := disj_un_left.1 hd₁
    have hplug : K.plug (K₀.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₀).plug (performE (.val (opPayload m i v))) := (Kont.plug_comp _ _ _).symm
    rw [hplug, un_assoc]
    refine ewp_perform (K.comp K₀) (by rw [hasHnd_comp, hKm, hK₀]; rfl) hs'
      (disj_un_right.2 ⟨hd, hda₂⟩) (hPA ▸ hA) ?_ ?_
    · intro k hk w σw hdw hb
      obtain ⟨hdkw, hd₂w⟩ := disj_un_left.1 hdw
      have hcont := hB k hk w σw hdkw (hPB ▸ hb)
      have e₁ : un (un σk σ₂) σw = un (un σk σw) σ₂ := by
        rw [un_assoc, un_comm hd₂w, ← un_assoc]
      rw [Kont.plug_comp, e₁]
      refine ih k (by omega) _ _ (disj_un_left.2 ⟨hdk₂, hd₂w.symm⟩) (fun k' hk' => hval k' (by omega))
        hcont
    · intro C' hc'
      obtain ⟨C, hc, hCC⟩ := hCE C' hc'
      rw [dead_comp, Kont.plug_comp]
      exact hCC _ _ _ hdk₂ (hC C hc)
  · obtain ⟨hKc, R', hR', hRR⟩ := hK.rais _ _ _ hR
    rw [← Kont.plug_comp]
    exact ewp_raise (K.comp K₀) (by rw [catches_comp, hKc, hK₀]; rfl) hR' (hRR _ _ _ hd₁ hr)
  · have hnv' : ¬ IsVal (K.plug e) := fun hv => hnv (K.isVal_of_plug hv)
    refine ewp_succ.2 (.inr (.inr (.inr ⟨hnv', fun σf hd hfd => ?_⟩)))
    obtain ⟨hd12, hd2f⟩ := disj_un_left.1 hd
    have hd' : Disj σ₁ (un σ₂ σf) := disj_un_right.2 ⟨hd₁, hd12⟩
    have hμ : un (un σ₁ σ₂) σf = un σ₁ (un σ₂ σf) := un_assoc _ _ _
    rw [hμ] at hfd ⊢
    obtain ⟨⟨μ₁, e₁, hred⟩, hpres⟩ := hst (un σ₂ σf) hd' hfd
    refine ⟨⟨μ₁, K.plug e₁, hred.plug K⟩, fun μ' E hE => ?_⟩
    obtain ⟨e', rfl, he'⟩ := step1_plug_of_step K hred hE
    obtain ⟨σ', hdσ', rfl, hw⟩ := hpres μ' e' he'
    obtain ⟨hσ'2, hσ'f⟩ := disj_un_right.1 hdσ'
    refine ⟨un σ' σ₂, disj_un_left.2 ⟨hσ'f, hd2f⟩, (un_assoc _ _ _).symm, ?_⟩
    exact ih n (by omega) _ _ hσ'2 (fun k hk => hval k (by omega)) hw

end BoCa.Fig16.LogRel.Core.Chain.SI

end
