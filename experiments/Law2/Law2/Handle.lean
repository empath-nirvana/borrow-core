import Law2.Piece

/-!
# Law2 — a handler installed inside the borrower

`handle_n e with (h_ret, hs)` inside the region a stack of lends spans. The handled computation's
row is the handler's operations ahead of the row outside (`Row.ofEff n E 0 ++ S`), and `n` is not
a name of the lenders' row (`outN S₀ n = false`), so a stop of `e` at an operation of `n` crosses
no lend: it is a stop inside (`InStop`), and the handler catches it.

* `bodyH_handle`: one run of `hnd H e`. An answer of `e` runs `h_ret`; a stop of the lenders' row
  and a stop caught further out pass the handler outward, reinstalled in their continuations
  (`opTable_handle`); a stop at `n` steps to the clause (`[op]`), handed the argument and `κ` at a
  fresh cell (`wpG_kappaCell`). `κ` is re-lendable (`rslot_kappaC`): its share is the
  continuation's, which the stop already split into views and a frozen part, beside its cell,
  owned and in every stratum; resumed at a re-lend on a re-lendable answer it frees the cell and
  runs `hnd H K[w]` (`wpG_kappaC_resume`), the piece there. The clause may hold `κ` across stops of
  the lenders' row, each dropping the views `κ` holds and thawing them at the next re-lend.
* `openH_handle`: the same at every continuation, by induction on `e`'s piece.
* `pj_handle`: the piece judgment for `handle_n e with H`, `H` a value form over a context whose
  live slots are persistent, from the piece judgment for `e` and `H` re-lendable.

The handler's operations are linear: `κ` is resumed once, and has no cancel branch.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload hndE hndVal kappa kappaAt kappaC
  kappaCBody kappaCell freeE clauseAt capTag)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

/-- One run of the piece at the computation type `C`. -/
abbrev BH (δ : LSub) (σ : LStack) (S₀ : Row) (C : CTy) (αs : List Life) :
    List SRec → Expr → WProp :=
  bodyH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)
    (OpenH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)) αs

/-- The piece at the computation type `C`. -/
abbrev OH (δ : LSub) (σ : LStack) (S₀ : Row) (C : CTy) : XT :=
  OpenH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)

/-! ### The capture cell and the resume, at `wpG` -/

/-- An allocation at an evaluation position, in front of a `wpG`. -/
theorem wpG_alloc (K : Kont) (v : Val) {ls : List SRec} {Q : List SRec → Expr → WProp}
    {ρ : WRes} (h : ∀ ℓ : Loc, (ptoOwn ℓ v ─⋆ wpG ls (K.plug (.val (Val.loc ℓ))) Q) ρ) :
    wpG ls (K.plug (.app (.val (.prim .alloc)) (.val v))) Q ρ :=
  wpG_bind_pure K _ ls Q ρ (wpTS_alloc ls v _ ρ h)

/-- A release of an owned cell at an evaluation position, in front of a `wpG`. -/
theorem wpG_free (K : Kont) (ℓ : Loc) (v : Val) {ls : List SRec}
    {Q : List SRec → Expr → WProp} {ρ : WRes} (h : (ptoOwn ℓ v ⋆ wpG ls (K.plug (.val v)) Q) ρ) :
    wpG ls (K.plug (freeE (.val (Val.loc ℓ)))) Q ρ :=
  wpG_bind_pure K _ ls Q ρ (wpTS_free ls ℓ v _ ρ h)

/-- **The capture cell's allocation** at `wpG`: `κ` before its cell, at an evaluation position,
allocates the cell by the ordinary `alloc` step and becomes `kappaC` at its location. -/
theorem wpG_kappaCell (aff : Bool) (H : Val) (K : Kont) (Kc : Kont) {ls : List SRec}
    {Q : List SRec → Expr → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ wpG ls (Kc.plug (kappaC aff ℓ H K)) Q) ρ) :
    wpG ls (Kc.plug (kappaCell aff H K)) Q ρ := by
  have e : Kc.plug (kappaCell aff H K) =
      (Kc.comp (.appR (.val (.lam (kappaCBody aff H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine wpG_alloc _ Val.unit (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  refine wpG_step (fun μ => (Step1N.head (Head.beta μ _ (Val.loc ℓ)) rfl).plug Kc) ls Q σ₂ ?_
  rw [kappaCBody_subst]
  exact h ℓ σ₁ σ₂ hp hc

/-- **Resuming a `κ` that owns a cell**, at `wpG`: it frees the cell, then runs `hnd H K[w]`. -/
theorem wpG_kappaC_resume (aff : Bool) (ℓ : Loc) (H : Val) (K : Kont) (w : Val)
    {ls : List SRec} {Q : List SRec → Expr → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ wpG ls (hndE H (K.plug (.val w))) Q) ρ) :
    wpG ls (.app (.app (kappaC aff ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) Q ρ := by
  refine wpG_step (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug (Kont.appL .hole w))
    ls Q ρ ?_
  refine wpG_step (fun μ => (Step1N.head (Head.case₁ μ Val.unit _ _) rfl).plug
    (Kont.appL .hole w)) ls Q ρ ?_
  refine wpG_step (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w)) ls Q ρ ?_
  refine wpG_free (Kont.appL (Kont.seq .hole _) w) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine wpG_step (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w))
    ls Q ρ₂ ?_
  refine wpG_step (fun μ => Step1N.head (Head.beta μ _ w) rfl) ls Q ρ₂ ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

/-- **A stop passes a handler of another name outward**, the handler reinstalled in its
continuation and dead in its cancel run (`[spec §19]`'s `H-fwd`, as in `ewp_handle`). -/
theorem opTable_handle {T : OpTab} {n : UInt32} (hTn : ∀ i, T n i = none) {qs hr hs : Val}
    {Φ Φ' : List SRec → Expr → WProp}
    (hΦ : ∀ ls e ρ, Φ ls e ρ → Φ' ls (hndE (hndVal n qs hr hs) e) ρ) {ls : List SRec}
    {t : Expr} {ρ : WRes} (h : opTable T ls t Φ ρ) :
    opTable T ls (hndE (hndVal n qs hr hs) t) Φ' ρ := by
  rcases h with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hm : m ≠ n := fun e => by subst e; rw [hTn] at hT; cases hT
    refine Or.inl ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
      pure_sep_mk ⟨(Kont.plug_comp (hndK (hndVal n qs hr hs)) K₁ _).symm, ?_, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq => ?_⟩⟩⟩
    · rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
    · rw [Kont.plug_comp]; exact hΦ _ _ _ ((hcont ls'' he).1 w τ₁ τ₂ hB hc)
    · intro P hP
      show P ls'' (((hndK (hndVal n qs hr hs)).comp K₁).dead.plug _) ρk
      rw [dead_comp, dead_hndK]
      exact (hcont ls'' he).2 hq P hP
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    have hm : m ≠ n := fun e => by subst e; rw [hTn] at hT; cases hT
    refine Or.inr ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
      pure_sep_mk ⟨(Kont.plug_comp (hndK (hndVal n qs hr hs)) K₁ _).symm, ?_, hT, ha⟩
        ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩
    rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm

/-! ### The handler's values, re-lendable -/

section vals
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- **The continuation a clause is handed is re-lendable**: its share is the continuation's,
re-lendable, beside its cell, owned and in every stratum. Resumed at a re-lend on a re-lendable
answer it frees the cell and runs `hnd H K[w]`, the piece there. -/
theorem rslot_kappaC {S : Row} (hS : S ≠ []) {R B : VTy} {H : Val} {K : Kont} {ℓ : Loc}
    {αs : List Life} {ls : List SRec} {ρk ρ : WRes} (hlen : αs.length = σ.length)
    (hk : RelendableS δ [] σ (fun αs' ls' ρ => ∀ w, (RSlot (ℍ := ℍ) δ σ S₀ B αs' ls' w ─⋆
      BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs' ls' (hndE H (K.plug (.val w)))) ρ) αs ls ρk)
    (hc : ResU.CompS ρk (ResU.single ℓ (CellU.ownOf Val.unit)) ρ) :
    RSlot (ℍ := ℍ) δ σ S₀ (kTy S R .lin B) αs ls ⟨kappaC false ℓ H K, isVal_kappaC false ℓ H K⟩
      ρ := by
  obtain ⟨o, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  have hcell : RelendableS δ [] σ (fun _ _ => ptoOwn ℓ Val.unit) αs ls
      (ResU.single ℓ (CellU.ownOf Val.unit)) :=
    relendableS_frozen hlen (fun a _ => ResU.inStratum_single_own a ℓ Val.unit)
      fun _ _ _ _ => rfl
  have hsep := relendableS_sep ρ ⟨ρk, _, hc, hk, hcell⟩
  change RelendableS δ [] σ _ αs ls ρ
  refine relendableS_mono_rel ?_ ρ hsep
  intro αs' ls' _ τ hτ w τw τ' hw hcw
  obtain ⟨τ₁, τ₂, hcτ, h₁, h₂⟩ := hτ
  obtain ⟨x, hx, hxτ⟩ := compS_exch hcτ hcw
  exact wpG_kappaC_resume false ℓ H K w ⟨τ₂, x, ResU.CompS.comm hxτ, h₂, h₁ w τw x hw hx⟩

/-- The clauses of a re-lendable clause tuple, each re-lendable at `∅`. -/
theorem rslot_clausesTy_at {S : Row} {R : VTy} {αs : List Life} {ls : List SRec}
    (hch : List.IsChain (· < ·) αs) :
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {hs : Val} {ρ : WRes},
      RSlot (ℍ := ℍ) δ σ S₀ (clausesTy S R E fs) αs ls hs ρ →
      ∀ j (h : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧
        RSlot (ℍ := ℍ) δ σ S₀ (clauseTy S R E[j] (fs j)) αs ls c PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, fs, hs, ρ, h, j, hj => by
      obtain ⟨c, rest, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, hc₁, hr⟩ := pure_sep_iff.mp h
      have hp : (clauseTy S R o (fs 0)).Persistent := by
        obtain ⟨q, A, B⟩ := o
        simp only [clauseTy]; split <;> rfl
      obtain rfl := rslot_persistent_empty _ hp hch hc₁
      cases j with
      | zero =>
          refine ⟨c, ?_, hc₁⟩
          simp [clauseAt, Val.pair, c.2]
      | succ j =>
          obtain ⟨c', hc', hv⟩ := rslot_clausesTy_at hch E (fun j => fs (j + 1)) hr j
            (by simpa using hj)
          exact ⟨c', by simpa [clauseAt, Val.pair] using hc', by simpa using hv⟩

/-- The handler's operations all carry its name. -/
theorem mem_ofEff_n {n : UInt32} : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy),
    ∀ o ∈ Row.ofEff n E k fs, o.n = n
  | [], _, _, o, h => by simp [Row.ofEff] at h
  | (q, A, B) :: E, k, fs, o, h => by
      simp only [Row.ofEff, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact mem_ofEff_n E (k + 1) _ o h

theorem forall₂_le_append : ∀ {a b : List Life}, List.Forall₂ (· ≤ ·) a b →
    ∀ c : List Life, List.Forall₂ (· ≤ ·) (a ++ c) (b ++ c)
  | [], [], .nil, _ => List.forall₂_same.mpr fun _ _ => le_rfl
  | _ :: _, _ :: _, .cons h t, c => .cons h (forall₂_le_append t c)

end vals

/-! ### The handler at the piece -/

section handle
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- **One run of `hnd H e`**, `e` one run of the piece at the handler's row ahead of `S`. An answer
runs `h_ret` (`hret`); a stop of the lenders' row and a stop caught further out pass the handler
outward, its continuations the piece of `hnd H` around `e`'s (`hX`, `hX₀`); a stop at the
handler's name runs its clause on the argument and `κ`, re-lendable (`hcl`, `rslot_kappaC`). -/
theorem bodyH_handle {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row} {A R : VTy}
    {hr hs : Val} (hS : S ≠ []) (hn : outN S₀ n = false) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlenE : E.length ≤ 2 ^ 32) (hE : ∀ q ∈ E, q.1 = .lin) {B αs : List Life}
    (hrB : ReLend αs B) (hlen : αs.length = σ.length)
    (hret : ∀ αs', ReLend αs' B → ∀ ls v, Entails (RSlot (ℍ := ℍ) δ σ S₀ A αs' ls v)
      (BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs' ls (.app (.val hr) (.val v))))
    (hcl : ∀ j (hj : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧ ∀ αs', ReLend αs' B →
      ∀ ls x, Entails (RSlot (ℍ := ℍ) δ σ S₀ (.tensor E[j].2.1 (kTy S R .lin E[j].2.2)) αs' ls x)
        (BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs' ls (.app (.val c) (.val x))))
    {X₁ : XT}
    (hX : ∀ ds ls e ρ, X₁ σ.length ds αs [] ls e ρ →
      OH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) σ.length ds αs [] ls
        (hndE (hndVal n (qualsVal (E.map Prod.fst)) hr hs) e) ρ)
    (hX₀ : ∀ αs' ls e ρ, ReLend αs' αs → X₁ 0 [] [] αs' ls e ρ →
      OH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) 0 [] [] αs' ls
        (hndE (hndVal n (qualsVal (E.map Prod.fst)) hr hs) e) ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : bodyH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf (Row.ofEff n E 0 ++ S) A))
      (QA (ℍ := ℍ) δ σ S₀ (CTy.effOf (Row.ofEff n E 0 ++ S) A)) X₁ αs ls e ρ) :
    BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs ls
      (hndE (hndVal n (qualsVal (E.map Prod.fst)) hr hs) e) ρ := by
  refine wpG_bind (hndK (hndVal n (qualsVal (E.map Prod.fst)) hr hs)) e ls _ ρ
    (wpG_mono (fun ls' t τ ht => ?_) h)
  rcases ht with ⟨v, rfl, hv⟩ | hst | hin
  · -- `[ret]`: the answer clause, on the answer re-lendable
    refine wpG_head (fun μ => Head.hret μ n _ hr hs v) rfl _ _ τ (hret αs hrB ls' v τ ?_)
    have := hv; simp only [QA] at this; rwa [rAns_effOf] at this
  · -- a stop of the lenders' row passes the handler outward
    refine wpG_here _ _ _ τ (Or.inr (Or.inl ?_))
    obtain ⟨ds, ρ₁, ρ₂, hc, hd, hb, hstr⟩ := hst
    exact ⟨ds, ρ₁, ρ₂, hc, hd,
      opTable_handle (tab_none_of_outN hn) (fun _ _ _ h => hX _ _ _ _ h) hb, hstr⟩
  · obtain ⟨K₁, m, i, y, P, hp⟩ := hin
    obtain ⟨⟨rfl, hK₁, hP⟩, ρa, ρk, hcak, hA, hk⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[op]` at the handler's name: its clause, on the argument and `κ` at a fresh cell
      subst hm
      obtain ⟨o, hf, -, rfl⟩ := rIn_effOf_some _ hP
      have hfo : Row.find (Row.ofEff m E 0) m i = some o := by
        rw [Row.find_append] at hf
        cases h₁ : Row.find (Row.ofEff m E 0) m i with
        | some o' => rw [h₁] at hf; exact hf
        | none =>
            rw [h₁] at hf
            obtain ⟨hm', hn', -⟩ := Row.find_mem hf
            exact absurd hn' (hnS o hm')
      obtain ⟨-, j, hj, rfl, rfl⟩ := Row.find_ofEff m E 0 finsNil m i o hfo
      have hjn : (UInt32.ofNat (0 + j)).toNat = j := by
        rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
      obtain ⟨c, hc, hcok⟩ := hcl j hj
      have hcap : capTag (qualsVal (E.map Prod.fst)).1 (UInt32.ofNat (0 + j)).toNat =
          Qual.lin.tag := by
        rw [hjn, capTag_qualsVal _ j (by simpa using hj)]
        simp [hE _ (List.getElem_mem hj)]
      refine wpG_head (fun μ => Head.hop μ m _ _ hr hs c y K₁ (by rw [hjn]; exact hc) hK₁) rfl
        _ _ τ ?_
      rw [hcap, kappaAt_tag]
      refine wpG_kappaCell false _ K₁ (.appR (.val c) (.pairR y .hole))
        (fun ℓ σ₁ σ₂ hcell hc₂ => ?_)
      obtain rfl : σ₁ = ResU.single ℓ (CellU.ownOf Val.unit) := hcell
      obtain ⟨z, hz, hz₂⟩ := compS_reassoc hcak hc₂
      have hk' : RelendableS δ [] σ (fun αs' ls'' ρ => ∀ w,
          (RSlot (ℍ := ℍ) δ σ S₀ E[j].2.2 αs' ls'' w ─⋆
            BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs' ls''
              (hndE (hndVal m (qualsVal (E.map Prod.fst)) hr hs) (K₁.plug (.val w)))) ρ)
          αs ls' ρk := by
        refine relendableS_mono_rel ?_ ρk hk
        intro αs' ls'' hr' τ' hτ w τw τ'' hw hcw
        exact openH_zero_unfold (hX₀ αs' ls'' _ τ'' hr' (hτ w τw τ'' hw hcw)) hr'.2
      have hκ := rslot_kappaC (ℍ := ℍ) hS hlen hk' hz
      exact hcok αs hrB ls' (Val.pair y ⟨_, isVal_kappaC false ℓ _ K₁⟩) σ₂
        ⟨y, _, pure_sep_mk rfl ⟨ρa, z, hz₂, hA, hκ⟩⟩
    · -- an operation caught further out passes the handler outward
      refine wpG_here _ _ _ τ (Or.inr (Or.inr ⟨(hndK (hndVal n (qualsVal (E.map Prod.fst)) hr
        hs)).comp K₁, m, i, y, P, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, ?_⟩
          ⟨ρa, ρk, hcak, hA, ?_⟩⟩))
      · rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      · rw [← rIn_effOf_ans S A R, ← rIn_effOf_append (Row.ofEff n E 0)
          (fun o ho => by rw [mem_ofEff_n E 0 _ o ho]; exact Ne.symm hm) i]
        exact hP
      · refine relendableS_mono_rel (P' := fun αs' ls'' ρ => ∀ w,
            (P.2 αs' ls'' w ─⋆ OH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) 0 [] [] αs' ls''
              (((hndK (hndVal n (qualsVal (E.map Prod.fst)) hr hs)).comp K₁).plug (.val w))) ρ)
          (fun αs' ls'' hr' τ' hτ w τw τ'' hw hcw => ?_) ρk hk
        rw [Kont.plug_comp]
        exact hX₀ αs' ls'' _ τ'' hr' (hτ w τw τ'' hw hcw)

/-- **The handler at every continuation**: by induction on `e`'s piece, `hnd H` around it is the
piece outside, at every vector below the one it was installed at (`B`). -/
theorem openH_handle {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row} {A R : VTy}
    {hr hs : Val} (hS : S ≠ []) (hn : outN S₀ n = false) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlenE : E.length ≤ 2 ^ 32) (hE : ∀ q ∈ E, q.1 = .lin) {B : List Life}
    (hBlen : B.length = σ.length)
    (hret : ∀ αs', ReLend αs' B → ∀ ls v, Entails (RSlot (ℍ := ℍ) δ σ S₀ A αs' ls v)
      (BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs' ls (.app (.val hr) (.val v))))
    (hcl : ∀ j (hj : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧ ∀ αs', ReLend αs' B →
      ∀ ls x, Entails (RSlot (ℍ := ℍ) δ σ S₀ (.tensor E[j].2.1 (kTy S R .lin E[j].2.2)) αs' ls x)
        (BH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) αs' ls (.app (.val c) (.val x)))) :
    ∀ {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr} {ρ : WRes},
      List.Forall₂ (· ≤ ·) (αi ++ αo) B →
      OH (ℍ := ℍ) δ σ S₀ (CTy.effOf (Row.ofEff n E 0 ++ S) A) k ds αi αo ls e ρ →
      OH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) k ds αi αo ls
        (hndE (hndVal n (qualsVal (E.map Prod.fst)) hr hs) e) ρ := by
  intro k ds αi αo ls e ρ hB h
  let Mot : XT := fun k ds αi αo ls e ρ => List.Forall₂ (· ≤ ·) (αi ++ αo) B →
    OH (ℍ := ℍ) δ σ S₀ (CTy.effOf S R) k ds αi αo ls
      (hndE (hndVal n (qualsVal (E.map Prod.fst)) hr hs) e) ρ
  refine h Mot ?_ hB
  intro k ds αi αo ls e ρ hF hB
  refine openH_fold fun αi' hlt hch => ?_
  have hB' : List.Forall₂ (· ≤ ·) (αi' ++ αo) B :=
    forall₂_le_trans (forall₂_le_append (hlt.imp fun _ _ => le_of_lt) αo) hB
  have hlen : (αi' ++ αo).length = σ.length := hB'.length_eq.trans hBlen
  exact boxTop_mono (wand_mono_right (fun _ hb => bodyH_handle hS hn hnS hlenE hE ⟨hB', hch⟩ hlen
    hret hcl (fun _ _ _ _ hM => hM (by simpa using hB'))
    (fun _ _ _ _ hr' hM => hM (by simpa using forall₂_le_trans hr'.1 hB')) hb)) ρ
    (hF αi' hlt hch)

/-- **`[handle]` inside the borrower.** `handle_n e with H`, `H` a value form over a part of the
context whose live slots are persistent, re-lendable at the answer clause's and the clauses' types;
`n` not a name of the lenders' row nor of the row outside; the handler's operations linear; `e`
the piece at the handler's row ahead of `S`. The handler's clauses, holding nothing, are
re-lendable at every re-lend (`relendableS_empty`); the run is `bodyH_handle`, every continuation
`openH_handle`. -/
theorem pj_handle {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} (hS : S ≠ [])
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
    (hHv : PV (ℍ := ℍ) δ σ S₀ Δ Γ₁ H (.tensor (retTy S A R) (clausesTy S R E)))
    (hn : outN S₀ n = false) (hnS : ∀ o ∈ S, o.n ≠ n) (hlenE : E.length ≤ 2 ^ 32)
    (hE : ∀ q ∈ E, q.1 = .lin)
    (he : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 ++ S) A)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R) := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  obtain ⟨hl₁, hs₁⟩ := pure_sep_iff.mp hg₁
  obtain rfl : ρ₁ = PMap.empty := rSep_deadP hch hd hs₁
  rw [eq_of_compS_empty_left hc]
  have hval : IsVal (substAll γ H) := isVal_psub_valFormIn hl₁ hH
  have hwp := hHv αs ls γ PMap.empty hlen hch hΔ hg₁
  have hb := he αs ls γ ρ₂ hlen hch hΔ hg₂
  show wpG ls (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) H e)) _ ρ₂
  rw [psub_hndExpr]
  intro ρf fρ ps hf hcf hT htg Al k
  obtain ⟨ls', ρ', -, hv⟩ := wpTS_val_post (v := ⟨substAll γ H, hval⟩) hwp
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg
  obtain ⟨vr, vc, hq⟩ := hv
  obtain ⟨hpair, σr, σc, -, hVr, hVc⟩ := pure_sep_iff.mp hq
  have hHe : Expr.psub 0 γ H = (Val.pair vr vc).1 := congrArg Subtype.val hpair
  obtain ⟨o, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  obtain ⟨rfl, hVr⟩ := hVr
  have hret : ∀ αs', ReLend αs' αs → ∀ ls v, Entails (RSlot (ℍ := ℍ) δ σ S₀ A αs' ls v)
      (BH (ℍ := ℍ) δ σ S₀ (CTy.effOf (o :: S') R) αs' ls (.app (.val vr) (.val v))) :=
    fun αs' hr ls'' v τ hτ => relendableS_empty hVr ls'' (ext_empty' _ _) αs' hr v τ τ hτ
      (compS_empty_left τ)
  have hcl : ∀ j (hj : j < E.length), ∃ c, clauseAt vc.1 j = some c ∧ ∀ αs', ReLend αs' αs →
      ∀ ls x, Entails (RSlot (ℍ := ℍ) δ σ S₀ (.tensor E[j].2.1 (kTy (o :: S') R .lin E[j].2.2))
        αs' ls x) (BH (ℍ := ℍ) δ σ S₀ (CTy.effOf (o :: S') R) αs' ls (.app (.val c) (.val x))) := by
    intro j hj
    obtain ⟨c, hcj, hVcj⟩ := rslot_clausesTy_at hch E finsNil hVc j hj
    refine ⟨c, hcj, fun αs' hr ls'' x τ hτ => ?_⟩
    have hq : E[j].1 = .lin := hE _ (List.getElem_mem hj)
    generalize hEj : E[j] = t at hVcj hq hτ ⊢
    obtain ⟨q, Aj, Bj⟩ := t
    simp only at hq
    subst hq
    have hct : clauseTy (o :: S') R (Qual.lin, Aj, Bj) (finsNil j) =
        .bang (.thunk (.arr (.tensor Aj (kTy (o :: S') R .lin Bj)) (CTy.effOf (o :: S') R))) := by
      simp [clauseTy]
    rw [hct] at hVcj
    obtain ⟨-, hVcj⟩ := hVcj
    exact relendableS_empty hVcj ls'' (ext_empty' _ _) αs' hr x τ τ hτ (compS_empty_left τ)
  rw [hHe]
  exact bodyH_handle (ℍ := ℍ) hS hn hnS hlenE hE (reLend_refl hch) hlen hret hcl
    (fun _ _ _ _ hO => openH_handle hS hn hnS hlenE hE hlen hret hcl
      (by simp only [List.append_nil]; exact List.forall₂_same.mpr fun _ _ => le_rfl) hO)
    (fun _ _ _ _ hr hO => openH_handle hS hn hnS hlenE hE hlen hret hcl (by simpa using hr.1) hO)
    hb ρf fρ ps hf hcf hT htg Al k

end handle

end Law2

end
