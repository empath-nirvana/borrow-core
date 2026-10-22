import Spike670.Payload

/-!
# #670 — slice 2: `κ` (`genKap` and the κ site of `convDrive`, SPEC §49)

A drive's clause at a suspension receives `(v, κ)`. `κ` is a value the conversion **invents**: a
`&` closure over the handled computation's suspended `k` and a copy of each of the handler's
values. Its code has three functions, also invented:

- the resume entry `kres`: rebuilds `κ.1` as a `λ` closure over the same environment;
- the resume `kapR`: `κ.1 y` resumes `k` at `y` (`k.1 y`) and drives the outcome again
  (`driveFn`, with the handler's values: the handler is deep);
- the cancel `kcan`: `κ.2 ()` cancels `k` (`k.2 ()`) and answers at the cancel row
  (`toResult`), dropping the handler's values; at `⊤` it drops everything.

`genKap_fnsOK`: every function `genKap` writes consumes its parameters exactly once
(`FnsOK` is preserved). `kappaSite_lin`: the κ site's term consumes `k`, `v` and the handler's
values once, given that the clause's body consumes the pair and the handler's values; the copies
it makes are of the handler's values, which the kernel's `[handle]` rule keeps persistent
(`Ctx.DeadP Γ₁`, `CDerivesP.effHandleV`'s `hd`): that is the hypothesis `hD`.
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

variable {D : Var → Prop}

/-! ### Every function of the program consumes its parameters -/

/-- Every function so far is linear. -/
def AllFnsOK (D : Var → Prop) (s : CState) : Prop :=
  ∀ (i : Nat) (d : Fn), s.fns[i]? = some d → FnBodyOK D d


theorem AllFnsOK.same {s s' : CState} (h : AllFnsOK D s) (e : SameFns s s') : AllFnsOK D s' := by
  unfold SameFns at e; intro i d hd; rw [e] at hd; exact h i d hd

theorem fnBodyOK_placeholder (n : String) :
    FnBodyOK D { name := n, params := [], body := .unit, ret := .unit } :=
  ⟨List.nodup_nil, ⟨some ∅, .ops rfl .nil, .inr rfl⟩, List.nodup_nil, by simp [bnd]⟩

theorem AllFnsOK.reserveFn {s s' : CState} {n : String} {i : Nat} (h : AllFnsOK D s)
    (hr : Ok (reserveFn n) s i s') : AllFnsOK D s' := by
  have := ok_modifyGet hr
  simp only [Prod.mk.injEq] at this
  rw [this.2]
  intro j d hd
  simp only [Array.getElem?_push] at hd
  split at hd
  · cases hd; exact fnBodyOK_placeholder n
  · exact h j d hd

theorem AllFnsOK.setFn {s s' : CState} {i : Nat} {f : Fn} {u : Unit} (h : AllFnsOK D s)
    (hf : FnBodyOK D f) (hs : Ok (setFn i f) s u s') : AllFnsOK D s' := by
  rw [ok_modify hs]
  intro j d hd
  simp only [Array.set!, Array.getElem?_setIfInBounds] at hd
  split at hd
  · split at hd
    · cases hd; exact hf
    · cases hd
  · exact h j d hd

theorem same_addCode {c : Code} {s s' : CState} {i : Nat} (h : Ok (addCode c) s i s') :
    SameFns s s' := by
  have := ok_modifyGet h; simp only [Prod.mk.injEq] at this; rw [this.2]; rfl


/-- `tys.mapM fresh`: consecutive fresh variables. -/
theorem ok_mapM_fresh : ∀ {tys : List LTy} {s s' : CState} {xs : List Var},
    Ok (tys.mapM fresh) s xs s' →
    xs = List.range' s.next tys.length ∧ s'.next = s.next + tys.length ∧ s'.mach = s.mach ∧
      SameFns s s'
  | [], s, s', xs, h => by
    simp only [List.mapM_nil] at h; obtain ⟨rfl, rfl⟩ := ok_pure h; exact ⟨rfl, rfl, rfl, rfl⟩
  | t :: tys, s, s', xs, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨x, s₁, h₁, h⟩ := ok_bind h
    obtain ⟨rfl, hn, hm⟩ := ok_fresh h₁
    obtain ⟨xs', s₂, h₂, h⟩ := ok_bind h
    obtain ⟨rfl, hs⟩ := ok_pure h
    rw [hs]
    obtain ⟨rfl, hn', hm', hf'⟩ := ok_mapM_fresh h₂
    refine ⟨?_, by rw [hn', hn]; simp; omega, hm'.trans hm, (same_fresh h₁).trans hf'⟩
    rw [hn]; simp [List.range'_succ]

/-! ### The cancel's answer (`toResult`) -/

theorem ok_opAnswer {F : OutInfo} {op : Key} {s s' : CState} {r : LTy × Option Pay}
    (h : Ok (opAnswer F op) s r s') : s' = s := by
  unfold opAnswer at h; split at h
  · exact (ok_pure h).2
  · exact (ok_throw h).elim

theorem ok_kTyAt {F : OutInfo} {op : Key} {s s' : CState} {r : LTy}
    (h : Ok (kTyAt F op) s r s') : s' = s := by
  unfold kTyAt at h
  obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
  rw [(ok_pure h₂).2, ok_opAnswer h₁]

theorem ok_selTy {t : LTy} {j : Nat} {s s' : CState} {r : LTy} (h : Ok (selTy t j) s r s') :
    s' = s := by
  unfold selTy at h
  split at h
  · split at h
    · unfold selTy.repK at h; split at h <;> exact (ok_pure h).2
    · unfold selTy.repK at h; split at h <;> exact (ok_pure h).2
    · exact (ok_throw h).elim
  · exact (ok_throw h).elim

/-- An operand-only form consuming exactly its operands. -/
theorem closedL_ops {t : Tm} {xs : List Var} {Γ : Finset Var} (ho : operands t = some xs)
    (hn : xs.Nodup) (hΓ : Γ = xs.toFinset) : LinL D Γ t (some ∅) := by
  subst hΓ; refine .ops ho ?_
  clear ho
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    refine .cons (by simp) ?_
    have : (insert x xs.toFinset).erase x = xs.toFinset := by
      rw [Finset.erase_insert]; simpa using (List.nodup_cons.1 hn).1
    simp only [List.toFinset_cons, this]
    exact ih (List.nodup_cons.1 hn).2

theorem range'_nodup_cons {a L : Nat} : (a :: List.range' (a + 1) L).Nodup := by
  rw [List.nodup_cons]; exact ⟨by simp, List.nodup_range' ..⟩

/-- The resume function's record: `k`, the handler's values and `y` consecutive from `a`, `kr` and
`o` after them. -/
theorem kap_record (a L drive : Nat) (name : String) (ret : LTy) :
    FnBodyOK D (Fn.mk name (a :: List.range' (a + 1) L ++ [a + 1 + L])
      (.letv (a + 1 + L + 1) (.sel a 0)
        (.letv (a + 1 + L + 1 + 1) (.app (a + 1 + L + 1) (a + 1 + L))
          (.call drive (List.range' (a + 1) L ++ [a + 1 + L + 1 + 1])))) ret none) := by
  have hp : a :: List.range' (a + 1) L ++ [a + 1 + L] = List.range' a (L + 2) := by
    rw [List.range'_succ, List.range'_concat]; simp <;> omega
  refine ⟨by rw [hp]; exact List.nodup_range' .., ⟨some ∅, ?_, .inr rfl⟩, ?_, ?_⟩
  · refine .letv (.ops rfl (.cons (by simp) .nil)) ?_
    refine .letv (.ops rfl (.cons (by simp) (.cons ?_ .nil))) ?_
    · simp [List.mem_range'_1] <;> vomega
    · apply closedL_ops rfl
      · rw [List.nodup_append]
        refine ⟨List.nodup_range' .., List.nodup_singleton _, ?_⟩
        intro z hz w hw; simp [List.mem_range'_1] at hz hw; vomega
      · ext z
        simp only [Finset.mem_erase, Finset.mem_insert, List.mem_toFinset, List.mem_range'_1,
          List.mem_append, List.mem_cons, List.mem_singleton, ne_eq, List.not_mem_nil, or_false]
        vomega
  · simp [bnd]
  · intro z hz hm
    simp [bnd] at hz
    simp [List.mem_range'_1] at hm
    vomega

/-- The cancel at `⊤`: everything dropped. -/
theorem can_top_record (b L : Nat) (name : String) (ret : LTy) :
    FnBodyOK D (Fn.mk name (b :: List.range' (b + 1) L)
      (.drop b (drops (List.range' (b + 1) L) .unit)) ret none) := by
  refine ⟨range'_nodup_cons, ⟨some ∅, ?_, .inr rfl⟩, by simp [bnd, bnd_drops], by
    simp [bnd, bnd_drops]⟩
  refine .drop (by simp) (LinL.drops (List.nodup_range' ..) (fun x hx => ?_) ?_)
  · simp only [List.mem_range'_1] at hx
    simp only [Finset.mem_erase, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
      List.mem_range'_1]
    vomega
  · have : (insert b (List.range' (b + 1) L).toFinset).erase b \ (List.range' (b + 1) L).toFinset
        = ∅ := by
      ext z; simp [List.mem_range'_1] <;> vomega
    simp only [List.toFinset_cons]; rw [this]; exact .ops rfl .nil

/-- The cancel at a row: `k.2 ()` taken, the handler's values dropped, the answer made. -/
theorem can_ret_record (b L : Nat) (name : String) (ret : LTy) (body : Tm)
    (hb : ClosedL D {b + 1 + L} body) (hn : (bnd body).Nodup)
    (hr : ∀ y ∈ bnd body, b + 1 + L + 1 ≤ y) :
    FnBodyOK D (Fn.mk name (b :: List.range' (b + 1) L)
      (.letv (b + 1 + L) (.sel b 1) (drops (List.range' (b + 1) L) body)) ret none) := by
  obtain ⟨Δ, l, c⟩ := hb
  refine ⟨range'_nodup_cons, ⟨Δ, ?_, c⟩, ?_, ?_⟩
  · refine .letv (.ops rfl (.cons (by simp) .nil)) ?_
    refine LinL.drops (List.nodup_range' ..) (fun x hx => ?_) ?_
    · simp only [List.mem_range'_1] at hx
      simp only [Finset.mem_insert, Finset.mem_erase, List.toFinset_cons, List.mem_toFinset,
        List.mem_range'_1]
      vomega
    · convert l using 1
      ext z; simp [List.mem_range'_1] <;> vomega
  · simp only [bnd, bnd_drops, List.nil_append, List.nodup_cons]
    exact ⟨fun h => by have := hr _ h; vomega, hn⟩
  · intro z hz hm
    simp only [bnd, bnd_drops, List.nil_append, List.mem_cons] at hz
    simp [List.mem_range'_1] at hm
    rcases hz with rfl | hz
    · vomega
    · have := hr z hz; vomega

/-- **`κ`'s functions are linear.** -/
theorem genKap_fnsOK {n : UInt32} {idx : Nat} {kT : LTy} {T : OutInfo} {outTy : LTy}
    {driveFn : Nat} {hvTys : List LTy} {cM : Option OutInfo} {cPay : Pay} {s s' : CState}
    {kc : Nat}
    (hres : ∀ cpIn c s₁ b s₂, c < s₁.next → Ok (toResult .unit cpIn cM cPay c) s₁ b s₂ →
      SameFns s₁ s₂ ∧ s₁.next ≤ s₂.next ∧ ClosedL D {c} b ∧ (bnd b).Nodup ∧
        ∀ y ∈ bnd b, s₁.next ≤ y)
    (hF : AllFnsOK D s) (h : Ok (genKap n idx kT T outTy driveFn hvTys cM cPay) s kc s') :
    AllFnsOK D s' := by
  simp only [genKap] at h
  split at h
  swap; · exact (ok_throw h).elim
  split at h
  swap; · exact (ok_throw h).elim
  rename_i kL bT oT cK
  split at h
  swap; · obtain ⟨_, _, h', _⟩ := ok_bind h; exact (ok_throw h').elim
  obtain ⟨⟨_, cpIn⟩, s₁, h₁, h⟩ := ok_bind h
  rw [ok_opAnswer h₁] at h
  obtain ⟨kIn, s₂, h₂, h⟩ := ok_bind h
  rw [ok_kTyAt h₂] at h
  obtain ⟨kapR, s₃, h₃, h⟩ := ok_bind h
  have F₃ := hF.reserveFn h₃
  obtain ⟨rc, s₄, h₄, h⟩ := ok_bind h
  have F₄ := F₃.same (same_addCode h₄)
  obtain ⟨kres, s₅, h₅, h⟩ := ok_bind h
  have F₅ := F₄.reserveFn h₅
  obtain ⟨kcan, s₆, h₆, h⟩ := ok_bind h
  have F₆ := F₅.reserveFn h₆
  obtain ⟨kc', s₇, h₇, h⟩ := ok_bind h
  have F₇ := F₆.same (same_addCode h₇)
  -- The resume entry.
  obtain ⟨k₀, s₈, h₈, h⟩ := ok_bind h
  obtain ⟨rfl, hn₈, -⟩ := ok_fresh h₈
  have F₈ := F₇.same (same_fresh h₈)
  obtain ⟨hv₀, s₉, h₉, h⟩ := ok_bind h
  obtain ⟨rfl, -, -, sf₉⟩ := ok_mapM_fresh h₉
  have F₉ := F₈.same sf₉
  obtain ⟨_, s₁₀, h₁₀, h⟩ := ok_bind h
  have F₁₀ := F₉.setFn ?res h₁₀
  case res =>
    rw [hn₈]
    exact ⟨range'_nodup_cons, ⟨some ∅, closedL_ops rfl range'_nodup_cons rfl, .inr rfl⟩,
      List.nodup_nil, by simp [bnd]⟩
  -- The resume.
  obtain ⟨k₁, s₁₁, h₁₁, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₁, -⟩ := ok_fresh h₁₁
  have F₁₁ := F₁₀.same (same_fresh h₁₁)
  obtain ⟨hv₁, s₁₂, h₁₂, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₂, -, sf₁₂⟩ := ok_mapM_fresh h₁₂
  have F₁₂ := F₁₁.same sf₁₂
  obtain ⟨y, s₁₃, h₁₃, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₃, -⟩ := ok_fresh h₁₃
  have F₁₃ := F₁₂.same (same_fresh h₁₃)
  obtain ⟨krT, s₁₄, h₁₄, h⟩ := ok_bind h
  rw [ok_selTy h₁₄] at h
  obtain ⟨kr, s₁₅, h₁₅, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₅, -⟩ := ok_fresh h₁₅
  have F₁₅ := F₁₃.same (same_fresh h₁₅)
  obtain ⟨o, s₁₆, h₁₆, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₆, -⟩ := ok_fresh h₁₆
  have F₁₆ := F₁₅.same (same_fresh h₁₆)
  obtain ⟨_, s₁₇, h₁₇, h⟩ := ok_bind h
  have F₁₇ := F₁₆.setFn ?kap h₁₇
  case kap =>
    rw [hn₁₅, hn₁₃, hn₁₂, hn₁₁]
    exact kap_record _ _ _ _ _
  -- The cancel.
  obtain ⟨k₂, s₁₈, h₁₈, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₈, -⟩ := ok_fresh h₁₈
  have F₁₈ := F₁₇.same (same_fresh h₁₈)
  obtain ⟨hv₂, s₁₉, h₁₉, h⟩ := ok_bind h
  obtain ⟨rfl, hn₁₉, -, sf₁₉⟩ := ok_mapM_fresh h₁₉
  have F₁₉ := F₁₈.same sf₁₉
  split at h
  all_goals try (obtain ⟨_, _, h', _⟩ := ok_bind h; exact (ok_throw h').elim)
  · -- `⊤`: a linear `κ`'s cancel, never run.
    obtain ⟨_, s₂₀, h₂₀, h⟩ := ok_bind h
    obtain ⟨-, rfl⟩ := ok_pure h
    refine F₁₉.setFn ?_ h₂₀
    rw [hn₁₈]; exact can_top_record _ _ _ _
  · cases cM <;> simp only at h <;> split at h
    all_goals try (obtain ⟨_, _, h', _⟩ := ok_bind h; exact (ok_throw h').elim)
    all_goals
      obtain ⟨c, s₂₀, h₂₀, h⟩ := ok_bind h
      obtain ⟨rfl, hn₂₀, -⟩ := ok_fresh h₂₀
      have F₂₀ := F₁₉.same (same_fresh h₂₀)
      obtain ⟨body, s₂₁, h₂₁, h⟩ := ok_bind h
      obtain ⟨sf, -, cl, nd, rg⟩ := hres _ _ _ _ _ (by rw [hn₂₀]; vomega) h₂₁
      have F₂₁ := F₂₀.same sf
      obtain ⟨_, s₂₂, h₂₂, h⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_pure h
      refine F₂₁.setFn ?_ h₂₂
      rw [hn₁₉, hn₁₈] at cl ⊢
      exact can_ret_record _ _ _ _ _ cl nd (fun y hy => by
        have := rg y hy; rw [hn₂₀, hn₁₉, hn₁₈] at this; vomega)

/-- **`κ`'s functions are linear**, the cancel's answer by `toResult_spec`. -/
theorem genKap_linear {n : UInt32} {idx : Nat} {kT : LTy} {T : OutInfo} {outTy : LTy}
    {driveFn : Nat} {hvTys : List LTy} {cM : Option OutInfo} {cPay : Pay} {s s' : CState}
    {kc : Nat} (hF : AllFnsOK D s) (h : Ok (genKap n idx kT T outTy driveFn hvTys cM cPay) s kc s') :
    AllFnsOK D s' :=
  genKap_fnsOK (fun _ _ _ _ _ hc hr => by
    obtain ⟨sf, g, p⟩ := toResult_spec (D := D) hr hc
    exact ⟨sf, g.next, p.closed, p.nodup, fun y hy => (p.range y hy).1⟩) hF h

end Backend2.Spike670

namespace Backend2.Spike670
open Backend2

variable {D : Var → Prop}

/-! ### The κ site (`convDrive`, `suspArms`, a clause of the node's own operation) -/

/-- The site's copies of the handler's values, `x` copied to `x'`, outermost first. -/
def copiesOf (ps : List (Var × Var)) (t : Tm) : Tm := ps.foldr (fun (x, x') t => .copy x x' t) t

/-- Copies made in turn: each original owned and duplicable, each copy new. -/
theorem LinL.copies {Γ : Finset Var} {t : Tm} {Δ : Option (Finset Var)} :
    ∀ (ps : List (Var × Var)), (∀ p ∈ ps, p.1 ∈ Γ ∧ D p.1) →
      LinL D (Γ ∪ (ps.map Prod.snd).toFinset) t Δ → LinL D Γ (copiesOf ps t) Δ
  | [], _, h => by simpa [copiesOf] using h
  | (x, x') :: ps, hp, h => by
    simp only [copiesOf, List.foldr_cons]
    refine .copy (hp (x, x') (by simp)).1 (hp (x, x') (by simp)).2 ?_
    refine LinL.copies ps (fun p hp' => ⟨Finset.mem_insert_of_mem (hp p (by simp [hp'])).1,
      (hp p (by simp [hp'])).2⟩) ?_
    convert h using 1
    ext z; simp <;> tauto

/-- Consuming a list disjoint from the rest. -/
theorem useAll_append : ∀ {A : Finset Var} {L : List Var}, L.Nodup → (∀ x ∈ L, x ∉ A) →
    UseAll (A ∪ L.toFinset) L A
  | _, [], _, _ => by simpa using UseAll.nil
  | A, x :: L, hn, hd => by
    refine .cons (by simp) ?_
    have : (A ∪ (x :: L).toFinset).erase x = A ∪ L.toFinset := by
      ext z; by_cases hz : z = x
      · subst hz; simp [hd z (by simp), (List.nodup_cons.1 hn).1]
      · simp [hz]
    rw [this]; exact useAll_append (List.nodup_cons.1 hn).2 (fun y hy => hd y (by simp [hy]))

/-- **The κ site's term**: the handler's values copied into `κ = clos kap (k :: copies)`, the
clause's body on `(v, κ)`. It consumes `k`, `v` and the handler's values, once each, when the body
consumes the pair and the handler's values. -/
theorem kappaSite_lin {k v kv pr kap : Var} {hv hvC : List Var} {body : Tm}
    {Δ : Option (Finset Var)}
    (hlen : hv.length = hvC.length) (hnC : hvC.Nodup)
    (hD : ∀ x ∈ hv, D x)
    (hC : ∀ x ∈ hvC, x ∉ hv ∧ x ≠ k ∧ x ≠ v)
    (hkv : k ≠ v) (hk : k ∉ hv) (hv' : v ∉ hv)
    (hkvf : kv ∉ hv ∧ kv ≠ v) (hpr : pr ∉ hv)
    (hb : LinL D (insert pr hv.toFinset) body Δ) :
    LinL D (insert k (insert v hv.toFinset))
      (copiesOf (hv.zip hvC) (.letv kv (.clos kap (k :: hvC)) (.letv pr (.pair v kv) body))) Δ := by
  refine LinL.copies _ (fun p hp => ?_) ?_
  · obtain ⟨x, x'⟩ := p
    have := List.of_mem_zip hp
    exact ⟨by simp [this.1], hD x this.1⟩
  · rw [List.map_snd_zip (by omega)]
    refine .letv (Γ₁ := insert v hv.toFinset) (.ops rfl ?_) (.letv (Γ₁ := hv.toFinset) (.ops rfl ?_) hb)
    · refine .cons (by simp) ?_
      have e : (insert k (insert v hv.toFinset) ∪ hvC.toFinset).erase k =
          insert v hv.toFinset ∪ hvC.toFinset := by
        ext z; by_cases hz : z = k
        · subst hz; simp [hkv, hk]; intro h; exact (hC z h).2.1 rfl
        · simp [hz]
      rw [e]
      exact useAll_append hnC (fun x hx h => by
        simp at h; rcases h with rfl | h
        · exact (hC _ hx).2.2 rfl
        · exact (hC _ hx).1 h)
    · refine .cons (by simp) (.cons ?_ ?_)
      · simp; exact fun h => hkvf.2 h
      · have e : ((insert kv (insert v hv.toFinset)).erase v).erase kv = hv.toFinset := by
          ext z; by_cases hz : z = kv
          · subst hz; simp [hkvf.1]
          · by_cases hz' : z = v
            · subst hz'; simp [hv']
            · simp [hz, hz']
        rw [e]; exact .nil

end Backend2.Spike670
