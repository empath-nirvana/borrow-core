import Spike670.LinOK
import Backend2.Lint

/-!
# #670 — `Lint.lint` is sound for `LinOK`

`lint_sound : lint p = .ok () → LinOK p (fun _ => True)`. The duplicability side condition of
`copy` is `True`: `Lint` does not check it, and cannot from the LIR's types (`!` is erased; see
`Spike670/LinOK.lean`).
-/

namespace Backend2.Spike670
open Backend2 Backend2.Lint

/-! ### The monad -/

theorem okS_bind {σ α β : Type} {x : StateT σ (Except String) α} {f : α → StateT σ (Except String) β}
    {s : σ} {r : β × σ} (h : (x >>= f) s = .ok r) : ∃ a s', x s = .ok (a, s') ∧ f a s' = .ok r := by
  simp only [bind, StateT.bind] at h
  cases hx : x s with
  | error e => rw [hx] at h; cases h
  | ok q => rw [hx] at h; exact ⟨q.1, q.2, by simp, h⟩

theorem okS_pure {σ α : Type} {a : α} {s : σ} {r : α × σ}
    (h : (pure a : StateT σ (Except String) α) s = .ok r) : r = (a, s) := by
  simp only [pure, StateT.pure, Except.pure] at h; cases h; rfl

theorem bad_not_ok {w m : String} {s : St} {r : α × St} (h : (bad w m : LM α) s = .ok r) : False := by
  simp [bad, throw, throwThe, MonadExceptOf.throw, StateT.lift] at h

/-! ### Hash sets as finite sets -/

/-- The finite set of a hash set's elements. -/
def toF (h : Std.HashSet Var) : Finset Var := h.toList.toFinset

theorem mem_toF {h : Std.HashSet Var} {x : Var} : x ∈ toF h ↔ h.contains x = true := by
  simp [toF, Std.HashSet.mem_toList, Std.HashSet.contains_iff_mem]

theorem toF_erase (h : Std.HashSet Var) (x : Var) : toF (h.erase x) = (toF h).erase x := by
  ext y; simp only [mem_toF, Std.HashSet.contains_erase, Finset.mem_erase]
  by_cases e : y = x
  · subst e; simp
  · have : (x == y) = false := by simpa using Ne.symm e
    simp [e, this]

theorem toF_insert (h : Std.HashSet Var) (x : Var) : toF (h.insert x) = insert x (toF h) := by
  ext y; simp only [mem_toF, Std.HashSet.contains_insert, Finset.mem_insert, Bool.or_eq_true,
    beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact .inl h.symm
    · exact .inr h
  · rintro (h | h)
    · exact .inl h.symm
    · exact .inr h

theorem toF_empty : toF (∅ : Std.HashSet Var) = ∅ := by
  ext y; simp [mem_toF]

theorem toF_card (h : Std.HashSet Var) : (toF h).card = h.size := by
  rw [toF, List.toFinset_card_of_nodup, Std.HashSet.length_toList]
  have := (Std.HashSet.distinct_toList (m := h))
  exact this.imp fun {a b} e => by simpa using e

theorem sameSet_toF {a b : Std.HashSet Var} (h : sameSet a b = true) : toF a = toF b := by
  simp only [sameSet, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hs, hall⟩ := h
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [toF_card, toF_card, hs])
  rw [mem_toF]; exact hall y (by simpa [toF] using hy)

theorem toF_isEmpty {h : Std.HashSet Var} (e : h.isEmpty = true) : toF h = ∅ := by
  ext y; simp only [mem_toF, Finset.notMem_empty, iff_false]
  intro hc
  exact (Std.HashSet.isEmpty_iff_forall_not_mem.1 e) y (Std.HashSet.contains_iff_mem.1 hc)

/-! ### The checks -/

theorem use_ok {w : String} {env : Std.HashSet Var} {x : Var} {s : St} {r}
    (h : use w env x s = .ok r) : env.contains x = true ∧ r = (env.erase x, s) := by
  simp only [use] at h
  split at h
  · obtain ⟨_, _, h, _⟩ := okS_bind h; exact (bad_not_ok h).elim
  · rename_i hc; simp at hc; exact ⟨hc, okS_pure h⟩

theorem useAll_ok {w : String} : ∀ {xs : List Var} {env : Std.HashSet Var} {s : St} {r},
    useAll w env xs s = .ok r → UseAll (toF env) xs (toF r.1) ∧ r.2 = s
  | [], env, s, r, h => by
    simp only [useAll, List.foldlM_nil] at h; cases okS_pure h; exact ⟨.nil, rfl⟩
  | x :: xs, env, s, r, h => by
    simp only [useAll, List.foldlM_cons] at h
    obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
    obtain ⟨hc, he⟩ := use_ok h₁
    cases he
    obtain ⟨hu, hs⟩ := useAll_ok (xs := xs) h₂
    refine ⟨.cons (mem_toF.2 hc) ?_, hs⟩
    rwa [← toF_erase]

theorem bindNew_ok {w : String} {p : Prog} {env : Std.HashSet Var} {x : Var} {s : St} {r}
    (h : bindNew w p env x s = .ok r) :
    p.ty.contains x = true ∧ s.bound.contains x = false ∧ r = (env.insert x, ⟨s.bound.insert x⟩) := by
  simp only [bindNew] at h
  split at h
  · obtain ⟨_, _, h, _⟩ := okS_bind h; exact (bad_not_ok h).elim
  rename_i ht; simp at ht
  obtain ⟨d, s₁, h₁, h₂⟩ := okS_bind h
  simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at h₁
  cases h₁
  split at h₂
  · obtain ⟨_, _, h, _⟩ := okS_bind h₂; exact (bad_not_ok h).elim
  rename_i hb; simp at hb
  obtain ⟨_, s₂, h₃, h₄⟩ := okS_bind h₂
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure] at h₃
  subst h₃
  exact ⟨ht, Bool.eq_false_iff.2 (fun h => hb (Std.HashSet.contains_iff_mem.1 h)), okS_pure h₄⟩

/-- A loop whose body only checks: its state is unchanged, and the body succeeded at each
element. -/
theorem forIn_check {γ : Type} {f : γ → PUnit → LM (ForInStep PUnit)}
    (hf : ∀ a s q, f a PUnit.unit s = .ok q → q.2 = s ∧ q.1 = .yield PUnit.unit) :
    ∀ {l : List γ} {s : St} {r}, forIn l PUnit.unit f s = .ok r →
      r.2 = s ∧ ∀ a ∈ l, ∃ q, f a PUnit.unit s = .ok q
  | [], s, r, h => by simp only [List.forIn_nil] at h; cases okS_pure h; exact ⟨rfl, by simp⟩
  | a :: l, s, r, h => by
    simp only [List.forIn_cons] at h
    obtain ⟨st, s₁, h₁, h₂⟩ := okS_bind h
    obtain ⟨e₁, e₂⟩ := hf a s _ h₁
    simp only at e₁ e₂; subst e₁; subst e₂
    obtain ⟨hs, hall⟩ := forIn_check hf h₂
    exact ⟨hs, fun b hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, h₁⟩
      · exact hall b hb⟩

/-- **`lintTm` is sound**: a term it accepts is `Lin` at the bound set it threads. -/
theorem lintTm_sound {w : String} {p : Prog} : ∀ (f : Nat) (env : Std.HashSet Var) (t : Tm)
    (s : St) (r : Left × St), lintTm w p f env t s = .ok r →
    Lin p (fun _ => True) (toF s.bound) (toF env) t (r.1.map toF) (toF r.2.bound)
  | 0, env, t, s, r, h => by rw [lintTm.eq_def] at h; exact (bad_not_ok h).elim
  | f + 1, env, t, s, r, h => by
    rw [lintTm.eq_def] at h
    have ops : ∀ xs, operands t = some xs → AritiesOK p t →
        (useAll w env xs s = .ok (r.1.getD ∅ |> fun e => e, r.2) → True) → True := fun _ _ _ _ => trivial
    clear ops
    cases t with
    | var x =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he; cases okS_pure h₂
      exact .ops rfl trivial (.cons (mem_toF.2 hc) (by rw [toF_erase]; exact .nil))
    | unit => cases okS_pure h; exact .ops rfl trivial .nil
    | lit c => cases okS_pure h; exact .ops rfl trivial .nil
    | pair a b =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hu, hs⟩ := useAll_ok h₁; cases okS_pure h₂; simp only at hs; subst hs
      exact .ops rfl trivial hu
    | inj rt a =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he; cases okS_pure h₂
      exact .ops rfl trivial (.cons (mem_toF.2 hc) (by rw [toF_erase]; exact .nil))
    | clos c xs =>
      simp only at h
      cases hcode : p.codes[c]? with
      | none => rw [hcode] at h; exact (bad_not_ok h).elim
      | some code =>
        rw [hcode] at h
        obtain ⟨_, s₁, h₁, h₂⟩ := okS_bind h
        obtain ⟨hs, hall⟩ := forIn_check (fun a s q hq => by
          cases hfa : p.fns[a]? with
          | none => rw [hfa] at hq; obtain ⟨_, _, hb, _⟩ := okS_bind hq; exact (bad_not_ok hb).elim
          | some d =>
            rw [hfa] at hq; dsimp only at hq
            split at hq <;> split at hq <;> first
              | (obtain ⟨_, _, hb, _⟩ := okS_bind hq; exact (bad_not_ok hb).elim)
              | (cases okS_pure hq; exact ⟨rfl, rfl⟩)) h₁
        simp only at hs; subst hs
        obtain ⟨e, s₂, h₃, h₄⟩ := okS_bind h₂
        obtain ⟨hu, hs⟩ := useAll_ok h₃; cases okS_pure h₄; simp only at hs; subst hs
        refine .ops rfl ⟨code, hcode, fun fn hfn => ?_⟩ hu
        obtain ⟨q, hq⟩ := hall fn hfn
        cases hfa : p.fns[fn]? with
        | none => rw [hfa] at hq; obtain ⟨_, _, hb, _⟩ := okS_bind hq; exact (bad_not_ok hb).elim
        | some d =>
          rw [hfa] at hq; dsimp only at hq
          refine ⟨d, rfl, ?_⟩
          split at hq
          · rename_i hkind
            split at hq
            · obtain ⟨_, _, hb, _⟩ := okS_bind hq; exact (bad_not_ok hb).elim
            · rename_i hk; rw [if_pos hkind]; simpa using hk
          · rename_i hkind
            split at hq
            · obtain ⟨_, _, hb, _⟩ := okS_bind hq; exact (bad_not_ok hb).elim
            · rename_i hk; rw [if_neg hkind]; simpa using hk
    | app g a =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hu, hs⟩ := useAll_ok h₁; cases okS_pure h₂; simp only at hs; subst hs
      exact .ops rfl trivial hu
    | app0 g =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he; cases okS_pure h₂
      exact .ops rfl trivial (.cons (mem_toF.2 hc) (by rw [toF_erase]; exact .nil))
    | sel g j =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he; cases okS_pure h₂
      exact .ops rfl trivial (.cons (mem_toF.2 hc) (by rw [toF_erase]; exact .nil))
    | call fn as =>
      simp only at h
      cases hd : p.fns[fn]? with
      | none => rw [hd] at h; exact (bad_not_ok h).elim
      | some d =>
        rw [hd] at h; simp only at h
        split at h
        · obtain ⟨_, _, hb, _⟩ := okS_bind h; exact (bad_not_ok hb).elim
        · rename_i hl
          obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
          obtain ⟨hu, hs⟩ := useAll_ok h₁; cases okS_pure h₂; simp only at hs; subst hs
          exact .ops rfl ⟨d, hd, by simpa using hl⟩ hu
    | prim op as =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hu, hs⟩ := useAll_ok h₁; cases okS_pure h₂; simp only at hs; subst hs
      exact .ops rfl trivial hu
    | letv x e b =>
      obtain ⟨l, s₁, h₁, h₂⟩ := okS_bind h
      have ih₁ := lintTm_sound f env e s (l, s₁) h₁
      cases l with
      | none => cases okS_pure h₂; exact .letvNone ih₁
      | some env' =>
        obtain ⟨e₂, s₂, h₃, h₄⟩ := okS_bind h₂
        obtain ⟨ht, hb, he⟩ := bindNew_ok h₃
        cases he
        have ih₂ := lintTm_sound f _ b _ r h₄
        rw [toF_insert, toF_insert] at ih₂
        exact .letv ih₁ (by rw [mem_toF]; simp [hb]) ht ih₂
    | letpair x y q b =>
      obtain ⟨e₁, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he
      obtain ⟨e₂, s₂, h₃, h₄⟩ := okS_bind h₂
      obtain ⟨ht₁, hb₁, he₁⟩ := bindNew_ok h₃; cases he₁
      obtain ⟨e₃, s₃, h₅, h₆⟩ := okS_bind h₄
      obtain ⟨ht₂, hb₂, he₂⟩ := bindNew_ok h₅; cases he₂
      have ih := lintTm_sound f _ b _ r h₆
      simp only [toF_insert, toF_erase] at ih
      refine .letpair (mem_toF.2 hc) (by rw [mem_toF]; simp [hb₁]) ht₁ ?_ ht₂ ih
      rw [← toF_insert, mem_toF]; simpa using hb₂
    | case sv x b₁ y b₂ =>
      obtain ⟨e₁, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he
      obtain ⟨e₂, s₂, h₃, h₄⟩ := okS_bind h₂
      obtain ⟨ht₁, hb₁, he₁⟩ := bindNew_ok h₃; cases he₁
      obtain ⟨l₁, s₃, h₅, h₆⟩ := okS_bind h₄
      have ih₁ := lintTm_sound f _ b₁ _ _ h₅
      obtain ⟨e₃, s₄, h₇, h₈⟩ := okS_bind h₆
      obtain ⟨ht₂, hb₂, he₂⟩ := bindNew_ok h₇; cases he₂
      obtain ⟨l₂, s₅, h₉, h₁₀⟩ := okS_bind h₈
      have ih₂ := lintTm_sound f _ b₂ _ _ h₉
      simp only [toF_insert, toF_erase] at ih₁ ih₂
      have hj : r.2 = s₅ ∧ Join (l₁.map toF) (l₂.map toF) (r.1.map toF) := by
        simp only at h₁₀
        cases l₁ with
        | none => cases okS_pure h₁₀; exact ⟨rfl, rfl⟩
        | some a =>
          cases l₂ with
          | none => cases okS_pure h₁₀; exact ⟨rfl, rfl⟩
          | some b =>
            simp only at h₁₀
            split at h₁₀
            · obtain ⟨_, _, hb, _⟩ := okS_bind h₁₀; exact (bad_not_ok hb).elim
            · rename_i hs; simp at hs
              cases okS_pure h₁₀
              exact ⟨rfl, sameSet_toF hs, rfl⟩
      rw [hj.1]
      exact .case (mem_toF.2 hc) (by rw [mem_toF]; simp [hb₁]) ht₁ ih₁
        (by rw [mem_toF]; simp [hb₂]) ht₂ ih₂ hj.2
    | absurd sv =>
      obtain ⟨e, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he; cases okS_pure h₂
      exact .absurd (mem_toF.2 hc)
    | copy x x' b =>
      simp only at h
      split at h
      · obtain ⟨_, _, hb, _⟩ := okS_bind h; exact (bad_not_ok hb).elim
      rename_i hc; simp at hc
      obtain ⟨e₂, s₂, h₃, h₄⟩ := okS_bind h
      obtain ⟨ht, hb, he⟩ := bindNew_ok h₃; cases he
      have ih := lintTm_sound f _ b _ r h₄
      rw [toF_insert, toF_insert] at ih
      exact .copy (mem_toF.2 (Std.HashSet.contains_iff_mem.2 hc)) trivial
        (by rw [mem_toF]; simp [hb]) ht ih
    | drop x b =>
      obtain ⟨e₁, s₁, h₁, h₂⟩ := okS_bind h
      obtain ⟨hc, he⟩ := use_ok h₁; cases he
      have ih := lintTm_sound f _ b _ r h₂
      rw [toF_erase] at ih
      exact .drop (mem_toF.2 hc) ih

/-! ### The program -/

theorem forIn_ruleS {σ γ β : Type} (L : List γ) (f : γ → β → StateT σ (Except String) (ForInStep β))
    (I : List γ → β → σ → Prop)
    (step : ∀ pfx a rest b s r, pfx ++ a :: rest = L → I pfx b s → f a b s = .ok r →
      ∃ b', r.1 = .yield b' ∧ I (pfx ++ [a]) b' r.2) :
    ∀ (rest pfx : List γ) (b : β) (s : σ) (r : β × σ), pfx ++ rest = L →
      I pfx b s → forIn rest b f s = .ok r → I L r.1 r.2 := by
  intro rest
  induction rest with
  | nil =>
    intro pfx b s r hL hI h
    simp only [List.forIn_nil] at h
    cases okS_pure h
    simpa [← hL] using hI
  | cons a rest ih =>
    intro pfx b s r hL hI h
    simp only [List.forIn_cons] at h
    obtain ⟨st, s₁, h₁, h₂⟩ := okS_bind h
    obtain ⟨b', hy, hI'⟩ := step pfx a rest b s _ hL hI h₁
    simp only at hy; subst hy
    exact ih (pfx ++ [a]) b' s₁ r (by simp [← hL]) hI' h₂

theorem ParamsOK.snoc {p : Prog} : ∀ {B xs B' x}, ParamsOK p B xs B' → x ∉ B' → Typed p x →
    ParamsOK p B (xs ++ [x]) (insert x B')
  | _, [], _, _, .nil, h, t => .cons h t .nil
  | _, _ :: _, _, _, .cons a b c, h, t => .cons a b (ParamsOK.snoc c h t)

theorem FnsOK.snoc {p : Prog} {D : Var → Prop} : ∀ {B ds B₁ d B₂}, FnsOK p D B ds B₁ →
    FnOK p D B₁ d B₂ → FnsOK p D B (ds ++ [d]) B₂
  | _, [], _, _, _, .nil, h => .cons h .nil
  | _, _ :: _, _, _, _, .cons a b, h => .cons a (FnsOK.snoc b h)

/-- **`Lint.lint` is sound**: a program it accepts is linear, at the duplicability predicate
`True` (it does not check `copy`'s type). -/
theorem lint_sound {p : Prog} (h : lint p = .ok ()) : LinOK p (fun _ => True) := by
  simp only [lint, bind, Except.bind] at h
  split at h
  · cases h
  rename_i r hr
  simp only [StateT.run] at hr
  obtain ⟨_, s₁, h₁, h₂⟩ := okS_bind hr
  -- The functions, in order.
  have hF := forIn_ruleS (σ := St) p.fns.toList.zipIdx _
    (fun pfx _ (st : St) => FnsOK p (fun _ => True) ∅ (pfx.map Prod.fst) (toF st.bound))
    ?step p.fns.toList.zipIdx [] PUnit.unit {} _ (by simp) (by simpa [toF_empty] using FnsOK.nil) h₁
  case step =>
    intro pfx a rest b st r' _ hI hf
    obtain ⟨d, i⟩ := a
    obtain ⟨env, s₂, h₃, h₄⟩ := okS_bind hf
    -- The parameters.
    have hP := forIn_ruleS (σ := St) d.params _
      (fun q (env : Std.HashSet Var) (st' : St) => toF env = q.toFinset ∧
        ParamsOK p (toF st.bound) q (toF st'.bound))
      ?pstep d.params [] ∅ st _ (by simp) ⟨toF_empty, .nil⟩ h₃
    case pstep =>
      intro q x rest' env' st' r'' _ hI' hf'
      obtain ⟨e', s₄, h₅, h₆⟩ := okS_bind hf'
      obtain ⟨ht, hb, he⟩ := bindNew_ok h₅; cases he
      cases okS_pure h₆
      refine ⟨_, rfl, ?_, ?_⟩
      · rw [toF_insert, hI'.1]; ext z; simp [or_comm]
      · rw [toF_insert]
        exact hI'.2.snoc (by rw [mem_toF]; simp [hb]) ht
    obtain ⟨hE, hPs⟩ := hP
    obtain ⟨l, s₅, h₇, h₈⟩ := okS_bind h₄
    have hL := lintTm_sound _ _ _ _ _ h₇
    rw [hE] at hL
    have hc : Closed (l.map toF) ∧ r'.2 = s₅ ∧ r'.1 = .yield PUnit.unit := by
      cases l with
      | none => cases okS_pure h₈; exact ⟨.inl rfl, rfl, rfl⟩
      | some rest =>
        simp only at h₈
        split at h₈
        · obtain ⟨_, _, hb, _⟩ := okS_bind h₈; exact (bad_not_ok hb).elim
        · rename_i he; simp at he
          cases okS_pure h₈
          exact ⟨.inr (by simp [toF_isEmpty he]), rfl, rfl⟩
    refine ⟨PUnit.unit, hc.2.2, ?_⟩
    rw [hc.2.1, List.map_append]
    exact hI.snoc ⟨_, _, hPs, hL, hc.1⟩
  rw [List.zipIdx_map_fst] at hF
  -- `main`.
  obtain ⟨l, s₂, h₃, h₄⟩ := okS_bind h₂
  have hL := lintTm_sound _ _ _ _ _ h₃
  rw [toF_empty] at hL
  refine ⟨_, _, _, hF, hL, ?_⟩
  cases l with
  | none => exact .inl rfl
  | some rest =>
    simp only at h₄
    split at h₄
    · exact (bad_not_ok h₄).elim
    · rename_i he; simp at he
      exact .inr (by simp [toF_isEmpty he])

end Backend2.Spike670
