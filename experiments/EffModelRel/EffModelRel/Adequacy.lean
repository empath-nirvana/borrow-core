import EffModelRel.Fundamental

/-!
# EffModelRel — adequacy and soundness for contextual equivalence

Related trees, run against worlds that agree with the relation (`Inv`), make the same
observation (`adequacy`). With the fundamental property this gives **soundness**: logically
related terms are contextually equivalent (`soundness`).

`Inv` says the two runs have allocated exactly the names the world has allocated, the matched
cells hold the same contents, every other cell is empty, and the traces agree.
-/

namespace EffRel

variable {S : Sig}

structure Inv (w : W) (wl wr : Wd) : Prop where
  nl : ∀ a, w.sl a = .free ↔ wl.next ≤ a
  nr : ∀ b, w.sr b = .free ↔ wr.next ≤ b
  st : ∀ a b, w.r a b → wl.store a = wr.store b
  sl : ∀ a, (∀ b, ¬ w.r a b) → wl.store a = none
  sr : ∀ b, (∀ a, ¬ w.r a b) → wr.store b = none
  tr : wl.trace = wr.trace

theorem Inv.init : Inv W.init Wd.init Wd.init :=
  ⟨fun a => by simp [W.init, Wd.init], fun b => by simp [W.init, Wd.init],
   fun _ _ h => by simp [W.r, W.init] at h, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Inv.emit {w : W} {wl wr : Wd} (h : Inv w wl wr) (e : Ev) : Inv w (wl.emit e) (wr.emit e) :=
  ⟨h.nl, h.nr, h.st, h.sl, h.sr, by simp [Wd.emit, h.tr]⟩

theorem Inv.set {w : W} {wl wr : Wd} (h : Inv w wl wr) {c c' : Nat} (hc : w.r c c')
    (v : Option GVal) : Inv w (wl.set c v) (wr.set c' v) := by
  refine ⟨h.nl, h.nr, fun a b hab => ?_, fun a ha => ?_, fun b hb => ?_, h.tr⟩
  · simp only [Wd.set]
    by_cases hac : a = c
    · subst hac; have := w.fn hab hc; subst this; simp
    · have hbc : b ≠ c' := fun hbc => hac (w.inj hab (hbc ▸ hc))
      simp [hac, hbc, h.st a b hab]
  · simp only [Wd.set]
    have hac : a ≠ c := fun hac => ha c' (hac ▸ hc)
    simp [hac, h.sl a ha]
  · simp only [Wd.set]
    have hbc : b ≠ c' := fun hbc => hb c (hbc ▸ hc)
    simp [hbc, h.sr b hb]

theorem Inv.get {w : W} {wl wr : Wd} (h : Inv w wl wr) {c c' : Nat} (hc : w.r c c') (g : G) :
    wl.get c g = wr.get c' g := by
  simp only [Wd.get, h.st c c' hc]

/-- Related actions, run in agreeing worlds, both fail or both answer the same. -/
theorem AR.exec_rel {w : W} {g : G} {a a' : Act g} (ha : AR w a a') {wl wr : Wd}
    (hI : Inv w wl wr) : (a.exec wl = none ∧ a'.exec wr = none) ∨
      ∃ y wl' wr', a.exec wl = some (y, wl') ∧ a'.exec wr = some (y, wr') ∧ Inv w wl' wr' := by
  cases ha with
  | out => exact .inr ⟨(), _, _, rfl, rfl, hI.emit _⟩
  | acq _ => exact .inr ⟨(), _, _, rfl, rfl, hI.emit _⟩
  | use _ => exact .inr ⟨(), _, _, rfl, rfl, hI.emit _⟩
  | free _ => exact .inr ⟨(), _, _, rfl, rfl, hI.emit _⟩
  | new hc => exact .inr ⟨(), _, _, rfl, rfl, (hI.set hc _).emit _⟩
  | @rd c c' g hc =>
      simp only [Act.exec, hI.get hc g]
      cases wr.get c' g with
      | none => exact .inl ⟨rfl, rfl⟩
      | some v => exact .inr ⟨v, wl, wr, rfl, rfl, hI⟩
  | @wr c c' s hc =>
      simp only [Act.exec, hI.st c c' hc]
      cases wr.store c' with
      | none => exact .inl ⟨rfl, rfl⟩
      | some _ => exact .inr ⟨(), _, _, rfl, rfl, hI.set hc _⟩
  | @kill c c' g hc =>
      simp only [Act.exec, hI.get hc g]
      cases wr.get c' g with
      | none => exact .inl ⟨rfl, rfl⟩
      | some v => exact .inr ⟨v, _, _, rfl, rfl, (hI.set hc _).emit _⟩

theorem DR.unwind_rel {w : W} {d d' : List Dtor} (hd : DR w d d') {wl wr : Wd}
    (hI : Inv w wl wr) : wl.unwind d = wr.unwind d' := by
  induction hd generalizing wl wr with
  | nil => simp only [Wd.unwind, hI.tr]
  | cons hδ _ ih =>
      simp only [Wd.unwind]
      rcases hδ.act.exec_rel hI with ⟨h1, h2⟩ | ⟨y, wl', wr', h1, h2, hI'⟩
      · simp only [h1, h2, hI.tr]
      · simp only [h1, h2]; exact ih hI'

theorem obs_dtors_ab (render : X → GV) (d : List Dtor) (i : Nat) (e : S.E) (a : S.A e) (v) (f)
    (w : Wd) : (Tree.dtors d (Tree.ab (X := X) i e a v f)).obs render w = w.unwind (d ++ f) := by
  induction d generalizing w with
  | nil => rfl
  | cons δ d ih =>
      simp only [Tree.dtors, Tree.obs, List.cons_append, Wd.unwind]
      cases δ.act.exec w with
      | none => rfl
      | some p => exact ih p.2

theorem Inv.alloc_free {w : W} {wl wr : Wd} (h : Inv w wl wr) : w.sl wl.next = .free :=
  (h.nl _).2 (Nat.le_refl _)

theorem Inv.alloc_freeR {w : W} {wl wr : Wd} (h : Inv w wl wr) : w.sr wr.next = .free :=
  (h.nr _).2 (Nat.le_refl _)

theorem Inv.store_l {w : W} {wl wr : Wd} (h : Inv w wl wr) {a : Nat} (ha : ∀ b, w.sl a ≠ .m b) :
    wl.store a = none := h.sl a (fun b hb => ha b hb)

theorem Inv.store_r {w : W} {wl wr : Wd} (h : Inv w wl wr) {b : Nat} (hb : ∀ a, w.sr b ≠ .m a) :
    wr.store b = none := h.sr b (fun a ha => hb a (w.r_sr ha))

theorem nl_upd {f : Nat → St} {n : Nat} (hf : ∀ a, f a = .free ↔ n ≤ a) {i : Nat} {s : St}
    (hs : s ≠ .free) {n' : Nat} (hc : (i = n ∧ n' = n + 1) ∨ (f i ≠ .free ∧ n' = n)) :
    ∀ a, upd f i s a = .free ↔ n' ≤ a := by
  intro a
  by_cases ha : a = i
  · subst ha; rw [upd_same]
    refine ⟨fun h => absurd h hs, fun h => ?_⟩
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · exact absurd ((hf a).2 (by omega)) h1
  · rw [upd_ne _ _ ha, hf]
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · subst h2; exact Iff.rfl

theorem Inv.link' {w : W} {wl wr : Wd} (h : Inv w wl wr) {i i' : Nat} (h1 h2) {nL nR : Nat}
    (hnl : ∀ a, (w.link i i' h1 h2).sl a = .free ↔ nL ≤ a)
    (hnr : ∀ b, (w.link i i' h1 h2).sr b = .free ↔ nR ≤ b) :
    Inv (w.link i i' h1 h2) { wl with next := nL } { wr with next := nR } := by
  refine ⟨hnl, hnr, fun a b hab => ?_, fun a ha => ?_, fun b hb => ?_, h.tr⟩
  · rcases W.link_r.1 hab with ⟨ha, hb⟩ | ⟨_, hab⟩
    · subst ha; subst hb; simp only; rw [h.store_l h1, h.store_r h2]
    · exact h.st a b hab
  · exact h.sl a (fun b hb => by
      have : a ≠ i := fun hai => h1 b (hai ▸ hb)
      exact ha b (W.link_r.2 (.inr ⟨this, hb⟩)))
  · exact h.sr b (fun a hab => by
      have hai : a ≠ i := fun hai => h1 b (hai ▸ hab)
      exact hb a (W.link_r.2 (.inr ⟨hai, hab⟩)))

theorem W.setL_r {w : W} {i : Nat} {s : St} {hs h1} {a b : Nat} :
    (w.setL i s hs h1).r a b ↔ w.r a b := by
  unfold setL r; simp only
  by_cases ha : a = i
  · subst ha; rw [upd_same]; exact ⟨fun h => absurd h (hs b), fun h => absurd h (h1 b)⟩
  · rw [upd_ne _ _ ha]

theorem W.setR_r {w : W} {i : Nat} {s : St} {hs h1} {a b : Nat} :
    (w.setR i s hs h1).r a b ↔ w.r a b := by
  constructor
  · intro h; apply (w.coh a b).2
    have := (W.coh _ a b).1 h
    unfold setR at this; simp only at this
    by_cases hb : b = i
    · subst hb; rw [upd_same] at this; exact absurd this (hs a)
    · rw [upd_ne _ _ hb] at this; exact this
  · intro h; apply (W.coh _ a b).2
    unfold setR; simp only
    have := (w.coh a b).1 h
    by_cases hb : b = i
    · subst hb; exact absurd this (h1 a)
    · rw [upd_ne _ _ hb]; exact this

theorem Inv.setL' {w : W} {wl wr : Wd} (h : Inv w wl wr) {i : Nat} {s : St} (hs h1) {nL : Nat}
    (hnl : ∀ a, (w.setL i s hs h1).sl a = .free ↔ nL ≤ a) :
    Inv (w.setL i s hs h1) { wl with next := nL } wr :=
  ⟨hnl, h.nr, fun a b hab => h.st a b (W.setL_r.1 hab),
   fun a ha => h.sl a (fun b hb => ha b (W.setL_r.2 hb)),
   fun b hb => h.sr b (fun a ha => hb a (W.setL_r.2 ha)), h.tr⟩

theorem Inv.setR' {w : W} {wl wr : Wd} (h : Inv w wl wr) {i : Nat} {s : St} (hs h1) {nR : Nat}
    (hnr : ∀ b, (w.setR i s hs h1).sr b = .free ↔ nR ≤ b) :
    Inv (w.setR i s hs h1) wl { wr with next := nR } :=
  ⟨h.nl, hnr, fun a b hab => h.st a b (W.setR_r.1 hab),
   fun a ha => h.sl a (fun b hb => ha b (W.setR_r.2 hb)),
   fun b hb => h.sr b (fun a ha => hb a (W.setR_r.2 ha)), h.tr⟩

/-- **Adequacy.** Related trees make the same observation. -/
theorem adequacy {R : W → X → X → Prop} {render render' : X → GV}
    (hR : ∀ w x x', w.noPend → R w x x' → render x = render' x')
    {w : W} {t t' : Tree S X} (h : TreeRel R w t t') :
    ∀ {wl wr : Wd}, Inv w wl wr → t.obs render wl = t'.obs render' wr := by
  induction h with
  | ret hp hx => intro wl wr hI; simp only [Tree.obs, hR _ _ _ hp hx, hI.tr]
  | op _ _ hd _ _ => intro wl wr hI; exact hd.unwind_rel hI
  | ab _ _ hd => intro wl wr hI; exact hd.unwind_rel hI
  | abE _ _ hd hf =>
      intro wl wr hI
      rw [obs_dtors_ab]
      exact (hd.append hf).unwind_rel hI
  | act ha _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      rcases ha.exec_rel hI with ⟨h1, h2⟩ | ⟨y, wl', wr', h1, h2, hI'⟩
      · simp only [h1, h2, hI.tr]
      · simp only [h1, h2]; exact ih y hI'
  | nu _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      exact ih _ _ hI.alloc_free hI.alloc_freeR (hI.link' _ _
        (nl_upd hI.nl St.noConfusion (.inl ⟨rfl, rfl⟩))
        (nl_upd hI.nr St.noConfusion (.inl ⟨rfl, rfl⟩)))
  | nuL _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      exact ih _ hI.alloc_free (hI.setL' _ _ (nl_upd hI.nl St.noConfusion (.inl ⟨rfl, rfl⟩)))
  | nuR _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      exact ih _ hI.alloc_freeR (hI.setR' _ _ (nl_upd hI.nr St.noConfusion (.inl ⟨rfl, rfl⟩)))
  | gL _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      exact ih _ hI.alloc_free (hI.setL' _ _ (nl_upd hI.nl St.noConfusion (.inl ⟨rfl, rfl⟩)))
  | gR _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      exact ih _ hI.alloc_freeR (hI.setR' _ _ (nl_upd hI.nr St.noConfusion (.inl ⟨rfl, rfl⟩)))
  | mL hi' _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      have := hI.link' (W.free_nm hI.alloc_free) (W.p_nmR hi') (nR := wr.next)
        (nl_upd hI.nl St.noConfusion (.inl ⟨rfl, rfl⟩))
        (nl_upd hI.nr St.noConfusion (.inr ⟨by rw [hi']; exact St.noConfusion, rfl⟩))
      exact ih _ hI.alloc_free this
  | mR hi _ ih =>
      intro wl wr hI
      simp only [Tree.obs]
      have := hI.link' (W.p_nm hi) (W.free_nmR hI.alloc_freeR) (nL := wl.next)
        (nl_upd hI.nl St.noConfusion (.inr ⟨by rw [hi]; exact St.noConfusion, rfl⟩))
        (nl_upd hI.nr St.noConfusion (.inl ⟨rfl, rfl⟩))
      exact ih _ hI.alloc_freeR this

/-! ## Soundness for contextual equivalence -/

theorem curryE_rel : (Γ : List (VTy S)) → ∀ {C : CTy S} {w : W} {f f' : Env Γ → C.den},
    (∀ w', w.le w' → ∀ ρ ρ', ER w' ρ ρ' → CRU C w' (f ρ) (f' ρ')) →
    CRU (arrs Γ C) w (curryE Γ f) (curryE Γ f')
  | [], _, w, _, _, hf => hf w (W.le.refl w) _ _ (ER.nil w)
  | A :: Γ, _, _, _, _, hf => by
      refine CRU_arr.2 (fun w' hle a a' ha => curryE_rel Γ (fun w'' h2 ρ ρ' hρ => ?_))
      exact hf w'' (hle.trans h2) _ _ (ER.cons hρ (VR.mono A h2.sub ha))

theorem curryI_rel : (Ψ : List S.E) → ∀ {D : CTy S} {w : W} {f f' : IEnv Ψ → D.den},
    (∀ w', w.le w' → ∀ η η', IR w' η η' → CRU D w' (f η) (f' η')) →
    CRU (pis Ψ D) w (curryI Ψ f) (curryI Ψ f')
  | [], _, w, _, _, hf => hf w (W.le.refl w) _ _ (IR.nil w)
  | e :: Ψ, _, _, _, _, hf => by
      refine CRU_pi.2 (fun w' hle i i' hi => curryI_rel Ψ (fun w'' h2 η η' hη => ?_))
      exact hf w'' (hle.trans h2) _ _ (IR.cons hη (h2.r _ _ hi) e)

/-- The closures of logically related terms are related. -/
theorem close_rel {M N : Cmp S Ψ Γ C} (h : LR M N) {w : W} (hw : w.noPend) :
    CRU (holeTy Ψ Γ C) w (close M.den) (close N.den) :=
  curryI_rel Ψ (fun w' hle η η' hη => curryE_rel Γ (fun w'' h2 ρ ρ' hρ =>
    h w'' ((hle.trans h2).noPend' hw) η η' ρ ρ' (hη.mono h2.r) hρ))

/-- **Soundness.** Logically related terms are contextually equivalent. -/
theorem soundness {M N : Cmp S Ψ Γ C} (h : LR M N) : CtxEq M N := by
  intro g P
  unfold Context.obs
  have hc : VR (.U Mode.unr (holeTy Ψ Γ C)) W.init (close M.den) (close N.den) :=
    (VR_U_noPend W.init_noPend).2 (close_rel h W.init_noPend)
  have hP := Cmp.fp P W.init_noPend (IR.nil _) (ER.cons (ER.nil _) hc)
  exact adequacy (fun _ x x' _ hx => by rw [VR_g.1 hx]) (CRU_F.1 hP) Inv.init

/-- Terms with the same denotation are logically related. -/
theorem LR.of_den {M N : Cmp S Ψ Γ C} (h : ∀ η ρ, M.den η ρ = N.den η ρ) : LR M N := by
  intro w hw η η' ρ ρ' hη hρ
  rw [← h η' ρ']; exact Cmp.fp M hw hη hρ

theorem CtxEq.of_den {M N : Cmp S Ψ Γ C} (h : ∀ η ρ, M.den η ρ = N.den η ρ) : CtxEq M N :=
  soundness (LR.of_den h)

theorem CtxEq.refl (M : Cmp S Ψ Γ C) : CtxEq M M := fun _ _ => rfl

theorem CtxEq.symm {M N : Cmp S Ψ Γ C} (h : CtxEq M N) : CtxEq N M := fun g P => (h g P).symm

theorem CtxEq.trans {M N L : Cmp S Ψ Γ C} (h₁ : CtxEq M N) (h₂ : CtxEq N L) : CtxEq M L :=
  fun g P => (h₁ g P).trans (h₂ g P)

end EffRel
