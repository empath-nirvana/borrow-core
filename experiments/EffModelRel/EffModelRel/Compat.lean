import EffModelRel.Rel

/-!
# EffModelRel — compatibility of the model structure and of the folds

The operations of every computation type's model preserve the relation (`opA_rel`, ...), and so
do the folds: sequencing (`bindC_rel`), handling (`hnd_rel`), running against a comodel
(`runL_rel`) and destructor frames (`addFin_rel`). Each fold lemma is an induction on the tree
relation; its hypotheses about the fold's clauses are Kripke: they hold at every later world.
-/

namespace EffRel

variable {S : Sig}

/-! ## Unfolding the relations -/

theorem CRU_F {A : VTy S} {w : W} {t t' : (CTy.F A).den} :
    CRU (.F A) w t t' ↔ TreeRel (fun w a a' => VR A w a a') w t t' := by simp only [CRU]

theorem CRU_arr {A : VTy S} {C : CTy S} {w : W} {f f' : (CTy.arr A C).den} :
    CRU (.arr A C) w f f' ↔ ∀ w', w.le w' → ∀ a a', VR A w' a a' → CRU C w' (f a) (f' a') := by
  simp only [CRU]

theorem CRU_wth {C D : CTy S} {w : W} {p p' : (CTy.wth C D).den} :
    CRU (.wth C D) w p p' ↔ CRU C w p.1 p'.1 ∧ CRU D w p.2 p'.2 := by simp only [CRU]

theorem CRU_pi {e : S.E} {C : CTy S} {w : W} {f f' : (CTy.pi e C).den} :
    CRU (.pi e C) w f f' ↔ ∀ w', w.le w' → ∀ i i', w'.r i i' → CRU C w' (f i) (f' i') := by
  simp only [CRU]

theorem VR_g {g : G} {w : W} {a a' : (VTy.g (S := S) g).den} : VR (.g g) w a a' ↔ a = a' := by
  unfold VR; rfl

theorem VR_prod {A B : VTy S} {w : W} {a a' : (VTy.prod A B).den} :
    VR (.prod A B) w a a' ↔ VR A w a.1 a'.1 ∧ VR B w a.2 a'.2 := by simp only [VR]

theorem VR_inl {A B : VTy S} {w : W} {a a' : A.den} :
    VR (.sum A B) w (.inl a) (.inl a') ↔ VR A w a a' := by simp only [VR]

theorem VR_inr {A B : VTy S} {w : W} {b b' : B.den} :
    VR (.sum A B) w (.inr b) (.inr b') ↔ VR B w b b' := by simp only [VR]

theorem VR_inl_inr {A B : VTy S} {w : W} {a : A.den} {b : B.den} :
    ¬ VR (.sum A B) w (.inl a) (.inr b) := by simp only [VR]; exact id

theorem VR_inr_inl {A B : VTy S} {w : W} {a : A.den} {b : B.den} :
    ¬ VR (.sum A B) w (.inr b) (.inl a) := by simp only [VR]; exact id

theorem VR_U {m : Mode} {C : CTy S} {w : W} {c c' : C.den} :
    VR (.U m C) w c c' ↔ CRU C w.gcP c c' := by simp only [VR]

theorem VR_cap {e : S.E} {s : G} {w : W} {c c' : (VTy.cap (S := S) e s).den} :
    VR (.cap e s) w c c' ↔ w.r c.1 c'.1 ∧ ∀ w', w.gcP.le w' → ∀ o a st,
      TreeRel (fun _ x x' => x = x') w' (c.2 o a st) (c'.2 o a st) := by simp only [VR]

theorem VR_res {w : W} {x x' : (VTy.res (S := S)).den} :
    VR .res w x x' ↔ x.1 = x'.1 ∧ w.r x.2 x'.2 := by simp only [VR]

theorem VR_strm {A : VTy S} {w : W} {s s' : (VTy.strm A).den} :
    VR (.strm A) w s s' ↔ StrmRel (fun w a a' => VR A w a a') w.gcP s s' := by simp only [VR]

/-- On a world with nothing pending, a thunk's relation is its computation's. -/
theorem VR_U_noPend {m : Mode} {C : CTy S} {w : W} (hw : w.noPend) {c c' : C.den} :
    VR (.U m C) w c c' ↔ CRU C w c c' :=
  ⟨fun h => CRU.mono C (W.gcP_le w hw) (VR_U.1 h), fun h => VR_U.2 (CRU.mono C (W.le_gcP w hw) h)⟩

theorem W.sub.r' {w w' : W} (h : w.sub w') {a b : Nat} (hr : w.r a b) : w'.r a b :=
  W.gcP_r.1 (h.r _ _ (W.gcP_r.2 hr))

theorem W.le.noPend' {w w' : W} (h : w.le w') (hw : w.noPend) : w'.noPend := W.noPend_le hw h

/-! ## Every computation type's model preserves the relation -/

theorem opA_rel : (C : CTy S) → ∀ {w : W} {i i' : Nat} {e : S.E} {o : S.O e}
    {v : (S.arg e o).den} {k k' : (S.res e o).den → C.den} {d d' : List Dtor},
    w.noPend → w.r i i' → DR w d d' → (∀ y, CRU C w (k y) (k' y)) →
    CRU C w (C.opA i e o v k d) (C.opA i' e o v k' d')
  | .F _, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hk => by
      rw [CRU_F]; exact .op hp hi hd (fun y => CRU_F.1 (hk y))
  | .arr _ C, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact opA_rel C (hw.noPend' hp) (hw.r _ _ hi) (hd.mono hw.r)
        (fun y => CRU_arr.1 (hk y) w' hw a a' ha)
  | .wth C D, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hk => by
      rw [CRU_wth]
      exact ⟨opA_rel C hp hi hd (fun y => (CRU_wth.1 (hk y)).1),
        opA_rel D hp hi hd (fun y => (CRU_wth.1 (hk y)).2)⟩
  | .pi _ C, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      exact opA_rel C (hw.noPend' hp) (hw.r _ _ hi) (hd.mono hw.r)
        (fun y => CRU_pi.1 (hk y) w' hw j j' hj)

theorem abA_rel : (C : CTy S) → ∀ {w : W} {i i' : Nat} {e : S.E} {a : S.A e}
    {v : (S.aarg e a).den} {d d' : List Dtor},
    w.noPend → w.r i i' → DR w d d' → CRU C w (C.abA i e a v d) (C.abA i' e a v d')
  | .F _, _, _, _, _, _, _, _, _, hp, hi, hd => by rw [CRU_F]; exact .ab hp hi hd
  | .arr _ C, _, _, _, _, _, _, _, _, hp, hi, hd => by
      rw [CRU_arr]; intro w' hw _ _ _
      exact abA_rel C (hw.noPend' hp) (hw.r _ _ hi) (hd.mono hw.r)
  | .wth C D, _, _, _, _, _, _, _, _, hp, hi, hd => by
      rw [CRU_wth]; exact ⟨abA_rel C hp hi hd, abA_rel D hp hi hd⟩
  | .pi _ C, _, _, _, _, _, _, _, _, hp, hi, hd => by
      rw [CRU_pi]; intro w' hw _ _ _
      exact abA_rel C (hw.noPend' hp) (hw.r _ _ hi) (hd.mono hw.r)

theorem actA_rel : (C : CTy S) → ∀ {w : W} {g : G} {a a' : Act g} {k k' : g.den → C.den},
    AR w a a' → (∀ y, CRU C w (k y) (k' y)) → CRU C w (C.actA a k) (C.actA a' k')
  | .F _, _, _, _, _, _, _, ha, hk => by rw [CRU_F]; exact .act ha (fun y => CRU_F.1 (hk y))
  | .arr _ C, _, _, _, _, _, _, ha, hk => by
      rw [CRU_arr]; intro w' hw x x' hx
      exact actA_rel C (ha.mono hw.r) (fun y => CRU_arr.1 (hk y) w' hw x x' hx)
  | .wth C D, _, _, _, _, _, _, ha, hk => by
      rw [CRU_wth]
      exact ⟨actA_rel C ha (fun y => (CRU_wth.1 (hk y)).1),
        actA_rel D ha (fun y => (CRU_wth.1 (hk y)).2)⟩
  | .pi _ C, _, _, _, _, _, _, ha, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      exact actA_rel C (ha.mono hw.r) (fun y => CRU_pi.1 (hk y) w' hw j j' hj)

theorem nuA_both : (C : CTy S) → ∀ {w : W} {k k' : Nat → C.den},
    (∀ i i' (hi : w.sl i = .free) (hi' : w.sr i' = .free), CRU C (w.both i i' hi hi') (k i) (k' i')) →
    CRU C w (C.nuA k) (C.nuA k')
  | .F _, _, _, _, hk => by rw [CRU_F]; exact .nu (fun i i' hi hi' => CRU_F.1 (hk i i' hi hi'))
  | .arr A C, _, _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_both C (fun i i' hi hi' => CRU_arr.1 (hk i i' (hw.fl i hi) (hw.fr i' hi'))
        _ (W.le_both hw _ _ _ _) a a' (VR.mono A (W.sub_both _ _ _ _ _) ha))
  | .wth C D, _, _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_both C (fun i i' hi hi' => (CRU_wth.1 (hk i i' hi hi')).1),
        nuA_both D (fun i i' hi hi' => (CRU_wth.1 (hk i i' hi hi')).2)⟩
  | .pi _ C, _, _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      exact nuA_both C (fun i i' hi hi' => CRU_pi.1 (hk i i' (hw.fl i hi) (hw.fr i' hi'))
        _ (W.le_both hw _ _ _ _) j j' ((W.le_both_self _ _ _ _ _).r _ _ hj))

theorem nuA_L : (C : CTy S) → ∀ {w : W} {k : Nat → C.den} {c' : C.den},
    (∀ i (hi : w.sl i = .free), CRU C (w.pendL i hi) (k i) c') → CRU C w (C.nuA k) c'
  | .F _, _, _, _, hk => by rw [CRU_F]; exact .nuL (fun i hi => CRU_F.1 (hk i hi))
  | .arr A C, _, _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_L C (fun i hi => CRU_arr.1 (hk i (hw.fl i hi)) _ (W.le_pendL hw _ _) a a'
        (VR.mono A (W.sub_pendL _ _ _) ha))
  | .wth C D, _, _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_L C (fun i hi => (CRU_wth.1 (hk i hi)).1),
        nuA_L D (fun i hi => (CRU_wth.1 (hk i hi)).2)⟩
  | .pi _ C, _, _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      refine nuA_L C (fun i hi => CRU_pi.1 (hk i (hw.fl i hi)) _ (W.le_pendL hw _ _) j j' ?_)
      exact W.gcP_r.1 ((W.sub_pendL w' i hi).r _ _ (W.gcP_r.2 hj))

theorem nuA_R : (C : CTy S) → ∀ {w : W} {c : C.den} {k' : Nat → C.den},
    (∀ i' (hi' : w.sr i' = .free), CRU C (w.pendR i' hi') c (k' i')) → CRU C w c (C.nuA k')
  | .F _, _, _, _, hk => by rw [CRU_F]; exact .nuR (fun i hi => CRU_F.1 (hk i hi))
  | .arr A C, _, _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_R C (fun i hi => CRU_arr.1 (hk i (hw.fr i hi)) _ (W.le_pendR hw _ _) a a'
        (VR.mono A (W.sub_pendR _ _ _) ha))
  | .wth C D, _, _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_R C (fun i hi => (CRU_wth.1 (hk i hi)).1),
        nuA_R D (fun i hi => (CRU_wth.1 (hk i hi)).2)⟩
  | .pi _ C, _, _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      refine nuA_R C (fun i hi => CRU_pi.1 (hk i (hw.fr i hi)) _ (W.le_pendR hw _ _) j j' ?_)
      exact W.gcP_r.1 ((W.sub_pendR w' i hi).r _ _ (W.gcP_r.2 hj))

theorem nuA_gL : (C : CTy S) → ∀ {w : W} {k : Nat → C.den} {c' : C.den},
    (∀ i (hi : w.sl i = .free), CRU C (w.garbL i hi) (k i) c') → CRU C w (C.nuA k) c'
  | .F _, _, _, _, hk => by rw [CRU_F]; exact .gL (fun i hi => CRU_F.1 (hk i hi))
  | .arr A C, _, _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_gL C (fun i hi => CRU_arr.1 (hk i (hw.fl i hi)) _ (W.le_garbL hw _ _) a a'
        (VR.mono A (W.sub_garbL _ _ _) ha))
  | .wth C D, _, _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_gL C (fun i hi => (CRU_wth.1 (hk i hi)).1),
        nuA_gL D (fun i hi => (CRU_wth.1 (hk i hi)).2)⟩
  | .pi _ C, _, _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      refine nuA_gL C (fun i hi => CRU_pi.1 (hk i (hw.fl i hi)) _ (W.le_garbL hw _ _) j j' ?_)
      exact W.gcP_r.1 ((W.sub_garbL w' i hi).r _ _ (W.gcP_r.2 hj))

theorem nuA_gR : (C : CTy S) → ∀ {w : W} {c : C.den} {k' : Nat → C.den},
    (∀ i' (hi' : w.sr i' = .free), CRU C (w.garbR i' hi') c (k' i')) → CRU C w c (C.nuA k')
  | .F _, _, _, _, hk => by rw [CRU_F]; exact .gR (fun i hi => CRU_F.1 (hk i hi))
  | .arr A C, _, _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_gR C (fun i hi => CRU_arr.1 (hk i (hw.fr i hi)) _ (W.le_garbR hw _ _) a a'
        (VR.mono A (W.sub_garbR _ _ _) ha))
  | .wth C D, _, _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_gR C (fun i hi => (CRU_wth.1 (hk i hi)).1),
        nuA_gR D (fun i hi => (CRU_wth.1 (hk i hi)).2)⟩
  | .pi _ C, _, _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      refine nuA_gR C (fun i hi => CRU_pi.1 (hk i (hw.fr i hi)) _ (W.le_garbR hw _ _) j j' ?_)
      exact W.gcP_r.1 ((W.sub_garbR w' i hi).r _ _ (W.gcP_r.2 hj))

theorem nuA_mL : (C : CTy S) → ∀ {w : W} {i' : Nat} (hi' : w.sr i' = .p) {k : Nat → C.den}
    {c' : C.den}, (∀ i (hi : w.sl i = .free), CRU C (w.matchL i i' hi hi') (k i) c') →
    CRU C w (C.nuA k) c'
  | .F _, _, _, hi', _, _, hk => by rw [CRU_F]; exact .mL hi' (fun i hi => CRU_F.1 (hk i hi))
  | .arr A C, _, _, hi', _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_mL C (hw.pR hi') (fun i hi => CRU_arr.1 (hk i (hw.fl i hi)) _
        (W.le_matchL hw _ _ _ _) a a' (VR.mono A (W.sub_matchL _ _ _ _ _) ha))
  | .wth C D, _, _, hi', _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_mL C hi' (fun i hi => (CRU_wth.1 (hk i hi)).1),
        nuA_mL D hi' (fun i hi => (CRU_wth.1 (hk i hi)).2)⟩
  | .pi _ C, _, _, hi', _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      refine nuA_mL C (hw.pR hi') (fun i hi => CRU_pi.1 (hk i (hw.fl i hi)) _
        (W.le_matchL hw _ _ _ _) j j' ?_)
      exact W.gcP_r.1 ((W.sub_matchL w' _ _ _ _).r _ _ (W.gcP_r.2 hj))

theorem nuA_mR : (C : CTy S) → ∀ {w : W} {i : Nat} (hi : w.sl i = .p) {c : C.den}
    {k' : Nat → C.den}, (∀ i' (hi' : w.sr i' = .free), CRU C (w.matchR i' i hi' hi) c (k' i')) →
    CRU C w c (C.nuA k')
  | .F _, _, _, hi, _, _, hk => by rw [CRU_F]; exact .mR hi (fun i hi => CRU_F.1 (hk i hi))
  | .arr A C, _, _, hi, _, _, hk => by
      rw [CRU_arr]; intro w' hw a a' ha
      exact nuA_mR C (hw.pL hi) (fun i' hi' => CRU_arr.1 (hk i' (hw.fr i' hi')) _
        (W.le_matchR hw _ _ _ _) a a' (VR.mono A (W.sub_matchR _ _ _ _ _) ha))
  | .wth C D, _, _, hi, _, _, hk => by
      rw [CRU_wth]
      exact ⟨nuA_mR C hi (fun i hi' => (CRU_wth.1 (hk i hi')).1),
        nuA_mR D hi (fun i hi' => (CRU_wth.1 (hk i hi')).2)⟩
  | .pi _ C, _, _, hi, _, _, hk => by
      rw [CRU_pi]; intro w' hw j j' hj
      refine nuA_mR C (hw.pL hi) (fun i' hi' => CRU_pi.1 (hk i' (hw.fr i' hi')) _
        (W.le_matchR hw _ _ _ _) j j' ?_)
      exact W.gcP_r.1 ((W.sub_matchR w' _ _ _ _).r _ _ (W.gcP_r.2 hj))

theorem DtorR.act {w : W} {δ δ' : Dtor} : DtorR w δ δ' → AR w δ.act δ'.act
  | .free hr => .free hr
  | .wb hr => .wr hr

theorem dtorsA_rel (C : CTy S) {w : W} {d d' : List Dtor} (hd : DR w d d') {x x' : C.den}
    (hx : CRU C w x x') : CRU C w (C.dtorsA d x) (C.dtorsA d' x') := by
  induction hd with
  | nil => exact hx
  | cons hδ _ ih => exact actA_rel C hδ.act (fun _ => ih)

theorem dtors_rel {R : W → X → X → Prop} {w : W} {d d' : List Dtor} (hd : DR w d d')
    {t t' : Tree S X} (ht : TreeRel R w t t') : TreeRel R w (Tree.dtors d t) (Tree.dtors d' t') := by
  induction hd with
  | nil => exact ht
  | cons hδ _ ih => exact .act hδ.act (fun _ => ih)

/-! ## Destructors commute with the folds -/

theorem dtorsA_F {A : VTy S} (d : List Dtor) (x : (CTy.F A).den) :
    (CTy.F A).dtorsA d x = Tree.dtors d x := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [CTy.dtorsA, Tree.dtors, ih]; rfl

theorem dtorsA_append (C : CTy S) (d f : List Dtor) (x : C.den) :
    C.dtorsA (d ++ f) x = C.dtorsA d (C.dtorsA f x) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [List.cons_append, CTy.dtorsA, ih]

theorem Tree.dtors_append (d f : List Dtor) (t : Tree S X) :
    Tree.dtors (d ++ f) t = Tree.dtors d (Tree.dtors f t) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [List.cons_append, Tree.dtors, ih]

theorem bindC_dtors (C : CTy S) (d : List Dtor) (t : Tree S X) (f : X → C.den) :
    (Tree.dtors d t).bindC C f = C.dtorsA d (t.bindC C f) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [Tree.dtors, Tree.bindC, CTy.dtorsA, ih]

theorem bind_dtors (d : List Dtor) (t : Tree S X) (f : X → Tree S Y) :
    (Tree.dtors d t).bind f = Tree.dtors d (t.bind f) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [Tree.dtors, Tree.bind, ih]

theorem hnd_dtors (C : CTy S) (i : Nat) (e : S.E) (hr hop hab) (d : List Dtor) (t : Tree S X) :
    (Tree.dtors d t).hnd C i e hr hop hab = C.dtorsA d (t.hnd C i e hr hop hab) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [Tree.dtors, Tree.hnd, CTy.dtorsA, ih]

theorem runL_dtors (i : Nat) (e : S.E) (c : Nat) (sg : G) (co : CoSem S e sg) (s : sg.den)
    (d : List Dtor) (t : Tree S X) :
    (Tree.dtors d t).runL i e c sg co s = Tree.dtors d (t.runL i e c sg co s) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [Tree.dtors, Tree.runL, ih]

theorem addFin_dtors (ℓ r : Nat) (d : List Dtor) (t : Tree S X) :
    (Tree.dtors d t).addFin ℓ r = Tree.dtors d (t.addFin ℓ r) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [Tree.dtors, Tree.addFin, ih]

theorem dtorsA_arr {A : VTy S} {C : CTy S} (d : List Dtor) (g : (CTy.arr A C).den) :
    (CTy.arr A C).dtorsA d g = fun x => C.dtorsA d (g x) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [CTy.dtorsA, CTy.actA, ih]; rfl

theorem dtorsA_wth {C D : CTy S} (d : List Dtor) (g : (CTy.wth C D).den) :
    (CTy.wth C D).dtorsA d g = (C.dtorsA d g.1, D.dtorsA d g.2) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [CTy.dtorsA, CTy.actA, ih]; rfl

theorem dtorsA_pi {e : S.E} {C : CTy S} (d : List Dtor) (g : (CTy.pi e C).den) :
    (CTy.pi e C).dtorsA d g = fun x => C.dtorsA d (g x) := by
  induction d with
  | nil => rfl
  | cons δ d ih => simp only [CTy.dtorsA, CTy.actA, ih]; rfl

theorem abA_dtors_rel : (C : CTy S) → ∀ {w : W} {i i' : Nat} {e : S.E} {a : S.A e}
    {v : (S.aarg e a).den} {d d' f f' : List Dtor},
    w.noPend → w.r i i' → DR w d d' → DR w f f' →
    CRU C w (C.abA i e a v (d ++ f)) (C.dtorsA d' (C.abA i' e a v f'))
  | .F _, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hf => by
      rw [dtorsA_F]; exact CRU_F.2 (.abE hp hi hd hf)
  | .arr _ C, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hf => by
      rw [dtorsA_arr]
      refine CRU_arr.2 (fun w' hw _ _ _ => ?_)
      exact abA_dtors_rel C (hw.noPend' hp) (hw.r _ _ hi) (hd.mono hw.r) (hf.mono hw.r)
  | .wth C D, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hf => by
      rw [dtorsA_wth]
      exact CRU_wth.2 ⟨abA_dtors_rel C hp hi hd hf, abA_dtors_rel D hp hi hd hf⟩
  | .pi _ C, _, _, _, _, _, _, _, _, _, _, hp, hi, hd, hf => by
      rw [dtorsA_pi]
      refine CRU_pi.2 (fun w' hw _ _ _ => ?_)
      exact abA_dtors_rel C (hw.noPend' hp) (hw.r _ _ hi) (hd.mono hw.r) (hf.mono hw.r)

/-! ## The folds preserve the relation -/

theorem bindC_rel (C : CTy S) {R : W → X → X → Prop} {w : W} {t t' : Tree S X}
    (h : TreeRel R w t t') {f f' : X → C.den}
    (hf : ∀ w', w.sub w' → w'.noPend → ∀ x x', R w' x x' → CRU C w' (f x) (f' x')) :
    CRU C w (t.bindC C f) (t'.bindC C f') := by
  revert hf
  induction h with
  | ret hp hx => intro hf; exact hf _ (W.sub.refl _) hp _ _ hx
  | op hp hi hd _ ih => intro hf; exact opA_rel C hp hi hd (fun y => ih y hf)
  | ab hp hi hd => intro _; exact abA_rel C hp hi hd
  | abE hp hi hd hf =>
      intro _; simp only [Tree.bindC]; rw [bindC_dtors]; exact abA_dtors_rel C hp hi hd hf
  | act ha _ ih => intro hf; exact actA_rel C ha (fun y => ih y hf)
  | nu _ ih =>
      intro hf
      exact nuA_both C (fun i i' hi hi' => ih i i' hi hi'
        (fun w' h1 => hf w' (W.sub.trans (W.sub_both _ _ _ _ _) h1)))
  | nuL _ ih =>
      intro hf
      exact nuA_L C (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_pendL _ _ _) h1)))
  | nuR _ ih =>
      intro hf
      exact nuA_R C (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_pendR _ _ _) h1)))
  | gL _ ih =>
      intro hf
      exact nuA_gL C (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_garbL _ _ _) h1)))
  | gR _ ih =>
      intro hf
      exact nuA_gR C (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_garbR _ _ _) h1)))
  | mL hi' _ ih =>
      intro hf
      exact nuA_mL C hi' (fun i hi => ih i hi
        (fun w' h1 => hf w' (W.sub.trans (W.sub_matchL _ _ _ _ _) h1)))
  | mR hi _ ih =>
      intro hf
      exact nuA_mR C hi (fun i hi' => ih i hi'
        (fun w' h1 => hf w' (W.sub.trans (W.sub_matchR _ _ _ _ _) h1)))

theorem Tree.bind_rel {R1 : W → X → X → Prop} {R2 : W → Y → Y → Prop} {w : W}
    {t t' : Tree S X} (h : TreeRel R1 w t t') {f f' : X → Tree S Y}
    (hf : ∀ w', w.sub w' → w'.noPend → ∀ x x', R1 w' x x' → TreeRel R2 w' (f x) (f' x')) :
    TreeRel R2 w (t.bind f) (t'.bind f') := by
  revert hf
  induction h with
  | ret hp hx => intro hf; exact hf _ (W.sub.refl _) hp _ _ hx
  | op hp hi hd _ ih => intro hf; exact .op hp hi hd (fun y => ih y hf)
  | ab hp hi hd => intro _; exact .ab hp hi hd
  | abE hp hi hd hf => intro _; simp only [Tree.bind]; rw [bind_dtors]; exact .abE hp hi hd hf
  | act ha _ ih => intro hf; exact .act ha (fun y => ih y hf)
  | nu _ ih =>
      intro hf
      exact .nu (fun i i' hi hi' => ih i i' hi hi'
        (fun w' h1 => hf w' (W.sub.trans (W.sub_both _ _ _ _ _) h1)))
  | nuL _ ih =>
      intro hf
      exact .nuL (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_pendL _ _ _) h1)))
  | nuR _ ih =>
      intro hf
      exact .nuR (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_pendR _ _ _) h1)))
  | gL _ ih =>
      intro hf
      exact .gL (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_garbL _ _ _) h1)))
  | gR _ ih =>
      intro hf
      exact .gR (fun i hi => ih i hi (fun w' h1 => hf w' (W.sub.trans (W.sub_garbR _ _ _) h1)))
  | mL hi' _ ih =>
      intro hf
      exact .mL hi' (fun i hi => ih i hi
        (fun w' h1 => hf w' (W.sub.trans (W.sub_matchL _ _ _ _ _) h1)))
  | mR hi _ ih =>
      intro hf
      exact .mR hi (fun i hi' => ih i hi'
        (fun w' h1 => hf w' (W.sub.trans (W.sub_matchR _ _ _ _ _) h1)))

theorem catchOp_self {C : CTy S} (e : S.E) (hop) (o : S.O e) (v) (k : (S.res e o).den → C.den) (d)
    (fwd : C.den) : catchOp e hop e o v k d fwd = hop o v k d := by simp [catchOp]

theorem catchOp_ne {C : CTy S} {e e' : S.E} (h : e' ≠ e) (hop) (o : S.O e') (v)
    (k : (S.res e' o).den → C.den) (d) (fwd : C.den) : catchOp e hop e' o v k d fwd = fwd := by
  simp [catchOp, h]

theorem catchAb_self {C : CTy S} (e : S.E) (hab) (a : S.A e) (v) (d) (fwd : C.den) :
    catchAb e hab e a v d fwd = C.dtorsA d (hab a v) := by simp [catchAb]

theorem catchAb_ne {C : CTy S} {e e' : S.E} (h : e' ≠ e) (hab) (a : S.A e') (v) (d)
    (fwd : C.den) : catchAb e hab e' a v d fwd = fwd := by simp [catchAb, h]

theorem hnd_rel (C : CTy S) {R : W → X → X → Prop} {w : W} {t t' : Tree S X}
    (h : TreeRel R w t t') {i i' : Nat} {e : S.E} {hr hr' : X → C.den}
    {hop hop' : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → C.den) → List Dtor → C.den}
    {hab hab' : (a : S.A e) → (S.aarg e a).den → C.den}
    (hi : w.r i i')
    (hR : ∀ w', w.sub w' → w'.noPend → ∀ x x', R w' x x' → CRU C w' (hr x) (hr' x'))
    (hO : ∀ w', w.sub w' → w'.noPend → ∀ o v k k' d d', (∀ y, CRU C w' (k y) (k' y)) →
      DR w' d d' → CRU C w' (hop o v k d) (hop' o v k' d'))
    (hA : ∀ w', w.sub w' → w'.noPend → ∀ a v, CRU C w' (hab a v) (hab' a v)) :
    CRU C w (t.hnd C i e hr hop hab) (t'.hnd C i' e hr' hop' hab') := by
  revert hi hR hO hA
  induction h with
  | ret hp hx => intro _ hR _ _; exact hR _ (W.sub.refl _) hp _ _ hx
  | @op w j j' e' o v k k' d d' hp hj hd _ ih =>
      intro hi hR hO hA
      have kk := fun y => ih y hi hR hO hA
      simp only [Tree.hnd]
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [catchOp_self, catchOp_self]
          exact hO _ (W.sub.refl _) hp o v _ _ d d' kk hd
        · rw [catchOp_ne he, catchOp_ne he]; exact opA_rel C hp hj hd kk
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']
        exact opA_rel C hp hj hd kk
  | @ab w j j' e' a v d d' hp hj hd =>
      intro hi _ _ hA
      simp only [Tree.hnd]
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [catchAb_self, catchAb_self]
          exact dtorsA_rel C hd (hA _ (W.sub.refl _) hp a v)
        · rw [catchAb_ne he, catchAb_ne he]; exact abA_rel C hp hj hd
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']
        exact abA_rel C hp hj hd
  | @abE w j j' e' a v d d' f f' hp hj hd hf =>
      intro hi _ _ hA
      rw [hnd_dtors]
      simp only [Tree.hnd]
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [catchAb_self, catchAb_self, dtorsA_append]
          exact dtorsA_rel C hd (dtorsA_rel C hf (hA _ (W.sub.refl _) hp a v))
        · rw [catchAb_ne he, catchAb_ne he]; exact abA_dtors_rel C hp hj hd hf
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']
        exact abA_dtors_rel C hp hj hd hf
  | act ha _ ih =>
      intro hi hR hO hA; exact actA_rel C ha (fun y => ih y hi hR hO hA)
  | nu _ ih =>
      intro hi hR hO hA
      have hs := W.sub_both
      exact nuA_both C (fun j j' hj hj' => ih j j' hj hj'
        ((hs _ _ _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _ _ _) h1)))
  | nuL _ ih =>
      intro hi hR hO hA
      have hs := W.sub_pendL
      exact nuA_L C (fun j hj => ih j hj ((hs _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _) h1)))
  | nuR _ ih =>
      intro hi hR hO hA
      have hs := W.sub_pendR
      exact nuA_R C (fun j hj => ih j hj ((hs _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _) h1)))
  | gL _ ih =>
      intro hi hR hO hA
      have hs := W.sub_garbL
      exact nuA_gL C (fun j hj => ih j hj ((hs _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _) h1)))
  | gR _ ih =>
      intro hi hR hO hA
      have hs := W.sub_garbR
      exact nuA_gR C (fun j hj => ih j hj ((hs _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _) h1)))
  | mL hi' _ ih =>
      intro hi hR hO hA
      have hs := W.sub_matchL
      exact nuA_mL C hi' (fun j hj => ih j hj ((hs _ _ _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _ _ _) h1)))
  | mR hi₀ _ ih =>
      intro hi hR hO hA
      have hs := W.sub_matchR
      exact nuA_mR C hi₀ (fun j hj => ih j hj ((hs _ _ _ _ _).r' hi)
        (fun w' h1 => hR w' (W.sub.trans (hs _ _ _ _ _) h1))
        (fun w' h1 => hO w' (W.sub.trans (hs _ _ _ _ _) h1))
        (fun w' h1 => hA w' (W.sub.trans (hs _ _ _ _ _) h1)))

theorem addFin_rel {R : W → X → X → Prop} {w : W} {t t' : Tree S X} (h : TreeRel R w t t')
    {ℓ r r' : Nat} (hr : w.r r r') : TreeRel R w (t.addFin ℓ r) (t'.addFin ℓ r') := by
  revert hr
  induction h with
  | ret hp hx => intro hr; exact .act (.free hr) (fun _ => .ret hp hx)
  | op hp hi hd _ ih =>
      intro hr; exact .op hp hi (hd.append (.cons (.free hr) .nil)) (fun y => ih y hr)
  | ab hp hi hd => intro hr; exact .ab hp hi (hd.append (.cons (.free hr) .nil))
  | abE hp hi hd hf =>
      intro hr
      simp only [Tree.addFin]; rw [addFin_dtors]; simp only [Tree.addFin]
      rw [List.append_assoc]
      exact .abE hp hi hd (hf.append (.cons (.free hr) .nil))
  | act ha _ ih => intro hr; exact .act ha (fun y => ih y hr)
  | nu _ ih => intro hr; exact .nu (fun i i' hi hi' => ih i i' hi hi' ((W.sub_both _ _ _ _ _).r' hr))
  | nuL _ ih => intro hr; exact .nuL (fun i hi => ih i hi ((W.sub_pendL _ _ _).r' hr))
  | nuR _ ih => intro hr; exact .nuR (fun i hi => ih i hi ((W.sub_pendR _ _ _).r' hr))
  | gL _ ih => intro hr; exact .gL (fun i hi => ih i hi ((W.sub_garbL _ _ _).r' hr))
  | gR _ ih => intro hr; exact .gR (fun i hi => ih i hi ((W.sub_garbR _ _ _).r' hr))
  | mL hi' _ ih => intro hr; exact .mL hi' (fun i hi => ih i hi ((W.sub_matchL _ _ _ _ _).r' hr))
  | mR hi _ ih => intro hr; exact .mR hi (fun i hi' => ih i hi' ((W.sub_matchR _ _ _ _ _).r' hr))

theorem coStep_self (e : S.E) (sg : G) (co : CoSem S e sg) (c : Nat) (s : sg.den) (d : List Dtor)
    (o : S.O e) (v) (rk : (S.res e o).den → sg.den → Tree S (X ⊕ Int)) (fwd) :
    coStep e sg co c s d e o v rk fwd = (co o v s).bind (coK sg c d rk) := by
  simp only [coStep, dite_true]

theorem coStep_ne {e e' : S.E} (h : e' ≠ e) (sg : G) (co : CoSem S e sg) (c : Nat) (s : sg.den)
    (d : List Dtor) (o : S.O e') (v) (rk : (S.res e' o).den → sg.den → Tree S (X ⊕ Int)) (fwd) :
    coStep e sg co c s d e' o v rk fwd = fwd := by
  simp [coStep, h]

/-- A lend preserves the relation: the client's trees related, the cells and instances matched,
the co-operations related at every later world. -/
theorem runL_rel {R : W → X → X → Prop} {R2 : W → (X ⊕ Int) → (X ⊕ Int) → Prop}
    (hR2 : ∀ w w' x x', w.le w' → R2 w x x' → R2 w' x x')
    (hinl : ∀ w x x', R w x x' → R2 w (.inl x) (.inl x')) (hinr : ∀ w n, R2 w (.inr n) (.inr n))
    {w : W} {t t' : Tree S X} (h : TreeRel R w t t') {i i' c c' : Nat} {e : S.E} {sg : G}
    {co co' : CoSem S e sg} (hi : w.r i i') (hc : w.r c c')
    (hco : ∀ w', w.sub w' → w'.noPend → ∀ o a st,
      TreeRel (fun _ x x' => x = x') w' (co o a st) (co' o a st)) :
    ∀ s, TreeRel R2 w (t.runL i e c sg co s) (t'.runL i' e c' sg co' s) := by
  revert hi hc hco
  induction h with
  | ret hp hx => intro _ hc _ s; exact .act (.wr hc) (fun _ => .ret hp (hinl _ _ _ hx))
  | @op w j j' e' o v k k' d d' hp hj hd _ ih =>
      intro hi hc hco s
      simp only [Tree.runL]
      have fwdR : TreeRel R2 w
          (Tree.op j e' o v (fun y => (k y).runL i e c sg co s) (d ++ [.wb c ⟨sg, s⟩]))
          (Tree.op j' e' o v (fun y => (k' y).runL i' e c' sg co' s) (d' ++ [.wb c' ⟨sg, s⟩])) :=
        .op hp hj (hd.append (.cons (.wb hc) .nil)) (fun y => ih y hi hc hco s)
      by_cases hji : j = i
      · have hji' : j' = i' := (w.r_iff hi hj).1 hji
        rw [if_pos hji, if_pos hji']
        by_cases he : e' = e
        · subst he
          rw [coStep_self, coStep_self]
          apply Tree.bind_rel (hco w (W.sub.refl _) hp o v s)
          intro w₂ h₂ hp₂ x x' hx
          subst hx
          have hle : w.le w₂ := W.noPend_le_of_sub hp hp₂ h₂
          rcases x with ⟨y, s'⟩ | ⟨nn, s'⟩
          · simp only [coK]
            exact (ih y hi hc hco s').mono hR2 w₂ hle
          · simp only [coK]
            exact dtors_rel (hd.mono hle.r) (.act (.wr (hle.r _ _ hc))
              (fun _ => .ret hp₂ (hinr _ _)))
        · rw [coStep_ne he, coStep_ne he]; exact fwdR
      · have hji' : ¬ j' = i' := fun h' => hji ((w.r_iff hi hj).2 h')
        rw [if_neg hji, if_neg hji']; exact fwdR
  | ab hp hj hd =>
      intro _ hc _ s
      exact .ab hp hj (hd.append (.cons (.wb hc) .nil))
  | abE hp hj hd hf =>
      intro _ hc _ s
      simp only [Tree.runL]; rw [runL_dtors]; simp only [Tree.runL]
      rw [List.append_assoc]
      exact .abE hp hj hd (hf.append (.cons (.wb hc) .nil))
  | act ha _ ih => intro hi hc hco s; exact .act ha (fun y => ih y hi hc hco s)
  | nu _ ih =>
      intro hi hc hco s
      have hs := W.sub_both
      exact .nu (fun j j' hj hj' => ih j j' hj hj' ((hs _ _ _ _ _).r' hi) ((hs _ _ _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _ _ _) h1)) s)
  | nuL _ ih =>
      intro hi hc hco s
      have hs := W.sub_pendL
      exact .nuL (fun j hj => ih j hj ((hs _ _ _).r' hi) ((hs _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _) h1)) s)
  | nuR _ ih =>
      intro hi hc hco s
      have hs := W.sub_pendR
      exact .nuR (fun j hj => ih j hj ((hs _ _ _).r' hi) ((hs _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _) h1)) s)
  | gL _ ih =>
      intro hi hc hco s
      have hs := W.sub_garbL
      exact .gL (fun j hj => ih j hj ((hs _ _ _).r' hi) ((hs _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _) h1)) s)
  | gR _ ih =>
      intro hi hc hco s
      have hs := W.sub_garbR
      exact .gR (fun j hj => ih j hj ((hs _ _ _).r' hi) ((hs _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _) h1)) s)
  | mL hi' _ ih =>
      intro hi hc hco s
      have hs := W.sub_matchL
      exact .mL hi' (fun j hj => ih j hj ((hs _ _ _ _ _).r' hi) ((hs _ _ _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _ _ _) h1)) s)
  | mR hi₀ _ ih =>
      intro hi hc hco s
      have hs := W.sub_matchR
      exact .mR hi₀ (fun j hj => ih j hj ((hs _ _ _ _ _).r' hi) ((hs _ _ _ _ _).r' hc)
        (fun w' h1 => hco w' (W.sub.trans (hs _ _ _ _ _) h1)) s)

end EffRel
