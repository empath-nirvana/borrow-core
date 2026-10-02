import EffModelRel.World

/-!
# EffModelRel — the binary logical relation

Two trees are related at a world when they have the same shape up to the world's matching of
names (`TreeRel`). Allocation is the one place the shapes may differ: a side may allocate a name
the other never does (`gL`, `gR`), or the two may allocate in a different order and match the
names later (`nuL`, `mR`, ...). Every name must be matched before anything else happens to it:
the leaves and the operations need a world with nothing pending.

There is **no step index**. Trees are finite (the language has no unbounded recursion), so
`TreeRel` is an inductive relation, and the value relation is defined by recursion on types. The
recursive stream type is the one place a type mentions itself; its relation is the least
relation closed under one unfolding (`StrmRel`), which exists because the stream occurs
positively, under `U` and `F`.
-/

namespace EffRel

variable {S : Sig}

inductive AR (w : W) : {g : G} → Act g → Act g → Prop where
  | out : AR w (.out n) (.out n)
  | acq : w.r r r' → AR w (.acq ℓ r) (.acq ℓ r')
  | use : w.r r r' → AR w (.use ℓ r) (.use ℓ r')
  | free : w.r r r' → AR w (.free ℓ r) (.free ℓ r')
  | new : w.r c c' → AR w (.new c s) (.new c' s)
  | rd : w.r c c' → AR w (.rd c g) (.rd c' g)
  | wr : w.r c c' → AR w (.wr c s) (.wr c' s)
  | kill : w.r c c' → AR w (.kill c g) (.kill c' g)

inductive DtorR (w : W) : Dtor → Dtor → Prop where
  | free : w.r r r' → DtorR w (.free ℓ r) (.free ℓ r')
  | wb : w.r c c' → DtorR w (.wb c s) (.wb c' s)

inductive DR (w : W) : List Dtor → List Dtor → Prop where
  | nil : DR w [] []
  | cons : DtorR w δ δ' → DR w d d' → DR w (δ :: d) (δ' :: d')

inductive TreeRel (R : W → X → X → Prop) : W → Tree S X → Tree S X → Prop where
  | ret : w.noPend → R w x x' → TreeRel R w (.ret x) (.ret x')
  | op {i i' : Nat} {e : S.E} {o : S.O e} {v : (S.arg e o).den}
      {k k' : (S.res e o).den → Tree S X} {d d' : List Dtor} :
      w.noPend → w.r i i' → DR w d d' → (∀ y, TreeRel R w (k y) (k' y)) →
      TreeRel R w (.op i e o v k d) (.op i' e o v k' d')
  | ab {i i' : Nat} {e : S.E} {a : S.A e} {v : (S.aarg e a).den} {d d' : List Dtor} :
      w.noPend → w.r i i' → DR w d d' → TreeRel R w (.ab i e a v d) (.ab i' e a v d')
  /-- An abort carrying destructors is related to running some of them first: the destructor
  form of algebraicity at arity 0. -/
  | abE {i i' : Nat} {e : S.E} {a : S.A e} {v : (S.aarg e a).den} {d d' f f' : List Dtor} :
      w.noPend → w.r i i' → DR w d d' → DR w f f' →
      TreeRel R w (.ab i e a v (d ++ f)) (Tree.dtors d' (.ab i' e a v f'))
  | act {g : G} {a a' : Act g} {k k' : g.den → Tree S X} : AR w a a' →
      (∀ y, TreeRel R w (k y) (k' y)) → TreeRel R w (.act a k) (.act a' k')
  /-- Both sides allocate; the names are matched. -/
  | nu {k k' : Nat → Tree S X} : (∀ i i' (hi : w.sl i = .free) (hi' : w.sr i' = .free),
      TreeRel R (w.both i i' hi hi') (k i) (k' i')) → TreeRel R w (.nu k) (.nu k')
  /-- The left allocates a name to be matched later. -/
  | nuL {k : Nat → Tree S X} : (∀ i (hi : w.sl i = .free), TreeRel R (w.pendL i hi) (k i) t') →
      TreeRel R w (.nu k) t'
  | nuR {k' : Nat → Tree S X} : (∀ i' (hi' : w.sr i' = .free), TreeRel R (w.pendR i' hi') t (k' i')) →
      TreeRel R w t (.nu k')
  /-- The left allocates a name never to be matched. -/
  | gL {k : Nat → Tree S X} : (∀ i (hi : w.sl i = .free), TreeRel R (w.garbL i hi) (k i) t') →
      TreeRel R w (.nu k) t'
  | gR {k' : Nat → Tree S X} : (∀ i' (hi' : w.sr i' = .free), TreeRel R (w.garbR i' hi') t (k' i')) →
      TreeRel R w t (.nu k')
  /-- The left allocates a name and matches it with the right's pending `i'`. -/
  | mL {k : Nat → Tree S X} {i' : Nat} (hi' : w.sr i' = .p) : (∀ i (hi : w.sl i = .free),
      TreeRel R (w.matchL i i' hi hi') (k i) t') → TreeRel R w (.nu k) t'
  | mR {k' : Nat → Tree S X} {i : Nat} (hi : w.sl i = .p) : (∀ i' (hi' : w.sr i' = .free),
      TreeRel R (w.matchR i' i hi' hi) t (k' i')) → TreeRel R w t (.nu k')

/-! ## Monotonicity -/

theorem W.noPend_le {w w' : W} (h : w.noPend) (hw : w.le w') : w'.noPend :=
  ⟨fun a ha => h.1 a ((hw.pl a).1 ha), fun b hb => h.2 b ((hw.pr b).1 hb)⟩

theorem AR.mono {w w' : W} (h : ∀ a b, w.r a b → w'.r a b) {g : G} {a a' : Act g} :
    AR w a a' → AR w' a a'
  | .out => .out
  | .acq hr => .acq (h _ _ hr)
  | .use hr => .use (h _ _ hr)
  | .free hr => .free (h _ _ hr)
  | .new hr => .new (h _ _ hr)
  | .rd hr => .rd (h _ _ hr)
  | .wr hr => .wr (h _ _ hr)
  | .kill hr => .kill (h _ _ hr)

theorem DtorR.mono {w w' : W} (h : ∀ a b, w.r a b → w'.r a b) {δ δ' : Dtor} :
    DtorR w δ δ' → DtorR w' δ δ'
  | .free hr => .free (h _ _ hr)
  | .wb hr => .wb (h _ _ hr)

theorem DR.mono {w w' : W} (h : ∀ a b, w.r a b → w'.r a b) {d d' : List Dtor} :
    DR w d d' → DR w' d d'
  | .nil => .nil
  | .cons hδ hd => .cons (hδ.mono h) (hd.mono h)

theorem DR.append {w : W} {d d' e e' : List Dtor} : DR w d d' → DR w e e' → DR w (d ++ e) (d' ++ e')
  | .nil, he => he
  | .cons hδ hd, he => .cons hδ (hd.append he)

theorem TreeRel.mono {R : W → X → X → Prop}
    (hR : ∀ w w' x x', w.le w' → R w x x' → R w' x x') {w : W} {t t' : Tree S X}
    (h : TreeRel R w t t') : ∀ w', w.le w' → TreeRel R w' t t' := by
  induction h with
  | ret hp hx => intro w' hw; exact .ret (W.noPend_le hp hw) (hR _ _ _ _ hw hx)
  | op hp hi hd _ ih =>
      intro w' hw; exact .op (W.noPend_le hp hw) (hw.r _ _ hi) (hd.mono hw.r) (fun y => ih y w' hw)
  | ab hp hi hd => intro w' hw; exact .ab (W.noPend_le hp hw) (hw.r _ _ hi) (hd.mono hw.r)
  | abE hp hi hd hf =>
      intro w' hw; exact .abE (W.noPend_le hp hw) (hw.r _ _ hi) (hd.mono hw.r) (hf.mono hw.r)
  | act ha _ ih => intro w' hw; exact .act (ha.mono hw.r) (fun y => ih y w' hw)
  | nu _ ih =>
      intro w' hw
      exact .nu (fun i i' hi hi' => ih i i' (hw.fl i hi) (hw.fr i' hi') _ (W.le_both hw _ _ _ _))
  | nuL _ ih => intro w' hw; exact .nuL (fun i hi => ih i (hw.fl i hi) _ (W.le_pendL hw _ _))
  | nuR _ ih => intro w' hw; exact .nuR (fun i hi => ih i (hw.fr i hi) _ (W.le_pendR hw _ _))
  | gL _ ih => intro w' hw; exact .gL (fun i hi => ih i (hw.fl i hi) _ (W.le_garbL hw _ _))
  | gR _ ih => intro w' hw; exact .gR (fun i hi => ih i (hw.fr i hi) _ (W.le_garbR hw _ _))
  | mL hi' _ ih =>
      intro w' hw
      exact .mL (hw.pR hi') (fun i hi => ih i (hw.fl i hi) _ (W.le_matchL hw _ _ _ _))
  | mR hi _ ih =>
      intro w' hw
      exact .mR (hw.pL hi) (fun i hi' => ih i (hw.fr i hi') _ (W.le_matchR hw _ _ _ _))

theorem TreeRel.mapR {R R' : W → X → X → Prop} (hR : ∀ w x x', R w x x' → R' w x x')
    {w : W} {t t' : Tree S X} (h : TreeRel R w t t') : TreeRel R' w t t' := by
  induction h with
  | ret hp hx => exact .ret hp (hR _ _ _ hx)
  | op hp hi hd _ ih => exact .op hp hi hd ih
  | ab hp hi hd => exact .ab hp hi hd
  | abE hp hi hd hf => exact .abE hp hi hd hf
  | act ha _ ih => exact .act ha ih
  | nu _ ih => exact .nu ih
  | nuL _ ih => exact .nuL ih
  | nuR _ ih => exact .nuR ih
  | gL _ ih => exact .gL ih
  | gR _ ih => exact .gR ih
  | mL hi' _ ih => exact .mL hi' ih
  | mR hi _ ih => exact .mR hi ih

/-! ## Streams: the least relation closed under one unfolding -/

def StrmLeaf (P : W → Strm S X → Strm S X → Prop) (RA : W → X → X → Prop) (w : W) :
    (X ⊕ (Int × Strm S X)) → (X ⊕ (Int × Strm S X)) → Prop
  | .inl a, .inl a' => RA w a a'
  | .inr (n, s), .inr (n', s') => n = n' ∧ P w s s'
  | _, _ => False

def StrmClosed (RA : W → X → X → Prop) (P : W → Strm S X → Strm S X → Prop) : Prop :=
  ∀ w p p' d d', TreeRel (StrmLeaf P RA) w p p' → TreeRel (fun _ _ _ => True) w d d' →
    P w (.mk p d) (.mk p' d')

def StrmRel (RA : W → X → X → Prop) (w : W) (s s' : Strm S X) : Prop :=
  ∀ P, StrmClosed RA P → P w s s'

theorem StrmLeaf.map {P P' : W → Strm S X → Strm S X → Prop} {RA RA' : W → X → X → Prop}
    (hP : ∀ w s s', P w s s' → P' w s s') (hA : ∀ w a a', RA w a a' → RA' w a a') :
    ∀ w x x', StrmLeaf P RA w x x' → StrmLeaf P' RA' w x x'
  | _, .inl _, .inl _, h => hA _ _ _ h
  | _, .inr (_, _), .inr (_, _), h => ⟨h.1, hP _ _ _ h.2⟩
  | _, .inl _, .inr _, h => h.elim
  | _, .inr _, .inl _, h => h.elim

theorem StrmRel.intro {RA : W → X → X → Prop} {w : W} {p p' d d'}
    (hp : TreeRel (StrmLeaf (StrmRel (S := S) RA) RA) w p p')
    (hd : TreeRel (fun _ _ _ => True) w d d') : StrmRel RA w (.mk p d) (.mk p' d') :=
  fun P hP => hP w p p' d d' (hp.mapR (StrmLeaf.map (fun _ _ _ hs => hs P hP) (fun _ _ _ h => h)))
    hd

def StrmUnf (RA : W → X → X → Prop) (w : W) : Strm S X → Strm S X → Prop
  | .mk p d, .mk p' d' => TreeRel (StrmLeaf (StrmRel RA) RA) w p p' ∧
      TreeRel (fun _ _ _ => True) w d d'

theorem StrmRel.unf {RA : W → X → X → Prop} {w : W} {s s' : Strm S X}
    (h : StrmRel RA w s s') : StrmUnf RA w s s' := by
  apply h
  intro w p p' d d' hp hd
  refine ⟨hp.mapR (StrmLeaf.map (fun w s s' hs => ?_) (fun _ _ _ h => h)), hd⟩
  cases s; cases s'
  exact StrmRel.intro hs.1 hs.2

theorem StrmRel.elim {RA : W → X → X → Prop} {w : W} {p p' d d'}
    (h : StrmRel (S := S) RA w (.mk p d) (.mk p' d')) :
    TreeRel (StrmLeaf (StrmRel RA) RA) w p p' ∧ TreeRel (fun _ _ _ => True) w d d' := h.unf

theorem StrmLeaf.mono {P : W → Strm S X → Strm S X → Prop} {RA : W → X → X → Prop}
    (hP : ∀ w w' s s', w.le w' → P w s s' → P w' s s')
    (hA : ∀ w w' a a', w.le w' → RA w a a' → RA w' a a') :
    ∀ w w' x x', w.le w' → StrmLeaf P RA w x x' → StrmLeaf P RA w' x x'
  | _, _, .inl _, .inl _, hw, h => hA _ _ _ _ hw h
  | _, _, .inr (_, _), .inr (_, _), hw, h => ⟨h.1, hP _ _ _ _ hw h.2⟩
  | _, _, .inl _, .inr _, _, h => h.elim
  | _, _, .inr _, .inl _, _, h => h.elim

theorem StrmRel.mono {RA : W → X → X → Prop} (hA : ∀ w w' a a', w.le w' → RA w a a' → RA w' a a')
    {w : W} {s s' : Strm S X} (h : StrmRel RA w s s') : ∀ w', w.le w' → StrmRel RA w' s s' := by
  apply h (fun w s s' => ∀ w', w.le w' → StrmRel RA w' s s')
  intro w p p' d d' hp hd w' hw
  have hP : ∀ (w w' : W) (s s' : Strm S X), w.le w' →
      (fun w s s' => ∀ w', w.le w' → StrmRel RA w' s s') w s s' →
      (fun w s s' => ∀ w', w.le w' → StrmRel RA w' s s') w' s s' :=
    fun _ _ _ _ h1 h2 w'' h3 => h2 w'' (W.le.trans h1 h3)
  apply StrmRel.intro
  · exact ((hp.mono (StrmLeaf.mono hP hA) w' hw).mapR
      (StrmLeaf.map (fun w s s' hs => hs w (W.le.refl w)) (fun _ _ _ h => h)))
  · exact hd.mono (fun _ _ _ _ _ h => h) w' hw

/-! ## The value and computation relations -/

mutual
def VR : (A : VTy S) → W → A.den → A.den → Prop
  | .g _, _, a, a' => a = a'
  | .prod A B, w, a, a' => VR A w a.1 a'.1 ∧ VR B w a.2 a'.2
  | .sum A B, w, x, x' =>
      match (x : A.den ⊕ B.den), (x' : A.den ⊕ B.den) with
      | .inl a, .inl a' => VR A w a a'
      | .inr b, .inr b' => VR B w b b'
      | _, _ => False
  | .U _ C, w, c, c' => CRU C w.gcP c c'
  | .cap _ _, w, c, c' => w.r c.1 c'.1 ∧ ∀ w', w.gcP.le w' → ∀ o a st,
      TreeRel (fun _ x x' => x = x') w' (c.2 o a st) (c'.2 o a st)
  | .res, w, x, x' => x.1 = x'.1 ∧ w.r x.2 x'.2
  | .strm A, w, s, s' => StrmRel (fun w a a' => VR A w a a') w.gcP s s'

def CRU : (C : CTy S) → W → C.den → C.den → Prop
  | .F A, w, t, t' => TreeRel (fun w a a' => VR A w a a') w t t'
  | .arr A C, w, f, f' => ∀ w', w.le w' → ∀ a a', VR A w' a a' → CRU C w' (f a) (f' a')
  | .wth C D, w, p, p' => CRU C w p.1 p'.1 ∧ CRU D w p.2 p'.2
  | .pi _ C, w, f, f' => ∀ w', w.le w' → ∀ i i', w'.r i i' → CRU C w' (f i) (f' i')
end

mutual
theorem VR.mono : (A : VTy S) → ∀ {w w' : W} {a a' : A.den}, w.sub w' → VR A w a a' → VR A w' a a'
  | .g _, _, _, _, _, _, h => h
  | .prod A B, _, _, _, _, hw, h => by
      unfold VR at h ⊢; exact ⟨VR.mono A hw h.1, VR.mono B hw h.2⟩
  | .sum A B, _, _, x, x', hw, h => by
      unfold VR at h ⊢
      match x, x' with
      | .inl _, .inl _ => exact VR.mono A hw h
      | .inr _, .inr _ => exact VR.mono B hw h
      | .inl _, .inr _ => exact h.elim
      | .inr _, .inl _ => exact h.elim
  | .U _ C, _, _, _, _, hw, h => by unfold VR at h ⊢; exact CRU.mono C hw h
  | .cap _ _, _, _, _, _, hw, h => by
      unfold VR at h ⊢
      exact ⟨W.gcP_r.1 (hw.r _ _ (W.gcP_r.2 h.1)), fun w'' h2 => h.2 w'' (W.le.trans hw h2)⟩
  | .res, _, _, _, _, hw, h => by
      unfold VR at h ⊢; exact ⟨h.1, W.gcP_r.1 (hw.r _ _ (W.gcP_r.2 h.2))⟩
  | .strm A, _, _, _, _, hw, h => by
      unfold VR at h ⊢
      exact StrmRel.mono (RA := fun w a a' => VR A w a a') (fun _ _ _ _ h1 h2 => VR.mono A h1.sub h2) h _ hw

theorem CRU.mono : (C : CTy S) → ∀ {w w' : W} {c c' : C.den}, w.le w' → CRU C w c c' →
    CRU C w' c c'
  | .F A, _, _, _, _, hw, h => by
      unfold CRU at h ⊢
      exact TreeRel.mono (R := fun w a a' => VR A w a a') (fun _ _ _ _ h1 h2 => VR.mono A h1.sub h2) h _ hw
  | .arr _ _, _, _, _, _, hw, h => by
      unfold CRU at h ⊢; exact fun w'' h2 a a' ha => h w'' (W.le.trans hw h2) a a' ha
  | .wth C D, _, _, _, _, hw, h => by
      unfold CRU at h ⊢; exact ⟨CRU.mono C hw h.1, CRU.mono D hw h.2⟩
  | .pi _ _, _, _, _, _, hw, h => by
      unfold CRU at h ⊢; exact fun w'' h2 i i' hi => h w'' (W.le.trans hw h2) i i' hi
end

/-- Instance environments related: each instance variable names matched instances. -/
def IR (w : W) (η η' : IEnv (S := S) Ψ) : Prop := ∀ e (x : Var Ψ e), w.r (η e x) (η' e x)

/-- Value environments related. -/
def ER (w : W) (ρ ρ' : Env (S := S) Γ) : Prop := ∀ A (x : Var Γ A), VR A w (ρ A x) (ρ' A x)

theorem IR.mono {w w' : W} (h : ∀ a b, w.r a b → w'.r a b) {η η' : IEnv (S := S) Ψ}
    (hη : IR w η η') : IR w' η η' := fun e x => h _ _ (hη e x)

theorem ER.mono {w w' : W} (hw : w.sub w') {ρ ρ' : Env (S := S) Γ} (hρ : ER w ρ ρ') :
    ER w' ρ ρ' := fun A x => VR.mono A hw (hρ A x)

theorem IR.cons {w : W} {η η' : IEnv (S := S) Ψ} (hη : IR w η η') {i i' : Nat} (hi : w.r i i')
    (e : S.E) : IR (Ψ := e :: Ψ) w (η.cons i) (η'.cons i') := by
  intro e' x; cases x with
  | z => exact hi
  | s x => exact hη _ x

theorem ER.cons {w : W} {ρ ρ' : Env (S := S) Γ} (hρ : ER w ρ ρ') {A : VTy S} {a a' : A.den}
    (ha : VR A w a a') : ER (Γ := A :: Γ) w (ρ.cons a) (ρ'.cons a') := by
  intro B x; cases x with
  | z => exact ha
  | s x => exact hρ _ x

/-- The logical relation on open terms: related at every world with nothing pending, in related
environments. -/
def LR (M N : Cmp S Ψ Γ C) : Prop :=
  ∀ w, w.noPend → ∀ η η' ρ ρ', IR w η η' → ER w ρ ρ' → CRU C w (M.den η ρ) (N.den η' ρ')

end EffRel
