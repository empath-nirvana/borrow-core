import EffModelRel.Obs

/-!
# EffModelRel — worlds of the binary relation

A world says, for each name on each side, what it is to the relation:

- `free`: not yet allocated;
- `m b`: matched with the name `b` on the other side (a partial bijection, `coh`);
- `p`: allocated and waiting to be matched with a name the other side allocates later;
- `g`: allocated and never to be matched: an instance nothing can name, such as the fresh
  instance of `ν x. M` when `x` is not used.

Matched names are Staton's instances in `[Inj, Set]`: two related terms may use different names,
as long as they use them the same way. Pending names let the two sides allocate in different
orders (`ν/ν`); garbage names let one side allocate a name the other never does (`idem-ν`).

`le` is the order of Kripke worlds: more names matched, fewer free, the same pending. Values are
related at a world with its pending names read as garbage (`gcP`), so a value's relation does not
change while the two sides line up their allocations.
-/

namespace EffRel

inductive St where
  | free
  | m (b : Nat)
  | p
  | g
deriving DecidableEq

def upd (f : Nat → St) (a : Nat) (s : St) : Nat → St := fun x => if x = a then s else f x

@[simp] theorem upd_same (f : Nat → St) (a : Nat) (s : St) : upd f a s a = s := by simp [upd]

theorem upd_ne (f : Nat → St) {a x : Nat} (s : St) (h : x ≠ a) : upd f a s x = f x := by
  simp [upd, h]

structure W where
  sl : Nat → St
  sr : Nat → St
  coh : ∀ a b, sl a = .m b ↔ sr b = .m a

namespace W

def r (w : W) (a b : Nat) : Prop := w.sl a = .m b

theorem fn (w : W) {a b b' : Nat} (h : w.r a b) (h' : w.r a b') : b = b' := by
  unfold r at h h'; rw [h] at h'; cases h'; rfl

theorem inj (w : W) {a a' b : Nat} (h : w.r a b) (h' : w.r a' b) : a = a' := by
  have h1 := (w.coh a b).1 h
  have h2 := (w.coh a' b).1 h'
  rw [h1] at h2; cases h2; rfl

theorem r_iff (w : W) {i i' j j' : Nat} (hi : w.r i i') (hj : w.r j j') : j = i ↔ j' = i' := by
  constructor
  · intro h; subst h; exact w.fn hj hi
  · intro h; subst h; exact w.inj hj hi

theorem r_sr (w : W) {a b : Nat} (h : w.r a b) : w.sr b = .m a := (w.coh a b).1 h

def noPend (w : W) : Prop := (∀ a, w.sl a ≠ .p) ∧ (∀ b, w.sr b ≠ .p)

def init : W := ⟨fun _ => .free, fun _ => .free, by intro a b; simp⟩

theorem init_noPend : init.noPend := ⟨fun _ => by simp [init], fun _ => by simp [init]⟩

/-- Match `i` with `i'`. -/
def link (w : W) (i i' : Nat) (h1 : ∀ b, w.sl i ≠ .m b) (h2 : ∀ a, w.sr i' ≠ .m a) : W where
  sl := upd w.sl i (.m i')
  sr := upd w.sr i' (.m i)
  coh := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = i'
    · subst ha; subst hb; simp
    · subst ha; rw [upd_same, upd_ne _ _ hb]
      constructor
      · intro h; cases h; exact absurd rfl hb
      · intro h; exact absurd ((w.coh a b).2 h) (h1 b)
    · subst hb; rw [upd_ne _ _ ha, upd_same]
      constructor
      · intro h; exact absurd ((w.coh a b).1 h) (h2 a)
      · intro h; cases h; exact absurd rfl ha
    · rw [upd_ne _ _ ha, upd_ne _ _ hb]; exact w.coh a b

/-- Set the status of a left name to something other than a match. -/
def setL (w : W) (i : Nat) (s : St) (hs : ∀ b, s ≠ .m b) (h : ∀ b, w.sl i ≠ .m b) : W where
  sl := upd w.sl i s
  sr := w.sr
  coh := by
    intro a b
    by_cases ha : a = i
    · subst ha; rw [upd_same]
      constructor
      · intro hh; exact absurd hh (hs b)
      · intro hh; exact absurd ((w.coh a b).2 hh) (h b)
    · rw [upd_ne _ _ ha]; exact w.coh a b

def setR (w : W) (i : Nat) (s : St) (hs : ∀ a, s ≠ .m a) (h : ∀ a, w.sr i ≠ .m a) : W where
  sl := w.sl
  sr := upd w.sr i s
  coh := by
    intro a b
    by_cases hb : b = i
    · subst hb; rw [upd_same]
      constructor
      · intro hh; exact absurd ((w.coh a b).1 hh) (h a)
      · intro hh; exact absurd hh (hs a)
    · rw [upd_ne _ _ hb]; exact w.coh a b

theorem free_nm {w : W} {i : Nat} (h : w.sl i = .free) : ∀ b, w.sl i ≠ .m b := by
  intro b; rw [h]; exact St.noConfusion

theorem free_nmR {w : W} {i : Nat} (h : w.sr i = .free) : ∀ a, w.sr i ≠ .m a := by
  intro a; rw [h]; exact St.noConfusion

theorem p_nm {w : W} {i : Nat} (h : w.sl i = .p) : ∀ b, w.sl i ≠ .m b := by
  intro b; rw [h]; exact St.noConfusion

theorem p_nmR {w : W} {i : Nat} (h : w.sr i = .p) : ∀ a, w.sr i ≠ .m a := by
  intro a; rw [h]; exact St.noConfusion

/-- Both sides allocate, matched. -/
def both (w : W) (i i' : Nat) (hi : w.sl i = .free) (hi' : w.sr i' = .free) : W :=
  w.link i i' (free_nm hi) (free_nmR hi')

def pendL (w : W) (i : Nat) (hi : w.sl i = .free) : W :=
  w.setL i .p (fun _ => St.noConfusion) (free_nm hi)

def pendR (w : W) (i' : Nat) (hi' : w.sr i' = .free) : W :=
  w.setR i' .p (fun _ => St.noConfusion) (free_nmR hi')

def garbL (w : W) (i : Nat) (hi : w.sl i = .free) : W :=
  w.setL i .g (fun _ => St.noConfusion) (free_nm hi)

def garbR (w : W) (i' : Nat) (hi' : w.sr i' = .free) : W :=
  w.setR i' .g (fun _ => St.noConfusion) (free_nmR hi')

/-- The left allocates `i` and matches it with the right's pending `i'`. -/
def matchL (w : W) (i i' : Nat) (hi : w.sl i = .free) (hi' : w.sr i' = .p) : W :=
  w.link i i' (free_nm hi) (p_nmR hi')

/-- The right allocates `i'` and matches it with the left's pending `i`. -/
def matchR (w : W) (i' i : Nat) (hi' : w.sr i' = .free) (hi : w.sl i = .p) : W :=
  w.link i i' (p_nm hi) (free_nmR hi')

def gcf (f : Nat → St) : Nat → St := fun a => if f a = .p then .g else f a

/-- Pending names read as garbage: the world at which values are related. -/
def gcP (w : W) : W where
  sl := gcf w.sl
  sr := gcf w.sr
  coh := by
    intro a b
    unfold gcf
    by_cases ha : w.sl a = .p <;> by_cases hb : w.sr b = .p <;> simp only [ha, hb, if_true,
      if_false]
    · constructor <;> intro h <;> cases h
    · constructor
      · intro h; cases h
      · intro h; have := (w.coh a b).2 h; rw [ha] at this; cases this
    · constructor
      · intro h; have := (w.coh a b).1 h; rw [hb] at this; cases this
      · intro h; cases h
    · exact w.coh a b

/-- Kripke order: more matched, fewer free, the same pending. -/
structure le (w w' : W) : Prop where
  r : ∀ a b, w.r a b → w'.r a b
  fl : ∀ a, w'.sl a = .free → w.sl a = .free
  fr : ∀ b, w'.sr b = .free → w.sr b = .free
  pl : ∀ a, w'.sl a = .p ↔ w.sl a = .p
  pr : ∀ b, w'.sr b = .p ↔ w.sr b = .p

/-- The order along which values stay related: `le` with pending names read as garbage. -/
def sub (w w' : W) : Prop := w.gcP.le w'.gcP

theorem le.refl (w : W) : w.le w := ⟨fun _ _ h => h, fun _ h => h, fun _ h => h,
  fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem le.trans {w₁ w₂ w₃ : W} (h₁ : w₁.le w₂) (h₂ : w₂.le w₃) : w₁.le w₃ :=
  ⟨fun a b h => h₂.r a b (h₁.r a b h), fun a h => h₁.fl a (h₂.fl a h),
   fun b h => h₁.fr b (h₂.fr b h), fun a => (h₂.pl a).trans (h₁.pl a),
   fun b => (h₂.pr b).trans (h₁.pr b)⟩

theorem sub.refl (w : W) : w.sub w := le.refl _

theorem sub.trans {w₁ w₂ w₃ : W} (h₁ : w₁.sub w₂) (h₂ : w₂.sub w₃) : w₁.sub w₃ := le.trans h₁ h₂

theorem gcf_m {f : Nat → St} {a b : Nat} : gcf f a = .m b ↔ f a = .m b := by
  unfold gcf; by_cases h : f a = .p <;> simp [h]

theorem gcf_free {f : Nat → St} {a : Nat} : gcf f a = .free ↔ f a = .free := by
  unfold gcf; by_cases h : f a = .p <;> simp [h]

theorem gcf_p {f : Nat → St} {a : Nat} : gcf f a ≠ .p := by
  unfold gcf; by_cases h : f a = .p <;> simp [h]

theorem gcP_r {w : W} {a b : Nat} : w.gcP.r a b ↔ w.r a b := gcf_m

theorem gcP_sl (w : W) (a : Nat) : w.gcP.sl a = gcf w.sl a := rfl
theorem gcP_sr (w : W) (b : Nat) : w.gcP.sr b = gcf w.sr b := rfl

theorem le.sub {w w' : W} (h : w.le w') : w.sub w' :=
  ⟨fun a b hh => gcP_r.2 (h.r a b (gcP_r.1 hh)),
   fun a hh => gcf_free.2 (h.fl a (gcf_free.1 hh)),
   fun b hh => gcf_free.2 (h.fr b (gcf_free.1 hh)),
   fun _ => ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩,
   fun _ => ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩⟩

theorem noPend_le_of_sub {w w' : W} (hw : w.noPend) (hw' : w'.noPend) (h : w.sub w') : w.le w' :=
  ⟨fun a b hh => gcP_r.1 (h.r a b (gcP_r.2 hh)),
   fun a hh => gcf_free.1 (h.fl a (gcf_free.2 hh)),
   fun b hh => gcf_free.1 (h.fr b (gcf_free.2 hh)),
   fun a => ⟨fun hh => absurd hh (hw'.1 a), fun hh => absurd hh (hw.1 a)⟩,
   fun b => ⟨fun hh => absurd hh (hw'.2 b), fun hh => absurd hh (hw.2 b)⟩⟩

theorem le_gcP (w : W) (hw : w.noPend) : w.le w.gcP :=
  ⟨fun _ _ hh => gcP_r.2 hh, fun _ hh => gcf_free.1 hh, fun _ hh => gcf_free.1 hh,
   fun a => ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh (hw.1 a)⟩,
   fun b => ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh (hw.2 b)⟩⟩

theorem gcP_le (w : W) (hw : w.noPend) : w.gcP.le w :=
  ⟨fun _ _ hh => gcP_r.1 hh, fun _ hh => gcf_free.2 hh, fun _ hh => gcf_free.2 hh,
   fun a => ⟨fun hh => absurd hh (hw.1 a), fun hh => absurd hh gcf_p⟩,
   fun b => ⟨fun hh => absurd hh (hw.2 b), fun hh => absurd hh gcf_p⟩⟩

theorem gcP_noPend (w : W) : w.gcP.noPend := ⟨fun _ => gcf_p, fun _ => gcf_p⟩

/-! ## Updates and the orders -/

theorem link_r {w : W} {i i' h1 h2} {a b : Nat} : (w.link i i' h1 h2).r a b ↔
    (a = i ∧ b = i') ∨ (a ≠ i ∧ w.r a b) := by
  unfold r link; simp only
  by_cases ha : a = i
  · subst ha; simp only [upd_same, St.m.injEq, true_and, ne_eq, not_true_eq_false, false_and,
      or_false]; exact eq_comm
  · rw [upd_ne _ _ ha]; simp [ha]

theorem le_link {w w' : W} (h : w.le w') {i i' : Nat} (h1 h2 h1' h2') :
    (w.link i i' h1 h2).le (w'.link i i' h1' h2') where
  r a b hh := by
    rw [link_r] at hh ⊢
    rcases hh with hh | ⟨ha, hh⟩
    · exact .inl hh
    · exact .inr ⟨ha, h.r a b hh⟩
  fl a hh := by
    unfold link at hh ⊢; simp only at hh ⊢
    by_cases ha : a = i
    · subst ha; rw [upd_same] at hh; cases hh
    · rw [upd_ne _ _ ha] at hh ⊢; exact h.fl a hh
  fr b hh := by
    unfold link at hh ⊢; simp only at hh ⊢
    by_cases hb : b = i'
    · subst hb; rw [upd_same] at hh; cases hh
    · rw [upd_ne _ _ hb] at hh ⊢; exact h.fr b hh
  pl a := by
    unfold link; simp only
    by_cases ha : a = i
    · subst ha; simp
    · rw [upd_ne _ _ ha, upd_ne _ _ ha]; exact h.pl a
  pr b := by
    unfold link; simp only
    by_cases hb : b = i'
    · subst hb; simp
    · rw [upd_ne _ _ hb, upd_ne _ _ hb]; exact h.pr b

theorem le_setL {w w' : W} (h : w.le w') {i : Nat} {s : St} (hs h1 hs' h1') :
    (w.setL i s hs h1).le (w'.setL i s hs' h1') where
  r a b hh := by
    unfold setL r at hh ⊢; simp only at hh ⊢
    by_cases ha : a = i
    · subst ha; rw [upd_same] at hh ⊢; exact hh
    · rw [upd_ne _ _ ha] at hh ⊢; exact h.r a b hh
  fl a hh := by
    unfold setL at hh ⊢; simp only at hh ⊢
    by_cases ha : a = i
    · subst ha; rw [upd_same] at hh ⊢; exact hh
    · rw [upd_ne _ _ ha] at hh ⊢; exact h.fl a hh
  fr b hh := h.fr b hh
  pl a := by
    unfold setL; simp only
    by_cases ha : a = i
    · subst ha; simp
    · rw [upd_ne _ _ ha, upd_ne _ _ ha]; exact h.pl a
  pr b := h.pr b

theorem le_setR {w w' : W} (h : w.le w') {i : Nat} {s : St} (hs h1 hs' h1') :
    (w.setR i s hs h1).le (w'.setR i s hs' h1') where
  r a b hh := by
    have hh' := (W.coh _ a b).1 hh
    apply (W.coh _ a b).2
    unfold setR at hh' ⊢; simp only at hh' ⊢
    by_cases hb : b = i
    · subst hb; rw [upd_same] at hh' ⊢; exact hh'
    · rw [upd_ne _ _ hb] at hh' ⊢; exact (w'.coh a b).1 (h.r a b ((w.coh a b).2 hh'))
  fl a hh := h.fl a hh
  fr b hh := by
    unfold setR at hh ⊢; simp only at hh ⊢
    by_cases hb : b = i
    · subst hb; rw [upd_same] at hh ⊢; exact hh
    · rw [upd_ne _ _ hb] at hh ⊢; exact h.fr b hh
  pl a := h.pl a
  pr b := by
    unfold setR; simp only
    by_cases hb : b = i
    · subst hb; simp
    · rw [upd_ne _ _ hb, upd_ne _ _ hb]; exact h.pr b

theorem le.free {w w' : W} (h : w.le w') {a : Nat} (ha : w'.sl a = .free) : w.sl a = .free :=
  h.fl a ha

theorem le.freeR {w w' : W} (h : w.le w') {b : Nat} (hb : w'.sr b = .free) : w.sr b = .free :=
  h.fr b hb

theorem le.pR {w w' : W} (h : w.le w') {b : Nat} (hb : w.sr b = .p) : w'.sr b = .p :=
  (h.pr b).2 hb

theorem le.pL {w w' : W} (h : w.le w') {a : Nat} (ha : w.sl a = .p) : w'.sl a = .p :=
  (h.pl a).2 ha

theorem le_both {w w' : W} (h : w.le w') {i i'} (hi hi' hj hj') :
    (w.both i i' hi hi').le (w'.both i i' hj hj') := le_link h _ _ _ _

theorem le_pendL {w w' : W} (h : w.le w') {i} (hi hj) : (w.pendL i hi).le (w'.pendL i hj) :=
  le_setL h _ _ _ _

theorem le_pendR {w w' : W} (h : w.le w') {i} (hi hj) : (w.pendR i hi).le (w'.pendR i hj) :=
  le_setR h _ _ _ _

theorem le_garbL {w w' : W} (h : w.le w') {i} (hi hj) : (w.garbL i hi).le (w'.garbL i hj) :=
  le_setL h _ _ _ _

theorem le_garbR {w w' : W} (h : w.le w') {i} (hi hj) : (w.garbR i hi).le (w'.garbR i hj) :=
  le_setR h _ _ _ _

theorem le_matchL {w w' : W} (h : w.le w') {i i'} (hi hi' hj hj') :
    (w.matchL i i' hi hi').le (w'.matchL i i' hj hj') := le_link h _ _ _ _

theorem le_matchR {w w' : W} (h : w.le w') {i' i} (hi' hi hj' hj) :
    (w.matchR i' i hi' hi).le (w'.matchR i' i hj' hj) := le_link h _ _ _ _

/-! ## Each allocation step moves up `sub` -/

theorem sub_link {w : W} {i i' : Nat} (h1 h2) (hi : w.sl i ≠ .m i' → w.sl i = .free ∨ w.sl i = .p)
    (hi' : w.sr i' = .free ∨ w.sr i' = .p) : w.sub (w.link i i' h1 h2) where
  r a b hh := by
    rw [gcP_r] at hh ⊢; rw [link_r]
    by_cases ha : a = i
    · subst ha; exact absurd hh (h1 b)
    · exact .inr ⟨ha, hh⟩
  fl a hh := by
    rw [gcP_sl, gcf_free] at hh; rw [gcP_sl, gcf_free]
    unfold link at hh; simp only at hh
    by_cases ha : a = i
    · subst ha; rw [upd_same] at hh; cases hh
    · rw [upd_ne _ _ ha] at hh; exact hh
  fr b hh := by
    rw [gcP_sr, gcf_free] at hh; rw [gcP_sr, gcf_free]
    unfold link at hh; simp only at hh
    by_cases hb : b = i'
    · subst hb; rw [upd_same] at hh; cases hh
    · rw [upd_ne _ _ hb] at hh; exact hh
  pl _ := ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩
  pr _ := ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩

theorem sub_setL {w : W} {i : Nat} {s : St} (hs h1) (hfree : s ≠ .free) : w.sub (w.setL i s hs h1) where
  r a b hh := by
    rw [gcP_r] at hh ⊢
    unfold setL r; simp only
    by_cases ha : a = i
    · subst ha; exact absurd hh (h1 b)
    · rw [upd_ne _ _ ha]; exact hh
  fl a hh := by
    rw [gcP_sl, gcf_free] at hh; rw [gcP_sl, gcf_free]
    unfold setL at hh; simp only at hh
    by_cases ha : a = i
    · subst ha; rw [upd_same] at hh; exact absurd hh hfree
    · rw [upd_ne _ _ ha] at hh; exact hh
  fr b hh := by rw [gcP_sr, gcf_free] at hh; rw [gcP_sr, gcf_free]; exact hh
  pl _ := ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩
  pr _ := ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩

theorem sub_setR {w : W} {i : Nat} {s : St} (hs h1) (hfree : s ≠ .free) : w.sub (w.setR i s hs h1) where
  r a b hh := by
    rw [gcP_r] at hh ⊢
    unfold setR r; simp only; exact hh
  fl a hh := by rw [gcP_sl, gcf_free] at hh; rw [gcP_sl, gcf_free]; exact hh
  fr b hh := by
    rw [gcP_sr, gcf_free] at hh; rw [gcP_sr, gcf_free]
    unfold setR at hh; simp only at hh
    by_cases hb : b = i
    · subst hb; rw [upd_same] at hh; exact absurd hh hfree
    · rw [upd_ne _ _ hb] at hh; exact hh
  pl _ := ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩
  pr _ := ⟨fun hh => absurd hh gcf_p, fun hh => absurd hh gcf_p⟩

theorem sub_both (w : W) (i i' hi hi') : w.sub (w.both i i' hi hi') :=
  sub_link _ _ (fun _ => .inl hi) (.inl hi')

theorem sub_pendL (w : W) (i hi) : w.sub (w.pendL i hi) := sub_setL _ _ St.noConfusion
theorem sub_pendR (w : W) (i hi) : w.sub (w.pendR i hi) := sub_setR _ _ St.noConfusion
theorem sub_garbL (w : W) (i hi) : w.sub (w.garbL i hi) := sub_setL _ _ St.noConfusion
theorem sub_garbR (w : W) (i hi) : w.sub (w.garbR i hi) := sub_setR _ _ St.noConfusion

theorem sub_matchL (w : W) (i i' hi hi') : w.sub (w.matchL i i' hi hi') :=
  sub_link _ _ (fun _ => .inl hi) (.inr hi')

theorem sub_matchR (w : W) (i' i hi' hi) : w.sub (w.matchR i' i hi' hi) :=
  sub_link _ _ (fun _ => .inr hi) (.inl hi')

theorem le_link_self {w : W} {i i' : Nat} (h1 h2) (hi : w.sl i = .free) (hi' : w.sr i' = .free) :
    w.le (w.link i i' h1 h2) :=
  ⟨fun a b hh => by
      rw [link_r]
      by_cases ha : a = i
      · subst ha; exact absurd hh (h1 b)
      · exact .inr ⟨ha, hh⟩,
   fun a hh => by
      unfold link at hh; simp only at hh
      by_cases ha : a = i
      · subst ha; rw [upd_same] at hh; cases hh
      · rw [upd_ne _ _ ha] at hh; exact hh,
   fun b hh => by
      unfold link at hh; simp only at hh
      by_cases hb : b = i'
      · subst hb; rw [upd_same] at hh; cases hh
      · rw [upd_ne _ _ hb] at hh; exact hh,
   fun a => by
      unfold link; simp only
      by_cases ha : a = i
      · subst ha; simp [hi]
      · rw [upd_ne _ _ ha],
   fun b => by
      unfold link; simp only
      by_cases hb : b = i'
      · subst hb; simp [hi']
      · rw [upd_ne _ _ hb]⟩

theorem le_both_self (w : W) (i i' hi hi') : w.le (w.both i i' hi hi') :=
  le_link_self _ _ hi hi'

theorem le_garbL_self (w : W) (i hi) : w.le (w.garbL i hi) :=
  ⟨fun a b hh => by
      unfold garbL setL r; simp only
      by_cases ha : a = i
      · subst ha; exact absurd hh (free_nm hi b)
      · rw [upd_ne _ _ ha]; exact hh,
   fun a hh => by
      unfold garbL setL at hh; simp only at hh
      by_cases ha : a = i
      · subst ha; rw [upd_same] at hh; cases hh
      · rw [upd_ne _ _ ha] at hh; exact hh,
   fun _ hh => hh,
   fun a => by
      unfold garbL setL; simp only
      by_cases ha : a = i
      · subst ha; simp [hi]
      · rw [upd_ne _ _ ha],
   fun _ => Iff.rfl⟩

theorem le_garbR_self (w : W) (i hi) : w.le (w.garbR i hi) :=
  ⟨fun a b hh => by
      apply (W.coh _ a b).2
      unfold garbR setR; simp only
      have := (w.coh a b).1 hh
      by_cases hb : b = i
      · subst hb; rw [hi] at this; cases this
      · rw [upd_ne _ _ hb]; exact this,
   fun _ hh => hh,
   fun b hh => by
      unfold garbR setR at hh; simp only at hh
      by_cases hb : b = i
      · subst hb; rw [upd_same] at hh; cases hh
      · rw [upd_ne _ _ hb] at hh; exact hh,
   fun _ => Iff.rfl,
   fun b => by
      unfold garbR setR; simp only
      by_cases hb : b = i
      · subst hb; simp [hi]
      · rw [upd_ne _ _ hb]⟩

/-! ## Names in the updated worlds -/

theorem both_r (w : W) (i i' hi hi') : (w.both i i' hi hi').r i i' := by
  unfold both link r; simp

theorem matchL_r (w : W) (i i' hi hi') : (w.matchL i i' hi hi').r i i' := by
  unfold matchL link r; simp

theorem matchR_r (w : W) (i' i hi' hi) : (w.matchR i' i hi' hi).r i i' := by
  unfold matchR link r; simp

theorem noPend_both {w : W} (hw : w.noPend) (i i' hi hi') : (w.both i i' hi hi').noPend :=
  ⟨fun a => by
      unfold both link; simp only
      by_cases ha : a = i
      · subst ha; simp
      · rw [upd_ne _ _ ha]; exact hw.1 a,
   fun b => by
      unfold both link; simp only
      by_cases hb : b = i'
      · subst hb; simp
      · rw [upd_ne _ _ hb]; exact hw.2 b⟩

theorem noPend_garbL {w : W} (hw : w.noPend) (i hi) : (w.garbL i hi).noPend :=
  ⟨fun a => by
      unfold garbL setL; simp only
      by_cases ha : a = i
      · subst ha; simp
      · rw [upd_ne _ _ ha]; exact hw.1 a,
   hw.2⟩

theorem noPend_garbR {w : W} (hw : w.noPend) (i hi) : (w.garbR i hi).noPend :=
  ⟨hw.1, fun b => by
      unfold garbR setR; simp only
      by_cases hb : b = i
      · subst hb; simp
      · rw [upd_ne _ _ hb]; exact hw.2 b⟩

end W

end EffRel
