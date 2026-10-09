import Targets.B.Adequacy

/-!
# System B — the step-for-step simulation B5 rests on (OQ-43 (b))

Every complete run of a typed program is, step for step, the image of a run of the bump allocator
from the same start (`bump_follows_at`), so B5 follows from B4′ at every typing system and borrow
world (`releasedOnceReuse_of_soundContracts`), and holds at today's unr-free kernel and BoLo
(`releasedOnceReuse_tier1NU`).

* **Renaming along a function** (`Expr.mapLoc`, `Kont.mapLoc`, `Heap.push`) commutes with shifting,
  substitution, plugging, the continuation `[op]` captures, a handler's clauses, the cancel payload
  and the error it keeps, the host step, the counted loops and the fuelled fixed point.  The array
  steps compute locations, `ℓ + j` from an array value `(ℓ, n)`, and commute with a renaming that
  moves `[ℓ, ℓ + n]` as a block (`tabFill_mapLoc`, `dropFill_mapLoc`, `idxAns_mapLoc`,
  `splitAns_mapLoc`).
* **A head step, renamed** (`head_image`): a step that allocates nothing, along a map injective on
  the live heap that moves the array steps' offsets as blocks, is a step of the pushed memory.  A
  renamed redex is a redex (`head_mapLoc_exists`), so it is the redex of every step of the renamed
  term (`step_at_image`, from Core's unique decomposition).
* **What a step names** (`named_step`): what its configuration named, or an array step's location,
  less than `2³²` above one it named.
* **The invariant** (`AffineAbove g μ e k`): `g` moves as a block the window `[ℓ, ℓ + (k + 1) · 2³²]`
  above every named location `ℓ`.  A step that allocates nothing narrows the windows by `2³²`
  (`affineAbove_step`); a bump allocation places its cell or block above every name, every window
  and `X`, where the new map translates onto the given step's (`sim_alloc`, `sim_tab`).
* **The simulation** (`BumpSimAt`, `bumpSimAt`): base's `BumpSim` with the hypotheses a bump run
  supplies: the platform keeps its protocol, the memory is finite, the windows hold for the steps
  to go, and the platform is asked at data arguments.
* **The protocol on every run** (`platData_of_safe`): a program safe under the platform restricted
  to data arguments (`Platform.restrict`) asks the platform at data arguments only, on every run.
  B4′ quantifies over every platform that keeps its protocol, the restricted one among them.

`[Core σ=[]]`: facts about Core's machine, read at no world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa clauseAt errNext errVal capTag kappaAt kappaC kappaCell kappaCBody
  freeE stuckE)

/-- `omega` over locations: `Loc` unfolded to `Nat` first. -/
local macro "lomega" : tactic => `(tactic| (try simp only [Loc] at *) <;> omega)

/-- `linarith` over locations: `Loc` unfolded to `Nat` first. -/
local macro "llinarith" : tactic => `(tactic| (try simp only [Loc] at *) <;> linarith)

/-! ### Renaming along a function commutes with the term operations -/

theorem mapLoc_shift (g : Loc → Loc) :
    ∀ (d c : Nat) (e : Expr), (e.shift d c).mapLoc g = (e.mapLoc g).shift d c
  | d, c, .var i => by by_cases h : i < c <;> simp [Expr.shift, Expr.mapLoc, h]
  | _, _, .unit | _, _, .prim _ | _, _, .loc _ => rfl
  | d, c, .pair a b | d, c, .seq a b | d, c, .app a b => by
      simp only [Expr.shift, Expr.mapLoc, mapLoc_shift g d c a, mapLoc_shift g d c b]
  | d, c, .letpair a b => by
      simp only [Expr.shift, Expr.mapLoc, mapLoc_shift g d c a, mapLoc_shift g d (c + 2) b]
  | d, c, .inj₁ a | d, c, .inj₂ a => by simp only [Expr.shift, Expr.mapLoc, mapLoc_shift g d c a]
  | d, c, .lam a => by simp only [Expr.shift, Expr.mapLoc, mapLoc_shift g d (c + 1) a]
  | d, c, .case a b e => by
      simp only [Expr.shift, Expr.mapLoc, mapLoc_shift g d c a, mapLoc_shift g d (c + 1) b,
        mapLoc_shift g d (c + 1) e]

theorem valMapLoc_shift (g : Loc → Loc) (d c : Nat) (v : Val) :
    (v.shift d c).mapLoc g = (v.mapLoc g).shift d c :=
  Subtype.ext (mapLoc_shift g d c v.1)

theorem mapLoc_subst (g : Loc → Loc) :
    ∀ (j : Nat) (s : Val) (e : Expr), (e.subst j s).mapLoc g = (e.mapLoc g).subst j (s.mapLoc g)
  | j, s, .var i => by
      simp only [Expr.subst, Expr.mapLoc]
      by_cases h₁ : i = j
      · simp [h₁]; rfl
      · by_cases h₂ : i > j <;> simp [h₁, h₂, Expr.mapLoc]
  | _, _, .unit | _, _, .prim _ | _, _, .loc _ => rfl
  | j, s, .pair a b | j, s, .seq a b | j, s, .app a b => by
      simp only [Expr.subst, Expr.mapLoc, mapLoc_subst g j s a, mapLoc_subst g j s b]
  | j, s, .letpair a b => by
      simp only [Expr.subst, Expr.mapLoc, mapLoc_subst g j s a,
        mapLoc_subst g (j + 2) (s.shift 2 0) b, valMapLoc_shift]
  | j, s, .inj₁ a | j, s, .inj₂ a => by
      simp only [Expr.subst, Expr.mapLoc, mapLoc_subst g j s a]
  | j, s, .lam a => by
      simp only [Expr.subst, Expr.mapLoc, mapLoc_subst g (j + 1) (s.shift 1 0) a, valMapLoc_shift]
  | j, s, .case a b e => by
      simp only [Expr.subst, Expr.mapLoc, mapLoc_subst g j s a,
        mapLoc_subst g (j + 1) (s.shift 1 0) b, mapLoc_subst g (j + 1) (s.shift 1 0) e,
        valMapLoc_shift]

/-- Renaming makes no term a value. -/
theorem isVal_of_mapLoc (g : Loc → Loc) : ∀ {e : Expr}, IsVal (e.mapLoc g) → IsVal e
  | .unit, _ => .unit
  | .pair _ _, h => .pair (isVal_of_mapLoc g h.pair_left) (isVal_of_mapLoc g h.pair_right)
  | .inj₁ _, h => .inj₁ (isVal_of_mapLoc g h.inj₁_inv)
  | .inj₂ _, h => .inj₂ (isVal_of_mapLoc g h.inj₂_inv)
  | .lam _, _ => .lam
  | .loc _, _ => .loc
  | .prim _, _ => .prim
  | .app f _, h => by
      have hf := h.app_fun
      cases f with
      | prim p =>
          simp only [Expr.mapLoc, Expr.prim.injEq] at hf
          subst hf
          exact .storeV (isVal_of_mapLoc g h.app_arg)
      | _ => simp [Expr.mapLoc] at hf
  | .var _, h | .seq _ _, h | .letpair _ _, h | .case _ _ _, h => by
      simp [Expr.mapLoc] at h

/-- Renamings that agree on the locations of `e` rename it alike. -/
theorem mapLoc_congr {g g' : Loc → Loc} :
    ∀ e : Expr, (∀ ℓ, e.MentionsLoc ℓ → g ℓ = g' ℓ) → e.mapLoc g = e.mapLoc g'
  | .var _, _ | .unit, _ | .prim _, _ => rfl
  | .loc k, h => by simp only [Expr.mapLoc, h k rfl]
  | .pair a b, h | .seq a b, h | .letpair a b, h | .app a b, h => by
      simp only [Expr.mapLoc, mapLoc_congr a (fun ℓ o => h ℓ (Or.inl o)),
        mapLoc_congr b (fun ℓ o => h ℓ (Or.inr o))]
  | .inj₁ a, h | .inj₂ a, h | .lam a, h => by
      simp only [Expr.mapLoc, mapLoc_congr a h]
  | .case a b c, h => by
      simp only [Expr.mapLoc, mapLoc_congr a (fun ℓ o => h ℓ (Or.inl o)),
        mapLoc_congr b (fun ℓ o => h ℓ (Or.inr (Or.inl o))),
        mapLoc_congr c (fun ℓ o => h ℓ (Or.inr (Or.inr o)))]

theorem valMapLoc_congr {g g' : Loc → Loc} (v : Val) (h : ∀ ℓ, v.1.MentionsLoc ℓ → g ℓ = g' ℓ) :
    v.mapLoc g = v.mapLoc g' :=
  Subtype.ext (mapLoc_congr v.1 h)

/-- The locations a renamed term mentions are the images of the term's. -/
theorem mentionsLoc_mapLoc {g : Loc → Loc} {x : Loc} :
    ∀ e : Expr, (e.mapLoc g).MentionsLoc x ↔ ∃ ℓ, e.MentionsLoc ℓ ∧ g ℓ = x
  | .var _ | .unit | .prim _ => by simp [Expr.mapLoc, Expr.MentionsLoc]
  | .loc k => by simp [Expr.mapLoc, Expr.MentionsLoc]
  | .pair a b | .seq a b | .letpair a b | .app a b => by
      simp only [Expr.mapLoc, Expr.MentionsLoc, mentionsLoc_mapLoc a, mentionsLoc_mapLoc b]
      constructor
      · rintro (⟨k, h, rfl⟩ | ⟨k, h, rfl⟩)
        · exact ⟨k, .inl h, rfl⟩
        · exact ⟨k, .inr h, rfl⟩
      · rintro ⟨k, h | h, rfl⟩
        · exact .inl ⟨k, h, rfl⟩
        · exact .inr ⟨k, h, rfl⟩
  | .inj₁ a | .inj₂ a | .lam a => by
      simp only [Expr.mapLoc, Expr.MentionsLoc, mentionsLoc_mapLoc a]
  | .case a b c => by
      simp only [Expr.mapLoc, Expr.MentionsLoc, mentionsLoc_mapLoc a, mentionsLoc_mapLoc b,
        mentionsLoc_mapLoc c]
      constructor
      · rintro (⟨k, h, rfl⟩ | ⟨k, h, rfl⟩ | ⟨k, h, rfl⟩)
        · exact ⟨k, .inl h, rfl⟩
        · exact ⟨k, .inr (.inl h), rfl⟩
        · exact ⟨k, .inr (.inr h), rfl⟩
      · rintro ⟨k, h | h | h, rfl⟩
        · exact .inl ⟨k, h, rfl⟩
        · exact .inr (.inl ⟨k, h, rfl⟩)
        · exact .inr (.inr ⟨k, h, rfl⟩)

/-- Shifting changes no location. -/
theorem mentionsLoc_shift {x : Loc} :
    ∀ (d c : Nat) (e : Expr), (e.shift d c).MentionsLoc x ↔ e.MentionsLoc x
  | d, c, .var i => by by_cases h : i < c <;> simp [Expr.shift, Expr.MentionsLoc, h]
  | _, _, .unit | _, _, .prim _ | _, _, .loc _ => Iff.rfl
  | d, c, .pair a b | d, c, .seq a b | d, c, .app a b => by
      simp only [Expr.shift, Expr.MentionsLoc, mentionsLoc_shift d c a, mentionsLoc_shift d c b]
  | d, c, .letpair a b => by
      simp only [Expr.shift, Expr.MentionsLoc, mentionsLoc_shift d c a,
        mentionsLoc_shift d (c + 2) b]
  | d, c, .inj₁ a | d, c, .inj₂ a => by
      simp only [Expr.shift, Expr.MentionsLoc, mentionsLoc_shift d c a]
  | d, c, .lam a => by simp only [Expr.shift, Expr.MentionsLoc, mentionsLoc_shift d (c + 1) a]
  | d, c, .case a b e => by
      simp only [Expr.shift, Expr.MentionsLoc, mentionsLoc_shift d c a,
        mentionsLoc_shift d (c + 1) b, mentionsLoc_shift d (c + 1) e]

/-- A substitution's locations are the term's or the value's. -/
theorem mentionsLoc_subst {x : Loc} :
    ∀ (j : Nat) (s : Val) (e : Expr), (e.subst j s).MentionsLoc x →
      e.MentionsLoc x ∨ s.1.MentionsLoc x
  | j, s, .var i, h => by
      simp only [Expr.subst] at h
      by_cases h₁ : i = j
      · simp only [h₁, if_true] at h; exact .inr h
      · by_cases h₂ : i > j <;> simp [h₁, h₂, Expr.MentionsLoc] at h
  | _, _, .unit, h | _, _, .prim _, h => h.elim
  | _, _, .loc _, h => .inl h
  | j, s, .pair a b, h | j, s, .seq a b, h | j, s, .app a b, h => by
      rcases h with h | h
      · exact (mentionsLoc_subst j s a h).imp .inl id
      · exact (mentionsLoc_subst j s b h).imp .inr id
  | j, s, .letpair a b, h => by
      rcases h with h | h
      · exact (mentionsLoc_subst j s a h).imp .inl id
      · exact (mentionsLoc_subst (j + 2) (s.shift 2 0) b h).imp .inr
          (fun h' => (mentionsLoc_shift 2 0 s.1).mp h')
  | j, s, .inj₁ a, h | j, s, .inj₂ a, h => mentionsLoc_subst j s a h
  | j, s, .lam a, h => (mentionsLoc_subst (j + 1) (s.shift 1 0) a h).imp id
      (fun h' => (mentionsLoc_shift 1 0 s.1).mp h')
  | j, s, .case a b e, h => by
      rcases h with h | h | h
      · exact (mentionsLoc_subst j s a h).imp .inl id
      · exact (mentionsLoc_subst (j + 1) (s.shift 1 0) b h).imp (fun h' => .inr (.inl h'))
          (fun h' => (mentionsLoc_shift 1 0 s.1).mp h')
      · exact (mentionsLoc_subst (j + 1) (s.shift 1 0) e h).imp (fun h' => .inr (.inr h'))
          (fun h' => (mentionsLoc_shift 1 0 s.1).mp h')

/-! ### Contexts, and the values the effect steps build -/

/-- `K` with every location renamed along `g`. -/
def _root_.BoCa.BoLo.Kont.mapLoc (g : Loc → Loc) : Kont → Kont
  | .hole          => .hole
  | .pairL K e     => .pairL (K.mapLoc g) (e.mapLoc g)
  | .pairR v K     => .pairR (v.mapLoc g) (K.mapLoc g)
  | .letpair K e   => .letpair (K.mapLoc g) (e.mapLoc g)
  | .case K e₁ e₂  => .case (K.mapLoc g) (e₁.mapLoc g) (e₂.mapLoc g)
  | .appR f K      => .appR (f.mapLoc g) (K.mapLoc g)
  | .appL K v      => .appL (K.mapLoc g) (v.mapLoc g)
  | .seq K e       => .seq (K.mapLoc g) (e.mapLoc g)
  | .inj₁ K        => .inj₁ (K.mapLoc g)
  | .inj₂ K        => .inj₂ (K.mapLoc g)

theorem kont_mapLoc_plug (g : Loc → Loc) (K : Kont) (e : Expr) :
    (K.plug e).mapLoc g = (K.mapLoc g).plug (e.mapLoc g) := by
  induction K with
  | hole => rfl
  | pairR v K ih => simp only [Kont.plug, Kont.mapLoc, Expr.mapLoc, ih]; rfl
  | appL K v ih => simp only [Kont.plug, Kont.mapLoc, Expr.mapLoc, ih]; rfl
  | _ => simp_all [Kont.plug, Kont.mapLoc, Expr.mapLoc]

theorem kont_mapLoc_shift (g : Loc → Loc) (d c : Nat) (K : Kont) :
    (K.shift d c).mapLoc g = (K.mapLoc g).shift d c := by
  induction K with
  | hole => rfl
  | pairR v K ih => simp only [Kont.shift, Kont.mapLoc, ih, valMapLoc_shift]
  | appL K v ih => simp only [Kont.shift, Kont.mapLoc, ih, valMapLoc_shift]
  | _ => simp_all [Kont.shift, Kont.mapLoc, mapLoc_shift]

/-- A context's locations, as those of the context around `()`. -/
theorem mentionsLoc_plug {x : Loc} (K : Kont) (e : Expr) :
    (K.plug e).MentionsLoc x ↔ (K.plug .unit).MentionsLoc x ∨ e.MentionsLoc x := by
  induction K with
  | hole => simp [Kont.plug, Expr.MentionsLoc]
  | pairL K e₂ ih | letpair K e₂ ih | seq K e₂ ih =>
      simp only [Kont.plug, Expr.MentionsLoc, ih]; tauto
  | pairR v K ih | appR v K ih => simp only [Kont.plug, Expr.MentionsLoc, ih]; tauto
  | appL K v ih => simp only [Kont.plug, Expr.MentionsLoc, ih]; tauto
  | case K e₁ e₂ ih => simp only [Kont.plug, Expr.MentionsLoc, ih]; tauto
  | inj₁ K ih | inj₂ K ih => simp only [Kont.plug, Expr.MentionsLoc, ih]

/-- Renamings that agree on a context's locations rename it alike. -/
theorem kont_mapLoc_congr {g g' : Loc → Loc} :
    ∀ (K : Kont), (∀ ℓ, (K.plug .unit).MentionsLoc ℓ → g ℓ = g' ℓ) → K.mapLoc g = K.mapLoc g'
  | .hole, _ => rfl
  | .pairL K e, h | .letpair K e, h | .seq K e, h => by
      simp only [Kont.mapLoc, kont_mapLoc_congr K (fun ℓ o => h ℓ (Or.inl o)),
        mapLoc_congr e (fun ℓ o => h ℓ (Or.inr o))]
  | .pairR v K, h => by
      simp only [Kont.mapLoc, kont_mapLoc_congr K (fun ℓ o => h ℓ (Or.inr o)),
        valMapLoc_congr v (fun ℓ o => h ℓ (Or.inl o))]
  | .appR f K, h => by
      simp only [Kont.mapLoc, kont_mapLoc_congr K (fun ℓ o => h ℓ (Or.inr o)),
        mapLoc_congr f (fun ℓ o => h ℓ (Or.inl o))]
  | .appL K v, h => by
      simp only [Kont.mapLoc, kont_mapLoc_congr K (fun ℓ o => h ℓ (Or.inl o)),
        valMapLoc_congr v (fun ℓ o => h ℓ (Or.inr o))]
  | .case K e₁ e₂, h => by
      simp only [Kont.mapLoc, kont_mapLoc_congr K (fun ℓ o => h ℓ (Or.inl o)),
        mapLoc_congr e₁ (fun ℓ o => h ℓ (Or.inr (Or.inl o))),
        mapLoc_congr e₂ (fun ℓ o => h ℓ (Or.inr (Or.inr o)))]
  | .inj₁ K, h | .inj₂ K, h => by
      simp only [Kont.mapLoc, kont_mapLoc_congr K h]

/-- A renamed term's outermost former is the term's. -/
theorem mapLoc_eq_app {g : Loc → Loc} {e a b : Expr} (h : e.mapLoc g = .app a b) :
    ∃ a' b', e = .app a' b' ∧ a'.mapLoc g = a ∧ b'.mapLoc g = b := by
  cases e <;> simp only [Expr.mapLoc, reduceCtorEq, Expr.app.injEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem mapLoc_eq_pair {g : Loc → Loc} {e a b : Expr} (h : e.mapLoc g = .pair a b) :
    ∃ a' b', e = .pair a' b' ∧ a'.mapLoc g = a ∧ b'.mapLoc g = b := by
  cases e <;> simp only [Expr.mapLoc, reduceCtorEq, Expr.pair.injEq] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem mapLoc_eq_prim {g : Loc → Loc} {e : Expr} {p : Prim} (h : e.mapLoc g = .prim p) :
    e = .prim p := by
  cases e <;> simp only [Expr.mapLoc, reduceCtorEq, Expr.prim.injEq] at h
  rw [h]

/-- A renamed context has the handlers it had. -/
theorem hasHnd_mapLoc (g : Loc → Loc) (n : UInt32) (K : Kont) :
    (K.mapLoc g).HasHnd n = K.HasHnd n := by
  induction K with
  | appR f K ih =>
      simp only [Kont.mapLoc, Kont.HasHnd, ih]
      congr 1
      split
      next m e₂ heq =>
        obtain ⟨a, b, rfl, ha, hb⟩ := mapLoc_eq_app heq
        obtain rfl := mapLoc_eq_prim ha
        obtain ⟨c, d, rfl, hc, -⟩ := mapLoc_eq_pair hb
        obtain rfl := mapLoc_eq_prim hc
        rfl
      next hne =>
        split
        next m e₂ => exact absurd rfl (hne m (e₂.mapLoc g))
        next => rfl
  | _ => simp_all [Kont.mapLoc, Kont.HasHnd]

/-- A renamed context has the catchers it had. -/
theorem catches_mapLoc (g : Loc → Loc) (n : UInt32) (K : Kont) :
    (K.mapLoc g).Catches n = K.Catches n := by
  induction K with
  | appR f K ih =>
      simp only [Kont.mapLoc, Kont.Catches, ih]
      congr 1
      split
      next m e₂ heq =>
        obtain ⟨a, b, rfl, ha, hb⟩ := mapLoc_eq_app heq
        obtain rfl := mapLoc_eq_prim ha
        obtain ⟨c, d, rfl, hc, -⟩ := mapLoc_eq_pair hb
        obtain rfl := mapLoc_eq_prim hc
        rfl
      next e₂ heq =>
        obtain ⟨a, b, rfl, ha, -⟩ := mapLoc_eq_app heq
        obtain rfl := mapLoc_eq_prim ha
        rfl
      next heq =>
        obtain rfl := mapLoc_eq_prim heq
        rfl
      next e₂ heq =>
        obtain ⟨a, b, rfl, ha, -⟩ := mapLoc_eq_app heq
        obtain rfl := mapLoc_eq_prim ha
        rfl
      next h₁ h₂ h₃ h₄ =>
        split
        next m e₂ => exact absurd rfl (h₁ m (e₂.mapLoc g))
        next e₂ => exact absurd rfl (h₂ (e₂.mapLoc g))
        next => exact absurd rfl h₃
        next e₂ => exact absurd rfl (h₄ (e₂.mapLoc g))
        next => rfl
  | _ => simp_all [Kont.mapLoc, Kont.Catches]

/-- A renamed frame dies with a cancel exactly when the frame does. -/
theorem deadFrame_mapLoc (g : Loc → Loc) (f : Expr) :
    Kont.DeadFrame (f.mapLoc g) = Kont.DeadFrame f := by
  unfold Kont.DeadFrame
  split
  next m e₂ heq =>
    obtain ⟨a, b, rfl, ha, hb⟩ := mapLoc_eq_app heq
    obtain rfl := mapLoc_eq_prim ha
    obtain ⟨c, d, rfl, hc, -⟩ := mapLoc_eq_pair hb
    obtain rfl := mapLoc_eq_prim hc
    rfl
  next heq =>
    obtain rfl := mapLoc_eq_prim heq
    rfl
  next h₁ h₂ =>
    split
    next m e₂ => exact absurd rfl (h₁ m (e₂.mapLoc g))
    next => exact absurd rfl h₂
    next => rfl

/-- A renamed region's dead region is the dead region renamed. -/
theorem dead_mapLoc (g : Loc → Loc) (K : Kont) : (K.mapLoc g).dead = K.dead.mapLoc g := by
  induction K with
  | appR f K ih =>
      simp only [Kont.mapLoc, Kont.dead, deadFrame_mapLoc, ih]
      split <;> rfl
  | _ => simp_all [Kont.mapLoc, Kont.dead]

/-! ### The values and terms the steps build -/

theorem pair_mapLoc (g : Loc → Loc) (v w : Val) :
    (Val.pair v w).mapLoc g = Val.pair (v.mapLoc g) (w.mapLoc g) := rfl
theorem inj₁_mapLoc (g : Loc → Loc) (v : Val) : (Val.inj₁ v).mapLoc g = Val.inj₁ (v.mapLoc g) := rfl
theorem loc_mapLoc (g : Loc → Loc) (ℓ : Loc) : (Val.loc ℓ).mapLoc g = Val.loc (g ℓ) := rfl
theorem arr_mapLoc (g : Loc → Loc) (ℓ : Loc) (n : UInt32) :
    (Val.arr ℓ n).mapLoc g = Val.arr (g ℓ) n := rfl
theorem opPayload_mapLoc (g : Loc → Loc) (n i : UInt32) (v : Val) :
    (opPayload n i v).mapLoc g = opPayload n i (v.mapLoc g) := rfl
theorem hndVal_mapLoc (g : Loc → Loc) (n : UInt32) (qs hr hs : Val) :
    (hndVal n qs hr hs).mapLoc g = hndVal n (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) := rfl

theorem capTag_mapLoc (g : Loc → Loc) (e : Expr) (i : Nat) : capTag (e.mapLoc g) i = capTag e i := by
  induction e generalizing i with
  | pair a r _ ihr =>
      cases i with
      | zero =>
          cases a with
          | prim p =>
              cases p with
              | lit c => cases c <;> rfl
              | _ => rfl
          | _ => rfl
      | succ i => simpa only [Expr.mapLoc, capTag] using ihr i
  | _ => cases i <;> rfl

theorem errVal_mapLoc (g : Loc → Loc) (err : Option Val) :
    (errVal err).mapLoc g = errVal (err.map (Val.mapLoc g)) := by
  cases err <;> rfl

theorem cancelVal_mapLoc (g : Loc → Loc) (err : Option Val) :
    (cancelVal err).mapLoc g = cancelVal (err.map (Val.mapLoc g)) := by
  simp only [cancelVal, opPayload_mapLoc, errVal_mapLoc]

theorem errNext_mapLoc (g : Loc → Loc) (err : Option Val) (m j : UInt32) (w : Val) :
    (errNext err m j w).map (Val.mapLoc g) = errNext (err.map (Val.mapLoc g)) m j (w.mapLoc g) := by
  cases err <;> rfl

theorem or_mapLoc (g : Loc → Loc) (err err' : Option Val) :
    (err.or err').map (Val.mapLoc g) = (err.map (Val.mapLoc g)).or (err'.map (Val.mapLoc g)) := by
  cases err <;> rfl

theorem hndE_mapLoc (g : Loc → Loc) (H : Val) (e : Expr) :
    (hndE H e).mapLoc g = hndE (H.mapLoc g) (e.mapLoc g) := rfl
theorem ubindE_mapLoc (g : Loc → Loc) (ND : Val) (e : Expr) :
    (ubindE ND e).mapLoc g = ubindE (ND.mapLoc g) (e.mapLoc g) := rfl
theorem ccatchE_mapLoc (g : Loc → Loc) (e : Expr) : (ccatchE e).mapLoc g = ccatchE (e.mapLoc g) := rfl
theorem cfinE_mapLoc (g : Loc → Loc) (st : Val) (e : Expr) :
    (cfinE st e).mapLoc g = cfinE (st.mapLoc g) (e.mapLoc g) := rfl
theorem performE_mapLoc (g : Loc → Loc) (p : Expr) :
    (performE p).mapLoc g = performE (p.mapLoc g) := rfl
theorem raiseE_mapLoc (g : Loc → Loc) (p : Expr) : (raiseE p).mapLoc g = raiseE (p.mapLoc g) := rfl

/-- The continuation `[op]` captures, renamed, is the renamed handler's over the renamed context. -/
theorem kappa_mapLoc (g : Loc → Loc) (H : Val) (K : Kont) :
    (kappa H K).mapLoc g = kappa (H.mapLoc g) (K.mapLoc g) := by
  have h₁ : ((K.shift 3 0).plug (.var 0)).mapLoc g = ((K.mapLoc g).shift 3 0).plug (.var 0) := by
    rw [kont_mapLoc_plug, kont_mapLoc_shift]; rfl
  have h₂ : ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none)))).mapLoc g =
      (((K.mapLoc g).dead.shift 2 0).plug (raiseE (.val (cancelVal none)))) := by
    rw [kont_mapLoc_plug, kont_mapLoc_shift, dead_mapLoc, raiseE_mapLoc]
    congr 2
  have h₃ : (H.shift 3 0).1.mapLoc g = ((H.mapLoc g).shift 3 0).1 :=
    congrArg Subtype.val (valMapLoc_shift g 3 0 H)
  simp only [kappa, hndE, ccatchE, Expr.val, Val.lam, Val.prim, Expr.mapLoc] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃]

theorem freeE_mapLoc (g : Loc → Loc) (e : Expr) :
    (freeE e).mapLoc g = freeE (e.mapLoc g) := rfl

theorem kappaC_mapLoc (g : Loc → Loc) (aff : Bool) (ℓ : Loc) (H : Val) (K : Kont) :
    (kappaC aff ℓ H K).mapLoc g = kappaC aff (g ℓ) (H.mapLoc g) (K.mapLoc g) := by
  have h₁ : ((K.shift 3 0).plug (.var 0)).mapLoc g = ((K.mapLoc g).shift 3 0).plug (.var 0) := by
    rw [kont_mapLoc_plug, kont_mapLoc_shift]; rfl
  have h₂ : ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none)))).mapLoc g =
      (((K.mapLoc g).dead.shift 2 0).plug (raiseE (.val (cancelVal none)))) := by
    rw [kont_mapLoc_plug, kont_mapLoc_shift, dead_mapLoc, raiseE_mapLoc]
    congr 2
  have h₃ : (H.shift 3 0).1.mapLoc g = ((H.mapLoc g).shift 3 0).1 :=
    congrArg Subtype.val (valMapLoc_shift g 3 0 H)
  cases aff <;>
  simp only [kappaC, hndE, ccatchE, freeE, stuckE, Expr.val, Val.lam, Val.prim, Val.loc, Val.unit,
    Expr.mapLoc, Bool.false_eq_true, if_true, if_false] at h₁ h₂ h₃ ⊢ <;>
  rw [h₁] <;> (try rw [h₂]) <;> rw [h₃]

theorem kappaCell_mapLoc (g : Loc → Loc) (aff : Bool) (H : Val) (K : Kont) :
    (kappaCell aff H K).mapLoc g = kappaCell aff (H.mapLoc g) (K.mapLoc g) := by
  have h₁ : ((K.shift 4 0).plug (.var 0)).mapLoc g = ((K.mapLoc g).shift 4 0).plug (.var 0) := by
    rw [kont_mapLoc_plug, kont_mapLoc_shift]; rfl
  have h₂ : ((K.dead.shift 3 0).plug (raiseE (.val (cancelVal none)))).mapLoc g =
      (((K.mapLoc g).dead.shift 3 0).plug (raiseE (.val (cancelVal none)))) := by
    rw [kont_mapLoc_plug, kont_mapLoc_shift, dead_mapLoc, raiseE_mapLoc]
    congr 2
  have h₃ : (H.shift 4 0).1.mapLoc g = ((H.mapLoc g).shift 4 0).1 :=
    congrArg Subtype.val (valMapLoc_shift g 4 0 H)
  cases aff <;>
  simp only [kappaCell, kappaCBody, hndE, ccatchE, freeE, stuckE, Expr.val, Val.lam, Val.prim,
    Val.unit, Expr.mapLoc, Bool.false_eq_true, if_true, if_false] at h₁ h₂ h₃ ⊢ <;>
  rw [h₁] <;> (try rw [h₂]) <;> rw [h₃]

theorem kappaAt_mapLoc (g : Loc → Loc) (t : UInt32) (H : Val) (K : Kont) :
    (kappaAt t H K).mapLoc g = kappaAt t (H.mapLoc g) (K.mapLoc g) := by
  unfold kappaAt
  split
  · exact kappaCell_mapLoc g false H K
  · split
    · exact kappaCell_mapLoc g true H K
    · exact kappa_mapLoc g H K

theorem clauseAt_mapLoc (g : Loc → Loc) :
    ∀ (e : Expr) (i : Nat), clauseAt (e.mapLoc g) i = (clauseAt e i).map (Val.mapLoc g)
  | .pair c r, 0 => by
      simp only [Expr.mapLoc, clauseAt]
      by_cases h : IsVal c
      · rw [dif_pos (isVal_mapLoc g h), dif_pos h]; rfl
      · rw [dif_neg (fun h' => h (isVal_of_mapLoc g h')), dif_neg h]; rfl
  | .pair c r, i + 1 => by simp only [Expr.mapLoc, clauseAt]; exact clauseAt_mapLoc g r i
  | .var _, _ | .unit, _ | .inj₁ _, _ | .inj₂ _, _ | .lam _, _ | .loc _, _ | .prim _, _
  | .seq _ _, _ | .letpair _ _, _ | .case _ _ _, _ | .app _ _, _ => rfl

/-! ### The host step, the counted loops and the fuelled fixed point -/

theorem lit?_mapLoc (g : Loc → Loc) (e : Expr) : (e.mapLoc g).lit? = e.lit? := by
  cases e <;> rfl

theorem arg32?_mapLoc (g : Loc → Loc) (e : Expr) : (e.mapLoc g).arg32? = e.arg32? := by
  simp only [Expr.arg32?, lit?_mapLoc]

theorem arg64?_mapLoc (g : Loc → Loc) (e : Expr) : (e.mapLoc g).arg64? = e.arg64? := by
  simp only [Expr.arg64?, lit?_mapLoc]

theorem arg8?_mapLoc (g : Loc → Loc) (e : Expr) : (e.mapLoc g).arg8? = e.arg8? := by
  simp only [Expr.arg8?, lit?_mapLoc]

theorem args32?_mapLoc (g : Loc → Loc) (e : Expr) : (e.mapLoc g).args32? = e.args32? := by
  cases e with
  | pair a b => simp only [Expr.mapLoc, Expr.args32?, arg32?_mapLoc]
  | _ => rfl

theorem args64?_mapLoc (g : Loc → Loc) (e : Expr) : (e.mapLoc g).args64? = e.args64? := by
  cases e with
  | pair a b => simp only [Expr.mapLoc, Expr.args64?, arg64?_mapLoc]
  | _ => rfl

theorem bool_mapLoc (g : Loc → Loc) (b : Bool) : (Val.bool b).mapLoc g = Val.bool b := by
  cases b <;> rfl

theorem opt_mapLoc (g : Loc → Loc) (o : Option Val) (h : ∀ v, o = some v → v.mapLoc g = v) :
    (Val.opt o).mapLoc g = Val.opt o := by
  cases o with
  | none => rfl
  | some v => exact congrArg Val.inj₁ (h v rfl)

set_option linter.unnecessarySeqFocus false in
/-- **The host step reads and answers literals only**: renaming its argument changes nothing, and
renaming fixes its answer. -/
theorem host_call_mapLoc (H : Host) (op : HostOp) (g : Loc → Loc) (v : Val) :
    H.call op (v.mapLoc g) = H.call op v ∧ ∀ r, H.call op v = some r → r.mapLoc g = r := by
  have hv : (v.mapLoc g).1 = v.1.mapLoc g := rfl
  cases op with
  | bin w o => cases w <;> refine ⟨by simp only [Host.call, hv, args32?_mapLoc, args64?_mapLoc],
      ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      first | (obtain ⟨_, _, rfl⟩ := h; rfl) | simp at h
  | div w o => cases w <;> refine ⟨by simp only [Host.call, hv, args32?_mapLoc, args64?_mapLoc],
      ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      first
        | (obtain ⟨_, _, rfl⟩ := h
           exact opt_mapLoc g _ (fun v hv => by
             simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, _, rfl⟩ := hv; rfl))
        | simp at h
  | un w o => cases w <;> refine ⟨by simp only [Host.call, hv, arg32?_mapLoc, arg64?_mapLoc],
      ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      first | (obtain ⟨_, _, rfl⟩ := h; rfl) | simp at h
  | eqz w => cases w <;> refine ⟨by simp only [Host.call, hv, arg32?_mapLoc, arg64?_mapLoc],
      ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      first | (obtain ⟨_, _, rfl⟩ := h; exact bool_mapLoc g _) | simp at h
  | rel w o => cases w <;> refine ⟨by simp only [Host.call, hv, args32?_mapLoc, args64?_mapLoc],
      ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      first | (obtain ⟨_, _, rfl⟩ := h; exact bool_mapLoc g _) | simp at h
  | _ => refine ⟨by simp only [Host.call, hv, arg32?_mapLoc, arg64?_mapLoc, arg8?_mapLoc], ?_⟩ <;>
      intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;> rfl

theorem countNext_mapLoc (g : Loc → Loc) (f : Val) (n i : UInt32) (s : Val) :
    (countNext f n i s).mapLoc g = countNext (f.mapLoc g) n i (s.mapLoc g) := by
  unfold countNext; split_ifs <;> rfl

theorem countTryNext_mapLoc (g : Loc → Loc) (f : Val) (n i : UInt32) (s : Val) :
    (countTryNext f n i s).mapLoc g = countTryNext (f.mapLoc g) n i (s.mapLoc g) := by
  have h : (f.shift 1 0).1.mapLoc g = ((f.mapLoc g).shift 1 0).1 :=
    congrArg Subtype.val (valMapLoc_shift g 1 0 f)
  unfold countTryNext
  split_ifs
  · simp only [Expr.val, Expr.mapLoc] at h ⊢; rw [h]; rfl
  · rfl

theorem fixSelf_mapLoc (g : Loc → Loc) (s : Val) (k : UInt32) :
    (fixSelf s k).mapLoc g = fixSelf (s.mapLoc g) k := by
  have h : (s.shift 1 0).1.mapLoc g = ((s.mapLoc g).shift 1 0).1 :=
    congrArg Subtype.val (valMapLoc_shift g 1 0 s)
  unfold fixSelf
  split_ifs
  · rfl
  · apply Subtype.ext
    simp only [Val.mapLoc, Val.inj₂, Val.lam, Expr.val, Expr.mapLoc] at h ⊢
    rw [h]; rfl

theorem boundedFixNext_mapLoc (g : Loc → Loc) (s : Val) (k : UInt32) (a : Val) :
    (boundedFixNext s k a).mapLoc g = boundedFixNext (s.mapLoc g) k (a.mapLoc g) := by
  have h := congrArg Subtype.val (fixSelf_mapLoc g s k)
  simp only [boundedFixNext, Expr.val, Val.pair, Expr.mapLoc] at h ⊢
  simp only [Val.mapLoc] at h
  rw [h]; rfl

/-! ### The array steps, where the renaming moves blocks -/

theorem tabFill_mapLoc (g : Loc → Loc) (f : Val) (ℓ : Loc) (n : UInt32) :
    ∀ (i k : Nat), (∀ j, j < i + k → g (ℓ + j) = g ℓ + j) →
      (tabFill f ℓ n i k).mapLoc g = tabFill (f.mapLoc g) (g ℓ) n i k
  | _, 0, _ => rfl
  | i, k + 1, h => by
      have ih := tabFill_mapLoc g f ℓ n (i + 1) k (fun j hj => h j (by omega))
      simp only [tabFill, Expr.mapLoc, ih]
      rw [← h i (by omega)]
      rfl

theorem dropFill_mapLoc (g : Loc → Loc) (f : Val) (ℓ : Loc) :
    ∀ (i k : Nat), (∀ j, j < i + k → g (ℓ + j) = g ℓ + j) →
      (dropFill f ℓ i k).mapLoc g = dropFill (f.mapLoc g) (g ℓ) i k
  | _, 0, _ => rfl
  | i, k + 1, h => by
      have ih := dropFill_mapLoc g f ℓ (i + 1) k (fun j hj => h j (by omega))
      simp only [dropFill, Expr.mapLoc, ih]
      rw [← h i (by omega)]
      rfl

theorem idxAns_mapLoc (g : Loc → Loc) (ℓ : Loc) (n i : UInt32)
    (h : i < n → g (ℓ + i.toNat) = g ℓ + i.toNat) :
    (idxAns ℓ n i).mapLoc g = idxAns (g ℓ) n i := by
  unfold idxAns
  split_ifs with hi
  · rw [inj₁_mapLoc, loc_mapLoc, h hi]
  · rfl

theorem splitAns_mapLoc (g : Loc → Loc) (ℓ : Loc) (n i : UInt32)
    (h : i ≤ n → g (ℓ + i.toNat) = g ℓ + i.toNat) :
    (splitAns ℓ n i).mapLoc g = splitAns (g ℓ) n i := by
  unfold splitAns
  split_ifs with hi
  · rw [inj₁_mapLoc, pair_mapLoc, arr_mapLoc, arr_mapLoc, h hi]
  · rfl

/-! ### Heaps moved along a renaming -/

theorem isSome_iff_ne {μ : Heap} {ℓ : Loc} : (μ ℓ).isSome ↔ μ ℓ ≠ none := Option.isSome_iff_ne_none

/-- Where `g` is injective on the live heap, pushing puts the live `ℓ`'s cell, renamed, at `g ℓ`. -/
theorem push_apply_live {g : Loc → Loc} {μ : Heap} (hinj : Set.InjOn g {x | μ x ≠ none})
    {ℓ : Loc} {v : Val} (h : μ ℓ = some v) : Heap.push g μ (g ℓ) = some (v.mapLoc g) := by
  have hex : ∃ ℓ', g ℓ' = g ℓ ∧ (μ ℓ').isSome := ⟨ℓ, rfl, by simp [h]⟩
  unfold Heap.push
  rw [dif_pos hex]
  obtain ⟨h₁, h₂⟩ := Classical.choose_spec hex
  have hc : Classical.choose hex = ℓ :=
    hinj (isSome_iff_ne.mp h₂) (show μ ℓ ≠ none by simp [h]) h₁
  rw [hc, h]; rfl

/-- Pushing puts nothing where no live cell is sent. -/
theorem push_apply_none {g : Loc → Loc} {μ : Heap} {x : Loc} (h : ∀ ℓ, μ ℓ ≠ none → g ℓ ≠ x) :
    Heap.push g μ x = none := by
  unfold Heap.push
  rw [dif_neg]
  rintro ⟨ℓ, h₁, h₂⟩
  exact h ℓ (isSome_iff_ne.mp h₂) h₁

/-- The pushed heap is live exactly at the images of the live heap. -/
theorem push_ne_none {g : Loc → Loc} {μ : Heap} {x : Loc} :
    Heap.push g μ x ≠ none ↔ ∃ ℓ, μ ℓ ≠ none ∧ g ℓ = x := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact h (push_apply_none fun ℓ hℓ e => hn ℓ hℓ e)
  · rintro ⟨ℓ, hℓ, rfl⟩
    have hs := push_isSome (g := g) (μ := μ) (ℓ := ℓ) (isSome_iff_ne.mpr hℓ)
    exact isSome_iff_ne.mp hs

/-- **A heap is a pushed heap** when it holds each live cell, renamed, at its image, and nothing
where no live cell is sent; `g` injective on the live heap. -/
theorem push_eq_of {g : Loc → Loc} {μ ν : Heap} (hinj : Set.InjOn g {x | μ x ≠ none})
    (hl : ∀ ℓ v, μ ℓ = some v → ν (g ℓ) = some (v.mapLoc g))
    (hn : ∀ x, (∀ ℓ, μ ℓ ≠ none → g ℓ ≠ x) → ν x = none) : Heap.push g μ = ν := by
  funext x
  by_cases hx : ∃ ℓ, μ ℓ ≠ none ∧ g ℓ = x
  · obtain ⟨ℓ, hℓ, rfl⟩ := hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hℓ
    rw [push_apply_live hinj hv, hl ℓ v hv]
  · push Not at hx
    rw [push_apply_none hx, hn x hx]

/-- The locations a heap's stored values mention. -/
def StoredLoc (μ : Heap) (ℓ : Loc) : Prop := ∃ m v, μ m = some v ∧ v.1.MentionsLoc ℓ

/-- `free`, pushed. -/
theorem push_del {g : Loc → Loc} {μ : Heap} (hinj : Set.InjOn g {x | μ x ≠ none}) {ℓ : Loc}
    (hℓ : μ ℓ ≠ none) : Heap.push g (μ.del ℓ) = (Heap.push g μ).del (g ℓ) := by
  have hinj' : Set.InjOn g {x | μ.del ℓ x ≠ none} := fun x hx y hy e => by
    have hx' : μ x ≠ none := by
      by_cases h : x = ℓ
      · subst h; simp at hx
      · simpa [Heap.del_other h] using hx
    have hy' : μ y ≠ none := by
      by_cases h : y = ℓ
      · subst h; simp at hy
      · simpa [Heap.del_other h] using hy
    exact hinj hx' hy' e
  refine push_eq_of hinj' (fun x v hx => ?_) (fun x hx => ?_)
  · have hxl : x ≠ ℓ := by rintro rfl; simp at hx
    rw [Heap.del_other hxl] at hx
    have hne : g x ≠ g ℓ := fun e => hxl (hinj (by simp [hx]) hℓ e)
    rw [Heap.del_other hne, push_apply_live hinj hx]
  · by_cases hxl : x = g ℓ
    · subst hxl; simp
    · rw [Heap.del_other hxl]
      refine push_apply_none fun y hy e => hx y ?_ e
      by_cases hyl : y = ℓ
      · subst hyl; exact absurd e.symm hxl
      · rwa [Heap.del_other hyl]

/-- `store`, at a live cell, pushed. -/
theorem push_upd_live {g : Loc → Loc} {μ : Heap} (hinj : Set.InjOn g {x | μ x ≠ none}) {ℓ : Loc}
    (hℓ : μ ℓ ≠ none) (v : Val) :
    Heap.push g (μ.upd ℓ v) = (Heap.push g μ).upd (g ℓ) (v.mapLoc g) := by
  have hdom : ∀ x, μ.upd ℓ v x ≠ none ↔ μ x ≠ none := fun x => by
    by_cases h : x = ℓ
    · subst h; simp [hℓ]
    · rw [Heap.upd_other h]
  have hinj' : Set.InjOn g {x | μ.upd ℓ v x ≠ none} := fun x hx y hy e =>
    hinj ((hdom x).mp hx) ((hdom y).mp hy) e
  refine push_eq_of hinj' (fun x w hx => ?_) (fun x hx => ?_)
  · by_cases hxl : x = ℓ
    · subst hxl; simp only [Heap.upd_same] at hx ⊢; cases hx; rfl
    · rw [Heap.upd_other hxl] at hx
      have hne : g x ≠ g ℓ := fun e => hxl (hinj (by simp [hx]) hℓ e)
      rw [Heap.upd_other hne, push_apply_live hinj hx]
  · have hxl : x ≠ g ℓ := fun e => hx ℓ ((hdom ℓ).mpr hℓ) e.symm
    rw [Heap.upd_other hxl]
    exact push_apply_none fun y hy e => hx y ((hdom y).mpr hy) e

/-- An allocation at a fresh `ℓB`, sent to `ℓA` where no live cell is sent, pushed along a renaming
that agrees with `g` on the live heap and the stored values. -/
theorem push_upd_fresh {g g' : Loc → Loc} {μ : Heap} (hinj : Set.InjOn g {x | μ x ≠ none})
    {ℓB ℓA : Loc} (hB : μ ℓB = none) (hA : ∀ x, μ x ≠ none → g x ≠ ℓA) (hgB : g' ℓB = ℓA)
    (hl : ∀ x, μ x ≠ none → g' x = g x) (hs : ∀ x, StoredLoc μ x → g' x = g x) (v : Val) :
    Heap.push g' (μ.upd ℓB v) = (Heap.push g μ).upd ℓA (v.mapLoc g') ∧
      Set.InjOn g' {x | μ.upd ℓB v x ≠ none} := by
  have hinj' : Set.InjOn g' {x | μ.upd ℓB v x ≠ none} := by
    intro x hx y hy e
    change μ.upd ℓB v x ≠ none at hx
    change μ.upd ℓB v y ≠ none at hy
    by_cases hx' : x = ℓB <;> by_cases hy' : y = ℓB
    · rw [hx', hy']
    · rw [Heap.upd_other hy'] at hy
      rw [hx', hgB, hl y hy] at e; exact absurd e.symm (hA y hy)
    · rw [Heap.upd_other hx'] at hx
      rw [hy', hgB, hl x hx] at e; exact absurd e (hA x hx)
    · rw [Heap.upd_other hx'] at hx
      rw [Heap.upd_other hy'] at hy
      rw [hl x hx, hl y hy] at e; exact hinj hx hy e
  refine ⟨push_eq_of hinj' (fun x w hx => ?_) (fun x hx => ?_), hinj'⟩
  · by_cases hxB : x = ℓB
    · subst hxB; simp only [Heap.upd_same] at hx; cases hx; rw [hgB, Heap.upd_same]
    · rw [Heap.upd_other hxB] at hx
      have hxl : μ x ≠ none := by simp [hx]
      rw [hl x hxl, Heap.upd_other (hA x hxl), push_apply_live hinj hx]
      congr 1
      exact valMapLoc_congr w fun y hy => (hs y ⟨x, w, hx, hy⟩).symm
  · have hxA : x ≠ ℓA := fun e => hx ℓB (by simp) (by rw [hgB, e])
    rw [Heap.upd_other hxA]
    refine push_apply_none fun y hy e => ?_
    have hyB : y ≠ ℓB := by rintro rfl; exact hy hB
    exact hx y (by rwa [Heap.upd_other hyB]) (by rw [hl y hy, e])

/-- A block allocation at a fresh `[ℓB, ℓB + n)`, sent to `[ℓA, ℓA + n)` where no live cell is
sent, pushed along a renaming that agrees with `g` on the live heap and the stored values. -/
theorem push_fill_fresh {g g' : Loc → Loc} {μ : Heap} (hinj : Set.InjOn g {x | μ x ≠ none})
    {ℓB ℓA : Loc} {n : Nat} (hB : ∀ j, j < n → μ (ℓB + j) = none)
    (hA : ∀ x, μ x ≠ none → ∀ j, j < n → g x ≠ ℓA + j) (hgB : ∀ j, j < n → g' (ℓB + j) = ℓA + j)
    (hl : ∀ x, μ x ≠ none → g' x = g x) (hs : ∀ x, StoredLoc μ x → g' x = g x) :
    Heap.push g' (μ.fill ℓB n .unit) = (Heap.push g μ).fill ℓA n .unit ∧
      Set.InjOn g' {x | μ.fill ℓB n .unit x ≠ none} := by
  have hin : ∀ x, (ℓB ≤ x ∧ x < ℓB + n) → ∃ j, j < n ∧ x = ℓB + j := fun x hx =>
    ⟨x - ℓB, by lomega, by lomega⟩
  have hinj' : Set.InjOn g' {x | μ.fill ℓB n .unit x ≠ none} := by
    intro x hx y hy e
    simp only [Set.mem_ofPred_eq, Heap.fill] at hx hy
    by_cases hx' : ℓB ≤ x ∧ x < ℓB + n <;> by_cases hy' : ℓB ≤ y ∧ y < ℓB + n
    · obtain ⟨j, hj, rfl⟩ := hin x hx'
      obtain ⟨j', hj', rfl⟩ := hin y hy'
      rw [hgB j hj, hgB j' hj'] at e; lomega
    · rw [if_neg hy'] at hy
      obtain ⟨j, hj, rfl⟩ := hin x hx'
      rw [hgB j hj, hl y hy] at e; exact absurd e.symm (hA y hy j hj)
    · rw [if_neg hx'] at hx
      obtain ⟨j, hj, rfl⟩ := hin y hy'
      rw [hgB j hj, hl x hx] at e; exact absurd e (hA x hx j hj)
    · rw [if_neg hx'] at hx
      rw [if_neg hy'] at hy
      rw [hl x hx, hl y hy] at e; exact hinj hx hy e
  refine ⟨push_eq_of hinj' (fun x w hx => ?_) (fun x hx => ?_), hinj'⟩
  · by_cases hx' : ℓB ≤ x ∧ x < ℓB + n
    · obtain ⟨j, hj, rfl⟩ := hin _ hx'
      simp only [Heap.fill, if_pos hx'] at hx
      cases hx
      rw [hgB j hj]
      simp only [Heap.fill]
      rw [if_pos (by lomega)]; rfl
    · simp only [Heap.fill, if_neg hx'] at hx
      have hxl : μ x ≠ none := by simp [hx]
      have hnot : ¬ (ℓA ≤ g x ∧ g x < ℓA + n) := fun h =>
        hA x hxl (g x - ℓA) (by lomega) (by lomega)
      rw [hl x hxl]
      simp only [Heap.fill, if_neg hnot]
      rw [push_apply_live hinj hx]
      congr 1
      exact valMapLoc_congr w fun y hy => (hs y ⟨x, w, hx, hy⟩).symm
  · have hxA : ¬ (ℓA ≤ x ∧ x < ℓA + n) := fun h => by
      have := hx (ℓB + (x - ℓA)) (by
        simp only [Heap.fill]; rw [if_pos (by lomega)]; simp)
      exact this (by rw [hgB _ (by lomega)]; lomega)
    simp only [Heap.fill, if_neg hxA]
    refine push_apply_none fun y hy e => ?_
    have hyB : ¬ (ℓB ≤ y ∧ y < ℓB + n) := fun h => by
      obtain ⟨j, hj, rfl⟩ := hin y h; exact hy (hB j hj)
    exact hx y (by simp only [Heap.fill, if_neg hyB]; exact hy) (by rw [hl y hy, e])

/-! ### A head step, renamed -/

/-- **A renamed redex is a redex**: it steps at some memory.  So it is the redex of every step of
the renamed term (`plug_decomp`). -/
theorem head_mapLoc_exists (g : Loc → Loc) {μ μ' : Heap} {b b' : Expr}
    (h : Head (ℍ := ℍ) μ b μ' b') : ∃ μ₂ μ₂' b₂, Head (ℍ := ℍ) μ₂ (b.mapLoc g) μ₂' b₂ := by
  cases h with
  | beta b v => exact ⟨_, _, _, Head.beta μ (b.mapLoc g) (v.mapLoc g)⟩
  | alloc v ℓ _ => exact ⟨_, _, _, Head.alloc Adequacy.emptyMem (v.mapLoc g) 0 rfl⟩
  | free ℓ v _ =>
      exact ⟨_, _, _, Head.free (Adequacy.emptyMem.upd (g ℓ) Val.unit) (g ℓ) Val.unit
        (Heap.upd_same _ _ _)⟩
  | load ℓ v _ =>
      exact ⟨_, _, _, Head.load (Adequacy.emptyMem.upd (g ℓ) Val.unit) (g ℓ) Val.unit
        (Heap.upd_same _ _ _)⟩
  | store ℓ v w _ =>
      exact ⟨_, _, _, Head.store (Adequacy.emptyMem.upd (g ℓ) Val.unit) (g ℓ) (v.mapLoc g) Val.unit
        (Heap.upd_same _ _ _)⟩
  | seq => exact ⟨_, _, _, Head.seq μ (b'.mapLoc g)⟩
  | letpair v₁ v₂ e => exact ⟨_, _, _, Head.letpair μ (v₁.mapLoc g) (v₂.mapLoc g) (e.mapLoc g)⟩
  | case₁ v e₁ e₂ => exact ⟨_, _, _, Head.case₁ μ (v.mapLoc g) (e₁.mapLoc g) (e₂.mapLoc g)⟩
  | case₂ v e₁ e₂ => exact ⟨_, _, _, Head.case₂ μ (v.mapLoc g) (e₁.mapLoc g) (e₂.mapLoc g)⟩
  | host op v r hr =>
      exact ⟨_, _, _, Head.host μ op (v.mapLoc g) r ((host_call_mapLoc ℍ op g v).1.trans hr)⟩
  | tab c f ℓ _ => exact ⟨_, _, _, Head.tab Adequacy.emptyMem c (f.mapLoc g) 0 (fun _ _ => rfl)⟩
  | idx ℓ n i => exact ⟨_, _, _, Head.idx μ (g ℓ) n i⟩
  | split ℓ n i => exact ⟨_, _, _, Head.split μ (g ℓ) n i⟩
  | drop f ℓ n => exact ⟨_, _, _, Head.drop μ (f.mapLoc g) (g ℓ) n⟩
  | count f n i s => exact ⟨_, _, _, Head.count μ (f.mapLoc g) n i (s.mapLoc g)⟩
  | countTry f n i s => exact ⟨_, _, _, Head.countTry μ (f.mapLoc g) n i (s.mapLoc g)⟩
  | boundedFix s k a => exact ⟨_, _, _, Head.boundedFix μ (s.mapLoc g) k (a.mapLoc g)⟩
  | hret n qs hr hs w =>
      exact ⟨_, _, _, Head.hret μ n (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) (w.mapLoc g)⟩
  | hop n i qs hr hs c v K hc hK =>
      rw [hndE_mapLoc, hndVal_mapLoc, kont_mapLoc_plug, performE_mapLoc]
      exact ⟨_, _, _, Head.hop μ n i (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) (c.mapLoc g)
        (v.mapLoc g) (K.mapLoc g)
        (by rw [show (hs.mapLoc g).1 = hs.1.mapLoc g from rfl, clauseAt_mapLoc, hc]; rfl)
        (by rw [hasHnd_mapLoc, hK])⟩
  | hunwind n i qs hr hs c v K hc hK =>
      rw [hndE_mapLoc, hndVal_mapLoc, kont_mapLoc_plug, raiseE_mapLoc]
      exact ⟨_, _, _, Head.hunwind μ n i (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) (c.mapLoc g)
        (v.mapLoc g) (K.mapLoc g)
        (by rw [show (hs.mapLoc g).1 = hs.1.mapLoc g from rfl, clauseAt_mapLoc, hc]; rfl)
        (by rw [catches_mapLoc, hK])⟩
  | uthen N D w => exact ⟨_, _, _, Head.uthen μ (N.mapLoc g) (D.mapLoc g) (w.mapLoc g)⟩
  | ufin N D n i v K hn hK =>
      rw [ubindE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc]
      exact ⟨_, _, _, Head.ufin μ (N.mapLoc g) (D.mapLoc g) n i (v.mapLoc g) (K.mapLoc g) hn
        (by rw [catches_mapLoc, hK])⟩
  | ufinC N D err K hK =>
      rw [ubindE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc,
        show (Expr.val (cancelVal err)).mapLoc g = Expr.val (cancelVal (err.map (Val.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g err)]
      exact ⟨_, _, _, Head.ufinC μ (N.mapLoc g) (D.mapLoc g) (err.map (Val.mapLoc g))
        (K.mapLoc g) (by rw [catches_mapLoc, hK])⟩
  | cfret err w =>
      rw [cfinE_mapLoc, cancelVal_mapLoc]
      exact ⟨_, _, _, Head.cfret μ (err.map (Val.mapLoc g)) (w.mapLoc g)⟩
  | cferr err m j w K hm hK =>
      rw [cfinE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc, cancelVal_mapLoc]
      exact ⟨_, _, _, Head.cferr μ (err.map (Val.mapLoc g)) m j (w.mapLoc g) (K.mapLoc g) hm
        (by rw [catches_mapLoc, hK])⟩
  | cfcancel err err' K hK =>
      rw [cfinE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc, cancelVal_mapLoc,
        show (Expr.val (cancelVal err')).mapLoc g = Expr.val (cancelVal (err'.map (Val.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g err')]
      exact ⟨_, _, _, Head.cfcancel μ (err.map (Val.mapLoc g)) (err'.map (Val.mapLoc g))
        (K.mapLoc g) (by rw [catches_mapLoc, hK])⟩
  | cancel K hK =>
      rw [ccatchE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc,
        show (Expr.val (cancelVal none)).mapLoc g = Expr.val (cancelVal none)
          from congrArg Subtype.val (cancelVal_mapLoc g none)]
      exact ⟨_, _, _, Head.cancel μ (K.mapLoc g) (by rw [catches_mapLoc, hK])⟩
  | creraise E K hK =>
      rw [ccatchE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc,
        show (Expr.val (cancelVal (some E))).mapLoc g = Expr.val (cancelVal (some (E.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g (some E))]
      exact ⟨_, _, _, Head.creraise μ (E.mapLoc g) (K.mapLoc g) (by rw [catches_mapLoc, hK])⟩

/-- `g` moves the window of the array steps' offsets, `[ℓ, ℓ + 2³²)`, above each location the redex
mentions as a block. -/
def AffineAt (g : Loc → Loc) (b : Expr) : Prop :=
  ∀ ℓ i, b.MentionsLoc ℓ → i < 2 ^ 32 → g (ℓ + i) = g ℓ + i

/-- The array redexes' base locations. -/
theorem mentions_arrRedex {p : Prim} {ℓ : Loc} {n : UInt32} {w : Val} :
    (Expr.app (.val (.prim p)) (.val (.pair (.arr ℓ n) w))).MentionsLoc ℓ :=
  Or.inr (Or.inl (Or.inl rfl))

theorem mentions_dropRedex {f : Val} {ℓ : Loc} {n : UInt32} :
    (Expr.app (.val (.prim .drop)) (.val (.pair f (.arr ℓ n)))).MentionsLoc ℓ :=
  Or.inr (Or.inr (Or.inl rfl))

/-- **A head step that allocates nothing, renamed, is a head step** of the pushed memory, where
`g` is injective on the live heap and moves the array steps' offsets as blocks. -/
theorem head_image {g : Loc → Loc} {μ μ' : Heap} {b b' : Expr} (h : Head (ℍ := ℍ) μ b μ' b')
    (hn : b.allocs = false) (hinj : Set.InjOn g {x | μ x ≠ none}) (haff : AffineAt g b) :
    Head (ℍ := ℍ) (Heap.push g μ) (b.mapLoc g) (Heap.push g μ') (b'.mapLoc g) := by
  cases h with
  | beta b v =>
      rw [mapLoc_subst]
      exact Head.beta _ (b.mapLoc g) (v.mapLoc g)
  | alloc v ℓ _ => simp [Expr.allocs] at hn
  | tab c f ℓ _ => simp [Expr.allocs] at hn
  | free ℓ v hℓ =>
      rw [push_del hinj (by simp [hℓ])]
      exact Head.free _ (g ℓ) (v.mapLoc g) (push_apply_live hinj hℓ)
  | load ℓ v hℓ => exact Head.load _ (g ℓ) (v.mapLoc g) (push_apply_live hinj hℓ)
  | store ℓ v w hℓ =>
      rw [push_upd_live hinj (by simp [hℓ]) v]
      exact Head.store _ (g ℓ) (v.mapLoc g) (w.mapLoc g) (push_apply_live hinj hℓ)
  | seq => exact Head.seq _ (b'.mapLoc g)
  | letpair v₁ v₂ e =>
      rw [mapLoc_subst, mapLoc_subst, valMapLoc_shift]
      exact Head.letpair _ (v₁.mapLoc g) (v₂.mapLoc g) (e.mapLoc g)
  | case₁ v e₁ e₂ =>
      rw [mapLoc_subst]
      exact Head.case₁ _ (v.mapLoc g) (e₁.mapLoc g) (e₂.mapLoc g)
  | case₂ v e₁ e₂ =>
      rw [mapLoc_subst]
      exact Head.case₂ _ (v.mapLoc g) (e₁.mapLoc g) (e₂.mapLoc g)
  | host op v r hr =>
      obtain ⟨h₁, h₂⟩ := host_call_mapLoc ℍ op g v
      rw [show (Expr.val r).mapLoc g = Expr.val r from congrArg Subtype.val (h₂ r hr)]
      exact Head.host _ op (v.mapLoc g) r (h₁.trans hr)
  | idx ℓ n i =>
      rw [show (Expr.val (idxAns ℓ n i)).mapLoc g = Expr.val (idxAns (g ℓ) n i) from
        congrArg Subtype.val (idxAns_mapLoc g ℓ n i
          (fun _ => haff ℓ i.toNat mentions_arrRedex (UInt32.toNat_lt i)))]
      exact Head.idx _ (g ℓ) n i
  | split ℓ n i =>
      rw [show (Expr.val (splitAns ℓ n i)).mapLoc g = Expr.val (splitAns (g ℓ) n i) from
        congrArg Subtype.val (splitAns_mapLoc g ℓ n i
          (fun _ => haff ℓ i.toNat mentions_arrRedex (UInt32.toNat_lt i)))]
      exact Head.split _ (g ℓ) n i
  | drop f ℓ n =>
      rw [dropFill_mapLoc g f ℓ 0 n.toNat (fun j hj => haff ℓ j mentions_dropRedex
        (lt_trans (by simpa using hj) (UInt32.toNat_lt n)))]
      exact Head.drop _ (f.mapLoc g) (g ℓ) n
  | count f n i s =>
      rw [countNext_mapLoc]
      exact Head.count _ (f.mapLoc g) n i (s.mapLoc g)
  | countTry f n i s =>
      rw [countTryNext_mapLoc]
      exact Head.countTry _ (f.mapLoc g) n i (s.mapLoc g)
  | boundedFix s k a =>
      rw [boundedFixNext_mapLoc]
      exact Head.boundedFix _ (s.mapLoc g) k (a.mapLoc g)
  | hret n qs hr hs w => exact Head.hret _ n (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) (w.mapLoc g)
  | hop n i qs hr hs c v K hc hK =>
      rw [hndE_mapLoc, hndVal_mapLoc, kont_mapLoc_plug, performE_mapLoc,
        show (Expr.app (.val c) (.pair (.val v)
            (kappaAt (capTag qs.1 i.toNat) (hndVal n qs hr hs) K))).mapLoc g =
          .app (.val (c.mapLoc g)) (.pair (.val (v.mapLoc g))
            (kappaAt (capTag (qs.mapLoc g).1 i.toNat)
              (hndVal n (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g)) (K.mapLoc g))) from by
          simp only [Expr.mapLoc, kappaAt_mapLoc, hndVal_mapLoc]
          rw [show (qs.mapLoc g).1 = qs.1.mapLoc g from rfl, capTag_mapLoc]; rfl]
      exact Head.hop _ n i (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) (c.mapLoc g) (v.mapLoc g)
        (K.mapLoc g)
        (by rw [show (hs.mapLoc g).1 = hs.1.mapLoc g from rfl, clauseAt_mapLoc, hc]; rfl)
        (by rw [hasHnd_mapLoc, hK])
  | hunwind n i qs hr hs c v K hc hK =>
      rw [hndE_mapLoc, hndVal_mapLoc, kont_mapLoc_plug, raiseE_mapLoc]
      exact Head.hunwind _ n i (qs.mapLoc g) (hr.mapLoc g) (hs.mapLoc g) (c.mapLoc g) (v.mapLoc g)
        (K.mapLoc g)
        (by rw [show (hs.mapLoc g).1 = hs.1.mapLoc g from rfl, clauseAt_mapLoc, hc]; rfl)
        (by rw [catches_mapLoc, hK])
  | uthen N D w => exact Head.uthen _ (N.mapLoc g) (D.mapLoc g) (w.mapLoc g)
  | ufin N D n i v K hn' hK =>
      rw [ubindE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc]
      exact Head.ufin _ (N.mapLoc g) (D.mapLoc g) n i (v.mapLoc g) (K.mapLoc g) hn'
        (by rw [catches_mapLoc, hK])
  | ufinC N D err K hK =>
      rw [ubindE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc, cfinE_mapLoc,
        show (Expr.val (cancelVal err)).mapLoc g = Expr.val (cancelVal (err.map (Val.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g err), cancelVal_mapLoc]
      exact Head.ufinC _ (N.mapLoc g) (D.mapLoc g) (err.map (Val.mapLoc g)) (K.mapLoc g)
        (by rw [catches_mapLoc, hK])
  | cfret err w =>
      rw [cfinE_mapLoc, raiseE_mapLoc, cancelVal_mapLoc,
        show (Expr.val (cancelVal err)).mapLoc g = Expr.val (cancelVal (err.map (Val.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g err)]
      exact Head.cfret _ (err.map (Val.mapLoc g)) (w.mapLoc g)
  | cferr err m j w K hm hK =>
      rw [cfinE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc, raiseE_mapLoc, cancelVal_mapLoc,
        show (Expr.val (cancelVal (errNext err m j w))).mapLoc g =
          Expr.val (cancelVal (errNext (err.map (Val.mapLoc g)) m j (w.mapLoc g))) from by
          rw [← errNext_mapLoc]; exact congrArg Subtype.val (cancelVal_mapLoc g _)]
      exact Head.cferr _ (err.map (Val.mapLoc g)) m j (w.mapLoc g) (K.mapLoc g) hm
        (by rw [catches_mapLoc, hK])
  | cfcancel err err' K hK =>
      rw [cfinE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc, raiseE_mapLoc, cancelVal_mapLoc,
        show (Expr.val (cancelVal err')).mapLoc g = Expr.val (cancelVal (err'.map (Val.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g err'),
        show (Expr.val (cancelVal (err.or err'))).mapLoc g =
          Expr.val (cancelVal ((err.map (Val.mapLoc g)).or (err'.map (Val.mapLoc g)))) from by
          rw [← or_mapLoc]; exact congrArg Subtype.val (cancelVal_mapLoc g _)]
      exact Head.cfcancel _ (err.map (Val.mapLoc g)) (err'.map (Val.mapLoc g)) (K.mapLoc g)
        (by rw [catches_mapLoc, hK])
  | cancel K hK =>
      rw [ccatchE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc,
        show (Expr.val (cancelVal none)).mapLoc g = Expr.val (cancelVal none)
          from congrArg Subtype.val (cancelVal_mapLoc g none)]
      exact Head.cancel _ (K.mapLoc g) (by rw [catches_mapLoc, hK])
  | creraise E K hK =>
      rw [ccatchE_mapLoc, kont_mapLoc_plug, raiseE_mapLoc, raiseE_mapLoc,
        show (Expr.val (cancelVal (some E))).mapLoc g = Expr.val (cancelVal (some (E.mapLoc g)))
          from congrArg Subtype.val (cancelVal_mapLoc g (some E))]
      exact Head.creraise _ (E.mapLoc g) (K.mapLoc g) (by rw [catches_mapLoc, hK])

/-! ### The given run's allocations -/

theorem head_alloc_inv {μ μ' : Heap} {v : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.prim .alloc)) (.val v)) μ' a') :
    ∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ v ∧ a' = .val (.loc ℓ) := by
  generalize hb : Expr.app (.val (.prim .alloc)) (.val v) = b at h
  cases h with
  | alloc w ℓ hℓ =>
      simp only [Expr.val, Val.prim, Expr.app.injEq, true_and] at hb
      obtain rfl : v = w := Subtype.ext hb
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim]

theorem head_tab_inv {μ μ' : Heap} {c : UInt32} {f : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f))) μ' a') :
    ∃ ℓ, (∀ i, i < (arrLen c).toNat → μ (ℓ + i) = none) ∧
      μ' = μ.fill ℓ (arrLen c).toNat .unit ∧ a' = tabFill f ℓ (arrLen c) 0 (arrLen c).toNat := by
  generalize hb : Expr.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)) = b at h
  cases h with
  | tab c' f' ℓ hℓ =>
      simp only [Expr.val, Val.prim, Val.pair, Val.i32, Expr.app.injEq, Expr.pair.injEq,
        Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq, true_and] at hb
      obtain ⟨rfl, hf⟩ := hb
      obtain rfl : f = f' := Subtype.ext hf
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim]

/-! ### What a step's result names -/

/-- A term every renaming fixes mentions no location. -/
theorem noLoc_of_fixed {e : Expr} (h : ∀ g : Loc → Loc, e.mapLoc g = e) :
    ∀ x, ¬ e.MentionsLoc x := by
  intro x hx
  have h₁ : (e.mapLoc (fun _ => x + 1)).MentionsLoc x := by rw [h]; exact hx
  obtain ⟨ℓ, -, hℓ⟩ := (mentionsLoc_mapLoc e).mp h₁
  exact absurd hℓ (by lomega)

theorem mentionsLoc_kshift {x : Loc} (d c : Nat) (K : Kont) :
    ((K.shift d c).plug .unit).MentionsLoc x ↔ (K.plug .unit).MentionsLoc x := by
  induction K generalizing c with
  | hole => exact Iff.rfl
  | pairL K e ih | seq K e ih =>
      simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih, mentionsLoc_shift]
  | letpair K e ih => simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih, mentionsLoc_shift]
  | pairR v K ih =>
      simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih, Val.val_shift, mentionsLoc_shift]
  | appR f K ih => simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih, mentionsLoc_shift]
  | appL K v ih =>
      simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih, Val.val_shift, mentionsLoc_shift]
  | case K e₁ e₂ ih => simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih, mentionsLoc_shift]
  | inj₁ K ih | inj₂ K ih => simp only [Kont.shift, Kont.plug, Expr.MentionsLoc, ih]

/-- A dead region names only locations its region names. -/
theorem mentionsLoc_dead {x : Loc} : ∀ (K : Kont), (K.dead.plug .unit).MentionsLoc x →
    (K.plug .unit).MentionsLoc x
  | .hole, h => h
  | .appR f K, h => by
      simp only [Kont.dead] at h
      split at h
      · exact Or.inr (mentionsLoc_dead K h)
      · simp only [Kont.plug, Expr.MentionsLoc] at h ⊢
        exact h.imp id (mentionsLoc_dead K)
  | .pairL K _, h | .letpair K _, h | .seq K _, h => by
      simp only [Kont.dead, Kont.plug, Expr.MentionsLoc] at h ⊢
      exact h.imp (mentionsLoc_dead K) id
  | .pairR _ K, h => by
      simp only [Kont.dead, Kont.plug, Expr.MentionsLoc] at h ⊢
      exact h.imp id (mentionsLoc_dead K)
  | .appL K _, h => by
      simp only [Kont.dead, Kont.plug, Expr.MentionsLoc] at h ⊢
      exact h.imp (mentionsLoc_dead K) id
  | .case K _ _, h => by
      simp only [Kont.dead, Kont.plug, Expr.MentionsLoc] at h ⊢
      exact h.imp (mentionsLoc_dead K) id
  | .inj₁ K, h | .inj₂ K, h => by
      simp only [Kont.dead, Kont.plug, Expr.MentionsLoc] at h ⊢
      exact mentionsLoc_dead K h

theorem mentionsLoc_cancelVal {x : Loc} {err : Option Val}
    (h : (cancelVal err).1.MentionsLoc x) : ∃ E, err = some E ∧ E.1.MentionsLoc x := by
  simp only [cancelVal, opPayload, Val.pair, Val.i32, Expr.MentionsLoc, false_or] at h
  cases err with
  | none => simp [errVal, Val.inj₁, Val.unit, Expr.MentionsLoc] at h
  | some E => exact ⟨E, rfl, h⟩

theorem mentionsLoc_errNext {x : Loc} {err : Option Val} {m j : UInt32} {w E : Val}
    (he : errNext err m j w = some E) (h : E.1.MentionsLoc x) :
    (∃ E', err = some E' ∧ E'.1.MentionsLoc x) ∨ w.1.MentionsLoc x := by
  cases err with
  | some E' => simp only [errNext, Option.some_or, Option.some.injEq] at he; subst he; exact .inl ⟨_, rfl, h⟩
  | none =>
      simp only [errNext, Option.none_or, Option.some.injEq] at he
      subst he
      simp only [opPayload, Val.pair, Val.i32, Expr.MentionsLoc, false_or] at h
      exact .inr h

theorem mentionsLoc_kappa {x : Loc} {H : Val} {K : Kont}
    (h : (kappa H K).MentionsLoc x) : H.1.MentionsLoc x ∨ (K.plug .unit).MentionsLoc x := by
  simp only [kappa, hndE, ccatchE, raiseE, Expr.val, Val.lam, Val.prim, Expr.MentionsLoc,
    false_or] at h
  rcases h with h | h
  · rcases h with h | h
    · exact .inl ((mentionsLoc_shift 3 0 H.1).mp h)
    · rcases (mentionsLoc_plug _ _).mp h with h | h
      · exact .inr ((mentionsLoc_kshift 3 0 K).mp h)
      · exact h.elim
  · rcases (mentionsLoc_plug _ _).mp h with h | h
    · exact .inr (mentionsLoc_dead K ((mentionsLoc_kshift 2 0 K.dead).mp h))
    · simp only [Expr.MentionsLoc, false_or] at h
      obtain ⟨E, hE, -⟩ := mentionsLoc_cancelVal h
      cases hE

theorem mentionsLoc_kappaCell {x : Loc} {aff : Bool} {H : Val} {K : Kont}
    (h : (kappaCell aff H K).MentionsLoc x) : H.1.MentionsLoc x ∨ (K.plug .unit).MentionsLoc x := by
  cases aff <;>
  simp only [kappaCell, kappaCBody, hndE, ccatchE, raiseE, freeE, stuckE, Expr.val, Val.lam,
    Val.prim, Val.unit, Expr.MentionsLoc, false_or, or_false, Bool.false_eq_true, if_true,
    if_false] at h
  · rcases h with h | h
    · exact .inl ((mentionsLoc_shift 4 0 H.1).mp h)
    · rcases (mentionsLoc_plug _ _).mp h with h | h
      · exact .inr ((mentionsLoc_kshift 4 0 K).mp h)
      · exact h.elim
  · rcases h with (h | h) | h
    · exact .inl ((mentionsLoc_shift 4 0 H.1).mp h)
    · rcases (mentionsLoc_plug _ _).mp h with h | h
      · exact .inr ((mentionsLoc_kshift 4 0 K).mp h)
      · exact h.elim
    · rcases (mentionsLoc_plug _ _).mp h with h | h
      · exact .inr (mentionsLoc_dead K ((mentionsLoc_kshift 3 0 K.dead).mp h))
      · simp only [Expr.MentionsLoc, false_or] at h
        obtain ⟨E, hE, -⟩ := mentionsLoc_cancelVal h
        cases hE

theorem mentionsLoc_kappaAt {x : Loc} {t : UInt32} {H : Val} {K : Kont}
    (h : (kappaAt t H K).MentionsLoc x) : H.1.MentionsLoc x ∨ (K.plug .unit).MentionsLoc x := by
  unfold kappaAt at h
  split at h
  · exact mentionsLoc_kappaCell h
  · split at h
    · exact mentionsLoc_kappaCell h
    · exact mentionsLoc_kappa h

theorem mentionsLoc_clauseAt {x : Loc} : ∀ {e : Expr} {i : Nat} {c : Val},
    clauseAt e i = some c → c.1.MentionsLoc x → e.MentionsLoc x
  | .pair c' r, 0, c, h, hx => by
      simp only [clauseAt] at h
      split_ifs at h with hv
      cases h
      exact .inl hx
  | .pair c' r, i + 1, c, h, hx => .inr (mentionsLoc_clauseAt (e := r) (i := i) h hx)
  | .var _, _, _, h, _ | .unit, _, _, h, _ | .inj₁ _, _, _, h, _ | .inj₂ _, _, _, h, _
  | .lam _, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ | .seq _ _, _, _, h, _
  | .letpair _ _, _, _, h, _ | .case _ _ _, _, _, h, _ | .app _ _, _, _, h, _ => by
      simp [clauseAt] at h

theorem mentionsLoc_dropFill {x : Loc} (f : Val) (ℓ : Loc) :
    ∀ (i k : Nat), (dropFill f ℓ i k).MentionsLoc x →
      f.1.MentionsLoc x ∨ ∃ j, j < i + k ∧ x = ℓ + j
  | _, 0, h => by simp [dropFill, Val.unit, Expr.MentionsLoc] at h
  | i, k + 1, h => by
      simp only [dropFill, Expr.val, Val.prim, Val.loc, Expr.MentionsLoc, false_or] at h
      rcases h with (h | h) | h
      · exact .inl h
      · exact .inr ⟨i, by omega, h.symm⟩
      · rcases mentionsLoc_dropFill f ℓ (i + 1) k h with h | ⟨j, hj, rfl⟩
        · exact .inl h
        · exact .inr ⟨j, by omega, rfl⟩

theorem mentionsLoc_tabFill {x : Loc} (f : Val) (ℓ : Loc) (n : UInt32) :
    ∀ (i k : Nat), (tabFill f ℓ n i k).MentionsLoc x →
      f.1.MentionsLoc x ∨ x = ℓ ∨ ∃ j, j < i + k ∧ x = ℓ + j
  | _, 0, h => by
      simp only [tabFill, Val.arr, Val.pair, Val.loc, Val.i32, Expr.val, Expr.MentionsLoc,
        or_false] at h
      exact .inr (.inl h.symm)
  | i, k + 1, h => by
      simp only [tabFill, Expr.val, Val.prim, Val.loc, Val.i32, Expr.MentionsLoc, false_or,
        or_false] at h
      rcases h with (h | h) | h
      · exact .inr (.inr ⟨i, by omega, h.symm⟩)
      · exact .inl h
      · rcases mentionsLoc_tabFill f ℓ n (i + 1) k h with h | h | ⟨j, hj, rfl⟩
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr ⟨j, by omega, rfl⟩)

theorem mentions_hndVal {x : Loc} (n : UInt32) (qs hr hs : Val) :
    (hndVal n qs hr hs).1.MentionsLoc x ↔
      qs.1.MentionsLoc x ∨ hr.1.MentionsLoc x ∨ hs.1.MentionsLoc x := by
  simp [hndVal, Val.pair, Val.i32, Expr.MentionsLoc]

theorem mentions_opPayload {x : Loc} (n i : UInt32) (v : Val) :
    (opPayload n i v).1.MentionsLoc x ↔ v.1.MentionsLoc x := by
  simp [opPayload, Val.pair, Val.i32, Expr.MentionsLoc]

theorem mentions_app_prim {x : Loc} (p : Prim) (e : Expr) :
    (Expr.app (.val (.prim p)) e).MentionsLoc x ↔ e.MentionsLoc x := by
  simp [Val.prim, Expr.MentionsLoc]

theorem mentions_app2_prim {x : Loc} (p : Prim) (V : Val) (e : Expr) :
    (Expr.app (.app (.val (.prim p)) (.val V)) e).MentionsLoc x ↔
      V.1.MentionsLoc x ∨ e.MentionsLoc x := by
  simp [Val.prim, Expr.MentionsLoc]

/-- **A step that allocates nothing adds no live cell.** -/
theorem head_live {μ μ' : Heap} {b b' : Expr} (h : Head (ℍ := ℍ) μ b μ' b')
    (hn : b.allocs = false) {x : Loc} (hx : μ' x ≠ none) : μ x ≠ none := by
  cases h with
  | alloc => simp [Expr.allocs] at hn
  | tab => simp [Expr.allocs] at hn
  | free ℓ v hℓ =>
      by_cases e : x = ℓ
      · subst e; simp at hx
      · rwa [Heap.del_other e] at hx
  | store ℓ v w hℓ =>
      by_cases e : x = ℓ
      · subst e; simp [hℓ]
      · rwa [Heap.upd_other e] at hx
  | _ => exact hx

/-- **A step that allocates nothing stores only what its redex mentions.** -/
theorem head_stored {μ μ' : Heap} {b b' : Expr} (h : Head (ℍ := ℍ) μ b μ' b')
    (hn : b.allocs = false) {x : Loc} (hx : StoredLoc μ' x) : StoredLoc μ x ∨ b.MentionsLoc x := by
  obtain ⟨m, v, hm, hv⟩ := hx
  cases h with
  | alloc => simp [Expr.allocs] at hn
  | tab => simp [Expr.allocs] at hn
  | free ℓ w hℓ =>
      by_cases e : m = ℓ
      · subst e; simp at hm
      · rw [Heap.del_other e] at hm; exact .inl ⟨m, v, hm, hv⟩
  | store ℓ w u hℓ =>
      by_cases e : m = ℓ
      · subst e
        simp only [Heap.upd_same, Option.some.injEq] at hm
        subst hm
        exact .inr (Or.inr hv)
      · rw [Heap.upd_other e] at hm; exact .inl ⟨m, v, hm, hv⟩
  | _ => exact .inl ⟨m, v, hm, hv⟩

/-- **What a step's result mentions**: what its redex mentions, what a cell it reads holds, or an
array step's location, within `2³²` above one its redex mentions. -/
theorem head_mentions {μ μ' : Heap} {b b' : Expr} (h : Head (ℍ := ℍ) μ b μ' b')
    (hn : b.allocs = false) {x : Loc} (hx : b'.MentionsLoc x) :
    b.MentionsLoc x ∨ StoredLoc μ x ∨ ∃ (ℓ : Loc) (i : ℕ), b.MentionsLoc ℓ ∧ i < 2 ^ 32 ∧ x = ℓ + i := by
  cases h with
  | alloc => simp [Expr.allocs] at hn
  | tab => simp [Expr.allocs] at hn
  | beta b v =>
      rcases mentionsLoc_subst 0 v b hx with h | h
      · exact .inl (.inl h)
      · exact .inl (.inr h)
  | free ℓ v hℓ => exact .inr (.inl ⟨ℓ, v, hℓ, hx⟩)
  | load ℓ v hℓ => exact .inr (.inl ⟨ℓ, v, hℓ, hx⟩)
  | store ℓ v w hℓ => exact absurd hx (by simp [Val.unit, Expr.MentionsLoc])
  | seq => exact .inl (.inr hx)
  | letpair v₁ v₂ e =>
      rcases mentionsLoc_subst 0 v₁ _ hx with h | h
      · rcases mentionsLoc_subst 0 (v₂.shift 1 0) e h with h | h
        · exact .inl (.inr h)
        · exact .inl (.inl (.inr ((mentionsLoc_shift 1 0 v₂.1).mp h)))
      · exact .inl (.inl (.inl h))
  | case₁ v e₁ e₂ =>
      rcases mentionsLoc_subst 0 v e₁ hx with h | h
      · exact .inl (.inr (.inl h))
      · exact .inl (.inl h)
  | case₂ v e₁ e₂ =>
      rcases mentionsLoc_subst 0 v e₂ hx with h | h
      · exact .inl (.inr (.inr h))
      · exact .inl (.inl h)
  | host op v r hr =>
      exact absurd hx (noLoc_of_fixed
        (fun g => congrArg Subtype.val ((host_call_mapLoc ℍ op g v).2 r hr)) x)
  | idx ℓ n i =>
      unfold idxAns at hx
      split_ifs at hx
      · exact .inr (.inr ⟨ℓ, i.toNat, mentions_arrRedex, UInt32.toNat_lt i, hx.symm⟩)
      · simp [Expr.MentionsLoc, Val.inj₂, Val.unit] at hx
  | split ℓ n i =>
      unfold splitAns at hx
      split_ifs at hx
      · simp only [Val.inj₁, Val.pair, Val.arr, Val.loc, Val.i32, Expr.val, Expr.MentionsLoc,
          or_false] at hx
        rcases hx with h | h
        · exact .inl (by rw [← h]; exact mentions_arrRedex)
        · exact .inr (.inr ⟨ℓ, i.toNat, mentions_arrRedex, UInt32.toNat_lt i, h.symm⟩)
      · simp only [Val.inj₂, Val.arr, Val.pair, Val.loc, Val.i32, Expr.val, Expr.MentionsLoc,
          or_false] at hx
        exact .inl (by rw [← hx]; exact mentions_arrRedex)
  | drop f ℓ n =>
      rcases mentionsLoc_dropFill f ℓ 0 n.toNat hx with h | ⟨j, hj, rfl⟩
      · exact .inl (Or.inr (Or.inl h))
      · exact .inr (.inr ⟨ℓ, j, mentions_dropRedex,
          lt_trans (by simpa using hj) (UInt32.toNat_lt n), rfl⟩)
  | count f n i s =>
      refine .inl ((mentions_app_prim _ _).mpr ?_)
      unfold countNext at hx
      split_ifs at hx
      · simp only [Val.prim, Val.i32, Val.pair, Expr.val, Expr.MentionsLoc, false_or] at hx ⊢
        tauto
      · exact Or.inr (Or.inr (Or.inr hx))
  | countTry f n i s =>
      refine .inl ((mentions_app_prim _ _).mpr ?_)
      unfold countTryNext at hx
      split_ifs at hx
      · simp only [Val.prim, Val.i32, Val.pair, Expr.val, Expr.MentionsLoc, false_or,
          or_false, Val.val_shift, mentionsLoc_shift] at hx ⊢
        tauto
      · exact Or.inr (Or.inr (Or.inr hx))
  | boundedFix s k a =>
      refine .inl ((mentions_app_prim _ _).mpr ?_)
      simp only [boundedFixNext, Val.pair, Expr.val, Expr.MentionsLoc] at hx ⊢
      rcases hx with h | h | h
      · exact .inl h
      · unfold fixSelf at h
        split_ifs at h
        · simp [Val.inj₁, Val.unit, Expr.MentionsLoc] at h
        · simp only [Val.inj₂, Val.lam, Val.prim, Val.i32, Expr.val, Expr.MentionsLoc,
            false_or, or_false, Val.val_shift, mentionsLoc_shift] at h
          exact .inl h
      · exact .inr (.inr h)
  | hret n qs hr hs w =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      rcases hx with h | h
      · exact .inl ((mentions_hndVal n qs hr hs).mpr (.inr (.inl h)))
      · exact .inr h
  | hop n i qs hr hs c v K hc hK =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      rcases hx with h | h | h
      · exact .inl ((mentions_hndVal n qs hr hs).mpr (.inr (.inr (mentionsLoc_clauseAt hc h))))
      · exact .inr ((mentionsLoc_plug _ _).mpr (.inr ((mentions_app_prim _ _).mpr
          ((mentions_opPayload n i v).mpr h))))
      · rcases mentionsLoc_kappaAt h with h | h
        · exact .inl h
        · exact .inr ((mentionsLoc_plug _ _).mpr (.inl h))
  | hunwind n i qs hr hs c v K hc hK =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      rcases hx with h | h
      · exact .inl ((mentions_hndVal n qs hr hs).mpr (.inr (.inr (mentionsLoc_clauseAt hc h))))
      · exact .inr ((mentionsLoc_plug _ _).mpr (.inr ((mentions_app_prim _ _).mpr
          ((mentions_opPayload n i v).mpr h))))
  | uthen N D w =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      rcases hx with h | h
      · exact .inl (.inl h)
      · exact .inr h
  | ufin N D n i v K hn' hK =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      simp only [Val.unit, Expr.val, Expr.MentionsLoc, or_false] at hx
      rcases hx with h | h
      · exact .inl (.inr h)
      · exact .inr ((mentionsLoc_plug _ _).mpr (.inr h))
  | ufinC N D err K hK =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      rcases (mentions_app2_prim _ _ _).mp hx with h | h
      · obtain ⟨E, rfl, hE⟩ := mentionsLoc_cancelVal h
        exact .inr ((mentionsLoc_plug _ _).mpr (.inr ((mentions_app_prim _ _).mpr
          (show (cancelVal (some E)).1.MentionsLoc x from Or.inr (Or.inr hE)))))
      · simp only [Val.unit, Expr.val, Expr.MentionsLoc, or_false] at h
        exact .inl (.inr h)
  | cfret err w =>
      refine .inl ((mentions_app2_prim _ _ _).mpr (.inl ?_))
      exact (mentions_app_prim _ _).mp hx
  | cferr err m j w K hm hK =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      obtain ⟨E, hE, hEx⟩ := mentionsLoc_cancelVal ((mentions_app_prim _ _).mp hx)
      rcases mentionsLoc_errNext hE hEx with ⟨E', rfl, h⟩ | h
      · exact .inl (Or.inr (Or.inr h))
      · exact .inr ((mentionsLoc_plug _ _).mpr (.inr ((mentions_app_prim _ _).mpr
          ((mentions_opPayload m j w).mpr h))))
  | cfcancel err err' K hK =>
      refine .inl ((mentions_app2_prim _ _ _).mpr ?_)
      obtain ⟨E, hE, hEx⟩ := mentionsLoc_cancelVal ((mentions_app_prim _ _).mp hx)
      cases err with
      | some E' =>
          simp only [Option.some_or, Option.some.injEq] at hE
          subst hE
          exact .inl (Or.inr (Or.inr hEx))
      | none =>
          simp only [Option.none_or] at hE
          subst hE
          exact .inr ((mentionsLoc_plug _ _).mpr (.inr ((mentions_app_prim _ _).mpr
            (show (cancelVal (some E)).1.MentionsLoc x from Or.inr (Or.inr hEx)))))
  | cancel K hK => exact absurd hx (by simp [Val.unit, Expr.MentionsLoc])
  | creraise E K hK =>
      refine .inl ((mentions_app_prim _ _).mpr ?_)
      exact (mentionsLoc_plug _ _).mpr (.inr ((mentions_app_prim _ _).mpr
        (show (cancelVal (some E)).1.MentionsLoc x from Or.inr (Or.inr
          ((mentions_app_prim _ _).mp hx)))))

/-! ### The simulation's invariant -/

/-- **The bump run's blocks**: `g` moves as a block the window `[ℓ, ℓ + (k + 1) · 2³²]` above every
location the configuration names.  A step's array arithmetic adds less than `2³²` to a location the
configuration names (`head_mentions`), so with `k` steps to go the windows still hold every
location the run computes. -/
def AffineAbove (g : Loc → Loc) (μ : Heap) (e : Expr) (k : Nat) : Prop :=
  ∀ ℓ, Named μ e ℓ → ∀ j, j ≤ (k + 1) * 2 ^ 32 → g (ℓ + j) = g ℓ + j

/-- **The platform's protocol at a stop**: an operation the platform answers is asked at a data
argument (`Platform.Respects` answers data arguments only). -/
def PlatData (P : Platform) (c : Conf P) : Prop :=
  ∀ (K : Kont) (n i : UInt32) (v : Val) (o : OpSig),
    c.e = K.plug (performE (.val (opPayload n i v))) → K.HasHnd n = false →
    Row.find P.ops n i = some o → DataVal o.A v

theorem two32_le (k : Nat) : 2 ^ 32 ≤ (k + 1) * 2 ^ 32 := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)

theorem mentionsLoc_of_mentionsArr {ℓ : Loc} {n : UInt32} :
    ∀ {e : Expr}, e.MentionsArr ℓ n → e.MentionsLoc ℓ
  | .pair a b, h => by
      rcases h with ⟨rfl, -⟩ | h | h
      · exact .inl rfl
      · exact .inl (mentionsLoc_of_mentionsArr h)
      · exact .inr (mentionsLoc_of_mentionsArr h)
  | .seq a b, h | .letpair a b, h | .app a b, h => by
      rcases h with h | h
      · exact .inl (mentionsLoc_of_mentionsArr h)
      · exact .inr (mentionsLoc_of_mentionsArr h)
  | .inj₁ a, h | .inj₂ a, h | .lam a, h => mentionsLoc_of_mentionsArr (e := a) h
  | .case a b c, h => by
      rcases h with h | h | h
      · exact .inl (mentionsLoc_of_mentionsArr h)
      · exact .inr (.inl (mentionsLoc_of_mentionsArr h))
      · exact .inr (.inr (mentionsLoc_of_mentionsArr h))
  | .var _, h | .unit, h | .prim _, h | .loc _, h => h.elim

/-- The windows hold every array value's block. -/
theorem blocksAffine_of_affineAbove {g : Loc → Loc} {μ : Heap} {e : Expr} {k : Nat}
    (h : AffineAbove g μ e k) : BlocksAffine g μ e := by
  intro ℓ n hn j hj
  have hnamed : Named μ e ℓ := by
    rcases hn with hn | ⟨m, v, hm, hv⟩
    · exact .inr (.inl (mentionsLoc_of_mentionsArr hn))
    · exact .inr (.inr ⟨m, v, hm, mentionsLoc_of_mentionsArr hv⟩)
  exact h ℓ hnamed j (le_trans hj (le_trans (UInt32.toNat_lt n).le (two32_le k)))

/-- The identity moves every window as a block. -/
theorem affineAbove_id (μ : Heap) (e : Expr) (k : Nat) : AffineAbove id μ e k :=
  fun _ _ _ _ => rfl

/-- Above every location a configuration of finite memory names, and above a finite set. -/
theorem exists_bound (μ : Heap) (e : Expr) (hfin : FinDom μ) (X : Finset Loc) :
    ∃ M : Loc, (∀ ℓ, Named μ e ℓ → ℓ ≤ M) ∧ ∀ ℓ ∈ X, ℓ ≤ M := by
  obtain ⟨d, hd⟩ := hfin
  refine ⟨(namedList μ e d).toFinset.sup id ⊔ X.sup id, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · exact le_sup_of_le_left (Finset.le_sup (f := id) (List.mem_toFinset.mpr (mem_namedList hd hℓ)))
  · exact le_sup_of_le_right (Finset.le_sup (f := id) hℓ)

theorem allocs_mapLoc (g : Loc → Loc) (b : Expr) : (b.mapLoc g).allocs = b.allocs := by
  cases b with
  | app f a =>
      cases f with
      | prim p => cases p <;> rfl
      | _ => rfl
  | _ => rfl

/-- **What a step that allocates nothing names**: what its configuration named, or an array step's
location, within `2³²` above one it named. -/
theorem named_step {μ μ' : Heap} {K : Kont} {b b' : Expr} (h : Head (ℍ := ℍ) μ b μ' b')
    (hn : b.allocs = false) {x : Loc} (hx : Named μ' (K.plug b') x) :
    Named μ (K.plug b) x ∨ ∃ (ℓ : Loc) (i : ℕ), Named μ (K.plug b) ℓ ∧ i < 2 ^ 32 ∧ x = ℓ + i := by
  have hb : ∀ y, b.MentionsLoc y → Named μ (K.plug b) y := fun y hy =>
    .inr (.inl ((mentionsLoc_plug K b).mpr (.inr hy)))
  rcases hx with hl | ht | hs
  · exact .inl (.inl (isSome_iff_ne.mpr (head_live h hn (isSome_iff_ne.mp hl))))
  · rcases (mentionsLoc_plug K b').mp ht with hK | hb'
    · exact .inl (.inr (.inl ((mentionsLoc_plug K b).mpr (.inl hK))))
    · rcases head_mentions h hn hb' with hm | hs | ⟨ℓ, i, hℓ, hi, rfl⟩
      · exact .inl (hb x hm)
      · exact .inl (.inr (.inr hs))
      · exact .inr ⟨ℓ, i, hb ℓ hℓ, hi, rfl⟩
  · rcases head_stored h hn hs with hs | hm
    · exact .inl (.inr (.inr hs))
    · exact .inl (hb x hm)

/-- The windows after a step that allocates nothing, one `2³²` narrower. -/
theorem affineAbove_step {g : Loc → Loc} {μ μ' : Heap} {K : Kont} {b b' : Expr} {k : Nat}
    (h : Head (ℍ := ℍ) μ b μ' b') (hn : b.allocs = false)
    (hA : AffineAbove g μ (K.plug b) (k + 1)) : AffineAbove g μ' (K.plug b') k := by
  intro x hx j hj
  rcases named_step h hn hx with hx | ⟨ℓ, i, hℓ, hi, rfl⟩
  · exact hA x hx j (by linarith)
  · have h₁ := hA ℓ hℓ (i + j) (by linarith)
    have h₂ := hA ℓ hℓ i (by linarith)
    rw [Nat.add_assoc, h₁, h₂, Nat.add_assoc]

/-! ### One step, followed -/

/-- **The given step is at the renamed redex**: a step of the renamed term is the renamed redex's,
in the renamed context (unique decomposition, `plug_decomp`). -/
theorem step_at_image {g : Loc → Loc} {μB μB'' μA μA' : Heap} {K : Kont} {b b'' eA' : Expr}
    (hB : Head (ℍ := ℍ) μB b μB'' b'')
    (hA : Step1 (ℍ := ℍ) μA ((K.plug b).mapLoc g) μA' eA') :
    ∃ a', eA' = (K.mapLoc g).plug a' ∧ Head (ℍ := ℍ) μA (b.mapLoc g) μA' a' := by
  obtain ⟨K', a, a', hE, rfl, hh⟩ := hA
  rw [kont_mapLoc_plug] at hE
  obtain ⟨μ₂, μ₂', b₂, h₂⟩ := head_mapLoc_exists g hB
  obtain ⟨rfl, rfl⟩ := plug_decomp hh (K.mapLoc g) K' h₂ hE
  exact ⟨a', rfl, hh⟩

/-- A renamed redex is never an operation the platform answers. -/
theorem not_plat_of_head {g : Loc → Loc} {μB μB'' : Heap} {K K' : Kont} {b b'' : Expr}
    {n i : UInt32} {v : Val} (hB : Head (ℍ := ℍ) μB b μB'' b'') (hK' : K'.HasHnd n = false)
    (he : (K.plug b).mapLoc g = K'.plug (performE (.val (opPayload n i v)))) : False := by
  obtain ⟨μ₂, μ₂', b₂, h₂⟩ := head_mapLoc_exists g hB
  have hs : Step1 (ℍ := ℍ) μ₂ ((K.plug b).mapLoc g) μ₂' ((K.mapLoc g).plug b₂) :=
    ⟨K.mapLoc g, _, _, kont_mapLoc_plug g K b, rfl, h₂⟩
  rw [he] at hs
  exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK' hs

/-- **A step that allocates nothing, followed**: the given step is the renamed step, along `g`
itself. -/
theorem sim_det {P : Platform} {X : Finset Loc} {g : Loc → Loc} {k : Nat} {μB μB'' : Heap}
    {K : Kont} {b b'' : Expr} {sB : P.St} {cA' : Conf P}
    (hB : Head (ℍ := ℍ) μB b μB'' b'') (hn : b.allocs = false)
    (hinj : Set.InjOn g {x | μB x ≠ none}) (hAff : AffineAbove g μB (K.plug b) (k + 1))
    (hA : PStep (ℍ := ℍ) P ⟨Heap.push g μB, (K.plug b).mapLoc g, sB⟩ cA') :
    ∃ (cB' : Conf P) (g' : Loc → Loc), PStep (ℍ := ℍ) P ⟨μB, K.plug b, sB⟩ cB' ∧
      (∀ ℓ, μB ℓ = none → (cB'.μ ℓ).isSome → ¬ Named μB (K.plug b) ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named μB (K.plug b) ℓ → g' ℓ = g ℓ) ∧ RelAt g' cA' cB' ∧
      BlocksAffine g' cB'.μ cB'.e ∧ AffineAbove g' cB'.μ cB'.e k := by
  have haff : AffineAt g b := fun ℓ i hℓ hi =>
    hAff ℓ (.inr (.inl ((mentionsLoc_plug K b).mpr (.inr hℓ)))) i
      (le_trans hi.le (two32_le (k + 1)))
  have hImg := head_image hB hn hinj haff
  rcases pstep_cases hA with ⟨hstepA, hsA⟩ | ⟨K', n, i, v, w, s', o, he, hK', -, -, -⟩
  · obtain ⟨cμ, ce, cs⟩ := cA'
    simp only at hstepA hsA
    subst cs
    obtain ⟨a', rfl, hhA⟩ := step_at_image hB hstepA
    obtain ⟨rfl, rfl⟩ := head_det hImg (by rw [allocs_mapLoc]; exact hn) hhA rfl
    have hA' := affineAbove_step hB hn hAff
    refine ⟨⟨μB'', K.plug b'', sB⟩, g, PStep.mach ⟨K, b, b'', rfl, rfl, hB⟩, ?_, fun _ _ => rfl,
      ⟨fun x hx y hy e => hinj (head_live hB hn hx) (head_live hB hn hy) e,
        (kont_mapLoc_plug g K b'').symm, rfl, rfl⟩, blocksAffine_of_affineAbove hA', hA'⟩
    intro ℓ h0 h1
    exact absurd h0 (head_live hB hn (isSome_iff_ne.mp h1))
  · exact (not_plat_of_head hB hK' he).elim

/-- The fresh block's base: above every location the configuration and `X` name, by more than the
windows. -/
theorem fresh_base {μ : Heap} {e : Expr} {X : Finset Loc} {M : Loc} (k : Nat)
    (hM : ∀ ℓ, Named μ e ℓ → ℓ ≤ M) (hMX : ∀ ℓ ∈ X, ℓ ≤ M) (j : Nat) :
    ¬ Named μ e (M + (k + 1 + 1) * 2 ^ 32 + 1 + j) ∧ M + (k + 1 + 1) * 2 ^ 32 + 1 + j ∉ X := by
  constructor
  · intro h; have := hM _ h; llinarith
  · intro h; have := hMX _ h; llinarith

/-- **The windows after an allocation at a fresh base**: a named location is old, below the base,
or at or above it, where `g'` translates. -/
theorem affineAbove_fresh {g : Loc → Loc} {μ μ' : Heap} {e e' : Expr} {k : Nat} {M ℓB ℓA : Loc}
    (hAff : AffineAbove g μ e (k + 1)) (hM : ∀ ℓ, Named μ e ℓ → ℓ ≤ M)
    (hB : ℓB = M + (k + 1 + 1) * 2 ^ 32 + 1)
    (hnamed : ∀ x, Named μ' e' x → Named μ e x ∨ ℓB ≤ x) :
    AffineAbove (fun x => if x < ℓB then g x else ℓA + (x - ℓB)) μ' e' k := by
  intro x hx j hj
  rcases hnamed x hx with hx | hx
  · have hxM := hM x hx
    have h₁ : x + j < ℓB := by rw [hB]; llinarith
    have h₂ : x < ℓB := lt_of_le_of_lt (Nat.le_add_right x j) h₁
    simp only [if_pos h₁, if_pos h₂]
    exact hAff x hx j (le_trans hj (Nat.mul_le_mul_right _ (Nat.le_succ _)))
  · have h₁ : ¬ x + j < ℓB := fun h => absurd (lt_of_le_of_lt (Nat.le_add_right x j) h) (not_lt.mpr hx)
    have h₂ : ¬ x < ℓB := not_lt.mpr hx
    simp only [if_neg h₁, if_neg h₂]
    lomega

/-- **An allocation, followed**: the bump step allocates above every name and `X`, and the
renaming sends that location to the given step's. -/
theorem sim_alloc {P : Platform} {X : Finset Loc} {g : Loc → Loc} {k : Nat} {μB : Heap}
    {K : Kont} {v : Val} {ℓ₀ : Loc} {sB : P.St} {cA' : Conf P}
    (hℓ₀ : μB ℓ₀ = none) (hfin : FinDom μB) (hinj : Set.InjOn g {x | μB x ≠ none})
    (hAff : AffineAbove g μB (K.plug (.app (.val (.prim .alloc)) (.val v))) (k + 1))
    (hA : PStep (ℍ := ℍ) P
      ⟨Heap.push g μB, (K.plug (.app (.val (.prim .alloc)) (.val v))).mapLoc g, sB⟩ cA') :
    ∃ (cB' : Conf P) (g' : Loc → Loc),
      PStep (ℍ := ℍ) P ⟨μB, K.plug (.app (.val (.prim .alloc)) (.val v)), sB⟩ cB' ∧
      (∀ ℓ, μB ℓ = none → (cB'.μ ℓ).isSome →
        ¬ Named μB (K.plug (.app (.val (.prim .alloc)) (.val v))) ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named μB (K.plug (.app (.val (.prim .alloc)) (.val v))) ℓ → g' ℓ = g ℓ) ∧
      RelAt g' cA' cB' ∧ BlocksAffine g' cB'.μ cB'.e ∧ AffineAbove g' cB'.μ cB'.e k := by
  set eB := K.plug (.app (.val (.prim .alloc)) (.val v)) with heB
  have hB₀ : Head (ℍ := ℍ) μB (.app (.val (.prim .alloc)) (.val v)) (μB.upd ℓ₀ v) (.val (.loc ℓ₀)) :=
    Head.alloc μB v ℓ₀ hℓ₀
  have hKn : ∀ y, (K.plug .unit).MentionsLoc y → Named μB eB y := fun y hy =>
    .inr (.inl ((mentionsLoc_plug K _).mpr (.inl hy)))
  have hvn : ∀ y, v.1.MentionsLoc y → Named μB eB y := fun y hy =>
    .inr (.inl ((mentionsLoc_plug K _).mpr (.inr (Or.inr hy))))
  rcases pstep_cases hA with ⟨hstepA, hsA⟩ | ⟨K', n, i, w, w', s', o, he, hK', -, -, -⟩
  · obtain ⟨cμ, ce, cs⟩ := cA'
    simp only at hstepA hsA
    subst cs
    obtain ⟨a', rfl, hhA⟩ := step_at_image hB₀ hstepA
    obtain ⟨ℓA, hℓA, rfl, rfl⟩ := head_alloc_inv (v := v.mapLoc g) hhA
    obtain ⟨M, hM, hMX⟩ := exists_bound μB eB hfin X
    set ℓB : Loc := M + (k + 1 + 1) * 2 ^ 32 + 1 with hℓB
    set g' : Loc → Loc := fun x => if x < ℓB then g x else ℓA + (x - ℓB) with hg'
    have hfr := fresh_base (μ := μB) (e := eB) k hM hMX 0
    simp only [Nat.add_zero] at hfr
    have hfreeB : μB ℓB = none := by
      by_contra h; exact hfr.1 (.inl (isSome_iff_ne.mpr h))
    have hlt : ∀ y, Named μB eB y → y < ℓB := fun y hy => by have := hM y hy; rw [hℓB]; llinarith
    have hagree : ∀ y, Named μB eB y → g' y = g y := fun y hy => by
      simp only [hg', if_pos (hlt y hy)]
    have hgB : g' ℓB = ℓA := by simp only [hg', lt_irrefl, if_false, Nat.sub_self, Nat.add_zero]
    have hAfree : ∀ x, μB x ≠ none → g x ≠ ℓA := fun x hx e =>
      push_ne_none.mpr ⟨x, hx, e⟩ hℓA
    obtain ⟨hpush, hinj'⟩ := push_upd_fresh hinj hfreeB hAfree hgB
      (fun x hx => hagree x (.inl (isSome_iff_ne.mpr hx)))
      (fun x hx => hagree x (.inr (.inr hx))) v
    have hvg : v.mapLoc g' = v.mapLoc g := valMapLoc_congr v fun y hy => hagree y (hvn y hy)
    have hKg : K.mapLoc g' = K.mapLoc g := kont_mapLoc_congr K fun y hy => hagree y (hKn y hy)
    have hnamed : ∀ x, Named (μB.upd ℓB v) (K.plug (.val (.loc ℓB))) x → Named μB eB x ∨ ℓB ≤ x := by
      rintro x (hl | ht | ⟨m, u, hm, hu⟩)
      · by_cases hx : x = ℓB
        · exact .inr hx.ge
        · rw [Heap.upd_other hx] at hl; exact .inl (.inl hl)
      · rcases (mentionsLoc_plug K _).mp ht with ht | ht
        · exact .inl (hKn x ht)
        · exact .inr (le_of_eq (show ℓB = x from ht))
      · by_cases hm' : m = ℓB
        · subst hm'; simp only [Heap.upd_same, Option.some.injEq] at hm; subst hm
          exact .inl (hvn x hu)
        · rw [Heap.upd_other hm'] at hm; exact .inl (.inr (.inr ⟨m, u, hm, hu⟩))
    have hA' := affineAbove_fresh (ℓA := ℓA) hAff hM hℓB hnamed
    refine ⟨⟨μB.upd ℓB v, K.plug (.val (.loc ℓB)), sB⟩, g',
      PStep.mach ⟨K, _, _, rfl, rfl, Head.alloc μB v ℓB hfreeB⟩, ?_, hagree,
      ⟨hinj', ?_, ?_, rfl⟩, blocksAffine_of_affineAbove hA', hA'⟩
    · intro ℓ h0 h1
      have hℓ : ℓ = ℓB := by
        by_contra hne; simp only [Heap.upd_other hne, h0] at h1; cases h1
      subst hℓ; exact hfr
    · simp only
      rw [kont_mapLoc_plug, hKg]
      show _ = (K.mapLoc g).plug (.loc (g' ℓB))
      rw [hgB]; rfl
    · simp only
      rw [hpush, hvg]
  · exact (not_plat_of_head hB₀ hK' he).elim

/-- **A block allocation, followed**: the bump step places the block above every name and `X`, and
the renaming translates it onto the given step's block. -/
theorem sim_tab {P : Platform} {X : Finset Loc} {g : Loc → Loc} {k : Nat} {μB : Heap}
    {K : Kont} {c : UInt32} {f : Val} {ℓ₀ : Loc} {sB : P.St} {cA' : Conf P}
    (hℓ₀ : ∀ i, i < (arrLen c).toNat → μB (ℓ₀ + i) = none) (hfin : FinDom μB)
    (hinj : Set.InjOn g {x | μB x ≠ none})
    (hAff : AffineAbove g μB (K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))) (k + 1))
    (hA : PStep (ℍ := ℍ) P
      ⟨Heap.push g μB, (K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))).mapLoc g, sB⟩
      cA') :
    ∃ (cB' : Conf P) (g' : Loc → Loc),
      PStep (ℍ := ℍ) P ⟨μB, K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f))), sB⟩ cB' ∧
      (∀ ℓ, μB ℓ = none → (cB'.μ ℓ).isSome →
        ¬ Named μB (K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))) ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named μB (K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))) ℓ →
        g' ℓ = g ℓ) ∧
      RelAt g' cA' cB' ∧ BlocksAffine g' cB'.μ cB'.e ∧ AffineAbove g' cB'.μ cB'.e k := by
  set eB := K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f))) with heB
  set len := (arrLen c).toNat with hlen
  have hB₀ : Head (ℍ := ℍ) μB (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))
      (μB.fill ℓ₀ len .unit) (tabFill f ℓ₀ (arrLen c) 0 len) := Head.tab μB c f ℓ₀ hℓ₀
  have hKn : ∀ y, (K.plug .unit).MentionsLoc y → Named μB eB y := fun y hy =>
    .inr (.inl ((mentionsLoc_plug K _).mpr (.inl hy)))
  have hfn : ∀ y, f.1.MentionsLoc y → Named μB eB y := fun y hy =>
    .inr (.inl ((mentionsLoc_plug K _).mpr (.inr (Or.inr (Or.inr hy)))))
  rcases pstep_cases hA with ⟨hstepA, hsA⟩ | ⟨K', n, i, w, w', s', o, he, hK', -, -, -⟩
  · obtain ⟨cμ, ce, cs⟩ := cA'
    simp only at hstepA hsA
    subst cs
    obtain ⟨a', rfl, hhA⟩ := step_at_image hB₀ hstepA
    obtain ⟨ℓA, hℓA, rfl, rfl⟩ := head_tab_inv (f := f.mapLoc g) hhA
    obtain ⟨M, hM, hMX⟩ := exists_bound μB eB hfin X
    set ℓB : Loc := M + (k + 1 + 1) * 2 ^ 32 + 1 with hℓB
    set g' : Loc → Loc := fun x => if x < ℓB then g x else ℓA + (x - ℓB) with hg'
    have hfr := fun j => fresh_base (μ := μB) (e := eB) k hM hMX j
    have hfreeB : ∀ j, j < len → μB (ℓB + j) = none := fun j _ => by
      by_contra h; exact (hfr j).1 (.inl (isSome_iff_ne.mpr h))
    have hlt : ∀ y, Named μB eB y → y < ℓB := fun y hy => by have := hM y hy; rw [hℓB]; llinarith
    have hagree : ∀ y, Named μB eB y → g' y = g y := fun y hy => by
      simp only [hg', if_pos (hlt y hy)]
    have hgB : ∀ j, g' (ℓB + j) = ℓA + j := fun j => by
      simp only [hg']
      rw [if_neg (by lomega)]
      lomega
    have hAfree : ∀ x, μB x ≠ none → ∀ j, j < len → g x ≠ ℓA + j := fun x hx j hj e =>
      push_ne_none.mpr ⟨x, hx, e⟩ (hℓA j hj)
    obtain ⟨hpush, hinj'⟩ := push_fill_fresh hinj hfreeB hAfree (fun j _ => hgB j)
      (fun x hx => hagree x (.inl (isSome_iff_ne.mpr hx)))
      (fun x hx => hagree x (.inr (.inr hx)))
    have hfg : f.mapLoc g' = f.mapLoc g := valMapLoc_congr f fun y hy => hagree y (hfn y hy)
    have hKg : K.mapLoc g' = K.mapLoc g := kont_mapLoc_congr K fun y hy => hagree y (hKn y hy)
    have hnamed : ∀ x, Named (μB.fill ℓB len .unit) (K.plug (tabFill f ℓB (arrLen c) 0 len)) x →
        Named μB eB x ∨ ℓB ≤ x := by
      rintro x (hl | ht | ⟨m, u, hm, hu⟩)
      · by_cases hx : ℓB ≤ x ∧ x < ℓB + len
        · exact .inr hx.1
        · simp only [Heap.fill, if_neg hx] at hl; exact .inl (.inl hl)
      · rcases (mentionsLoc_plug K _).mp ht with ht | ht
        · exact .inl (hKn x ht)
        · rcases mentionsLoc_tabFill f ℓB (arrLen c) 0 len ht with h | rfl | ⟨j, -, rfl⟩
          · exact .inl (hfn x h)
          · exact .inr le_rfl
          · exact .inr (Nat.le_add_right _ _)
      · by_cases hm' : ℓB ≤ m ∧ m < ℓB + len
        · simp only [Heap.fill, if_pos hm', Option.some.injEq] at hm
          subst hm
          simp [Val.unit, Expr.MentionsLoc] at hu
        · simp only [Heap.fill, if_neg hm'] at hm
          exact .inl (.inr (.inr ⟨m, u, hm, hu⟩))
    have hA' := affineAbove_fresh (ℓA := ℓA) hAff hM hℓB hnamed
    refine ⟨⟨μB.fill ℓB len .unit, K.plug (tabFill f ℓB (arrLen c) 0 len), sB⟩, g',
      PStep.mach ⟨K, _, _, rfl, rfl, Head.tab μB c f ℓB hfreeB⟩, ?_, hagree,
      ⟨hinj', ?_, ?_, rfl⟩, blocksAffine_of_affineAbove hA', hA'⟩
    · intro ℓ h0 h1
      by_cases hℓ : ℓB ≤ ℓ ∧ ℓ < ℓB + len
      · obtain ⟨j, -, rfl⟩ : ∃ j, j < len ∧ ℓ = ℓB + j := ⟨ℓ - ℓB, by lomega, by lomega⟩
        exact hfr j
      · simp only [Heap.fill, if_neg hℓ, h0] at h1; cases h1
    · simp only
      rw [kont_mapLoc_plug, hKg, tabFill_mapLoc g' f ℓB (arrLen c) 0 len
        (fun j _ => by rw [hgB j, show ℓB = ℓB + 0 from rfl, hgB 0]; rfl), hfg,
        show g' ℓB = ℓA from by simpa using hgB 0]
    · simp only
      rw [hpush]
  · exact (not_plat_of_head hB₀ hK' he).elim

/-- **A platform answer, followed**: the given run's answer is the bump run's, at a data argument
and a data answer, which no renaming moves. -/
theorem sim_plat {P : Platform} {X : Finset Loc} {g : Loc → Loc} {k : Nat} {μB : Heap}
    {K : Kont} {n i : UInt32} {v w : Val} {s' sB : P.St} {o : OpSig} {cA' : Conf P}
    (hP : P.Respects) (hd : DataVal o.A v) (hK : K.HasHnd n = false)
    (hf : Row.find P.ops n i = some o) (hco : P.co sB n i v = some (w, s'))
    (hinj : Set.InjOn g {x | μB x ≠ none})
    (hAff : AffineAbove g μB (K.plug (performE (.val (opPayload n i v)))) (k + 1))
    (hA : PStep (ℍ := ℍ) P
      ⟨Heap.push g μB, (K.plug (performE (.val (opPayload n i v)))).mapLoc g, sB⟩ cA') :
    ∃ (cB' : Conf P) (g' : Loc → Loc),
      PStep (ℍ := ℍ) P ⟨μB, K.plug (performE (.val (opPayload n i v))), sB⟩ cB' ∧
      (∀ ℓ, μB ℓ = none → (cB'.μ ℓ).isSome →
        ¬ Named μB (K.plug (performE (.val (opPayload n i v)))) ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named μB (K.plug (performE (.val (opPayload n i v)))) ℓ → g' ℓ = g ℓ) ∧
      RelAt g' cA' cB' ∧ BlocksAffine g' cB'.μ cB'.e ∧ AffineAbove g' cB'.μ cB'.e k := by
  have hv : v.mapLoc g = v := Subtype.ext (mapLoc_of_noLoc (noLoc_of_dataVal hd))
  have hdB : DataVal o.B w := hP.typed sB s' o v w (Row.find_mem hf).1 hd
    (by rw [(Row.find_mem hf).2.1, (Row.find_mem hf).2.2]; exact hco)
  have hnw := noLoc_of_dataVal hdB
  have hw : w.1.mapLoc g = w.1 := mapLoc_of_noLoc hnw
  have hp : (opPayload n i v).mapLoc g = opPayload n i v := by rw [opPayload_mapLoc, hv]
  have he : (K.plug (performE (.val (opPayload n i v)))).mapLoc g =
      (K.mapLoc g).plug (performE (.val (opPayload n i v))) := by
    rw [kont_mapLoc_plug, performE_mapLoc]
    congr 2
    exact congrArg Subtype.val hp
  rcases pstep_cases hA with ⟨hstepA, -⟩ | ⟨K', n', i', v', w', s'', o', he', hK', hf', hco', rfl⟩
  · exfalso
    simp only at hstepA
    rw [he] at hstepA
    exact opPlug_no_step (r := false) (payloadName_opPayload n i v)
      (show (K.mapLoc g).HasHnd n = false by rw [hasHnd_mapLoc, hK]) hstepA
  · simp only at he' hco'
    rw [he] at he'
    obtain ⟨rfl, hp⟩ := plug_perform_inj he'
    obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp
    rw [hco] at hco'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hco')
    have hnamed : ∀ x, Named μB (K.plug (.val w)) x →
        Named μB (K.plug (performE (.val (opPayload n i v)))) x := by
      rintro x (hl | ht | hs)
      · exact .inl hl
      · rcases (mentionsLoc_plug K _).mp ht with ht | ht
        · exact .inr (.inl ((mentionsLoc_plug K _).mpr (.inl ht)))
        · exact absurd ht (hnw x)
      · exact .inr (.inr hs)
    have hA' : AffineAbove g μB (K.plug (.val w)) k := fun x hx j hj =>
      hAff x (hnamed x hx) j (le_trans hj (Nat.mul_le_mul_right _ (Nat.le_succ _)))
    refine ⟨⟨μB, K.plug (.val w), s'⟩, g, PStep.plat hK hf hco, ?_, fun _ _ => rfl,
      ⟨hinj, ?_, rfl, rfl⟩, blocksAffine_of_affineAbove hA', hA'⟩
    · intro ℓ h0 h1; simp [h0] at h1
    · simp only
      rw [kont_mapLoc_plug]
      exact congrArg _ hw.symm

/-! ### The simulation -/

/-- **`BumpSim` at the configurations a bump run reaches** (OQ-43 (b)): `BumpSim` with four
hypotheses added, and the windows carried to the successor.
* `P.Respects`: the platform keeps its protocol, as B5 asks of every platform it quantifies over.
* `FinDom cB.μ`: the bump side's memory is finite, as every memory a run from `init` reaches is
  (`finDom_pstep`).
* `AffineAbove g cB.μ cB.e (k + 1)`: `g` moves as a block the window `[ℓ, ℓ + (k + 2) · 2³²]`
  above every location `cB` names; the identity does, at every `k`, at `init`.
* `PlatData P cB`: an operation the platform answers is asked at a data argument.  Every run of a
  program safe under the restricted platform meets it (`platData_of_safe`).

`BlocksAffine` is kept as `BumpSim` states it; `AffineAbove` implies it
(`blocksAffine_of_affineAbove`). -/
def BumpSimAt : Prop :=
  ∀ (P : Platform) (X : Finset Loc) (g : Loc → Loc) (cA cA' cB : Conf P) (k : Nat),
    P.Respects → FinDom cB.μ → AffineAbove g cB.μ cB.e (k + 1) → PlatData P cB →
    RelAt g cA cB → BlocksAffine g cB.μ cB.e → PStep (ℍ := ℍ) P cA cA' →
    (∃ cB'', PStep (ℍ := ℍ) P cB cB'') →
    ∃ cB' g', PStep (ℍ := ℍ) P cB cB' ∧
      (∀ ℓ, cB.μ ℓ = none → (cB'.μ ℓ).isSome → ¬ Named cB.μ cB.e ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named cB.μ cB.e ℓ → g' ℓ = g ℓ) ∧ RelAt g' cA' cB' ∧ BlocksAffine g' cB'.μ cB'.e ∧
      AffineAbove g' cB'.μ cB'.e k

/-- **The step-for-step simulation, at the configurations a bump run reaches.** -/
theorem bumpSimAt : BumpSimAt (ℍ := ℍ) := by
  intro P X g cA cA' cB k hP hfin hAff hPD hR _ hA hprog
  obtain ⟨μB, eB, sB⟩ := cB
  obtain ⟨μA, eA, sA⟩ := cA
  obtain ⟨hinj, he, hμ, hs⟩ := hR
  simp only at hinj he hμ hs hfin hAff hPD ⊢
  subst he hμ hs
  obtain ⟨⟨μ'', e'', s''⟩, hB''⟩ := hprog
  rcases pstep_cases hB'' with ⟨⟨K, b, b'', heB, -, hB⟩, -⟩ |
    ⟨K, n, i, v, w, s', o, heB, hK, hf, hco, -⟩
  · simp only at heB
    subst heB
    cases hb : b.allocs with
    | false => exact sim_det hB hb hinj hAff hA
    | true =>
        cases hB with
        | alloc v ℓ₀ hℓ₀ => exact sim_alloc hℓ₀ hfin hinj hAff hA
        | tab c f ℓ₀ hℓ₀ => exact sim_tab hℓ₀ hfin hinj hAff hA
        | _ => simp [Expr.allocs, hndE, ubindE, ccatchE, cfinE] at hb
  · simp only at heB
    subst heB
    exact sim_plat hP (hPD K n i v o rfl hK hf) hK hf hco hinj hAff hA


/-! ### The platform's protocol along every run of a safe program -/

open Classical in
/-- The platform restricted to its protocol: it answers an operation of its row only at a data
argument of the operation's type. -/
def Platform.restrict (P : Platform) : Platform where
  ops := P.ops
  St := P.St
  s₀ := P.s₀
  co s n i v :=
    if ∃ o, Row.find P.ops n i = some o ∧ DataVal o.A v then P.co s n i v else Option.none

/-- A platform that keeps its protocol keeps it restricted. -/
theorem restrict_respects {P : Platform} (hP : P.Respects) : P.restrict.Respects where
  uniq := hP.uniq
  nz := hP.nz
  lin := hP.lin
  data := hP.data
  total := fun s o v ho hd => by
    obtain ⟨w, s', h⟩ := hP.total s o v ho hd
    refine ⟨w, s', ?_⟩
    simp only [Platform.restrict]
    rw [if_pos ⟨o, Row.find_of_mem hP.uniq ho, hd⟩]
    exact h
  typed := fun s s' o v w ho hd h => by
    simp only [Platform.restrict] at h
    split_ifs at h
    exact hP.typed s s' o v w ho hd h

/-- A configuration, read under the restricted platform. -/
def Conf.toRestrict {P : Platform} (c : Conf P) : Conf P.restrict := ⟨c.μ, c.e, c.s⟩

/-- **Where the restricted platform does not get stuck, the protocol holds**: a stop of an
operation the platform answers, at an argument that is not data, has no step under the restricted
platform and is not final. -/
theorem platData_of_safeAt {P : Platform} {A : VTy} {c : Conf P}
    (h : Final P.restrict A c.toRestrict ∨ ∃ c', PStep (ℍ := ℍ) P.restrict c.toRestrict c') :
    PlatData P c := by
  intro K n i v o he hK hf
  rcases h with ⟨w, hw, -⟩ | ⟨c', hc'⟩
  · exact absurd (he.symm.trans hw) (plug_perform_ne_val K _ w)
  · rcases pstep_cases hc' with ⟨hs, -⟩ | ⟨K', n', i', v', w', s', o', he', hK', hf', hco', -⟩
    · exact absurd (show Step1 (ℍ := ℍ) c.μ c.e _ _ from hs)
        (by rw [he]; exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK)
    · change c.e = _ at he'
      rw [he] at he'
      obtain ⟨rfl, hp⟩ := plug_perform_inj he'
      obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp
      simp only [Platform.restrict] at hco'
      split_ifs at hco' with hd
      obtain ⟨o'', hf'', hd''⟩ := hd
      rw [hf] at hf''
      cases hf''
      exact hd''

/-- A step at a configuration that keeps the protocol is a step under the restricted platform. -/
theorem pstep_restrict {P : Platform} {c c' : Conf P} (hPD : PlatData P c)
    (h : PStep (ℍ := ℍ) P c c') : PStep (ℍ := ℍ) P.restrict c.toRestrict c'.toRestrict := by
  cases h with
  | mach hs => exact PStep.mach hs
  | @plat μ s s' K n i v w o hK hf hco =>
      refine PStep.plat (P := P.restrict) hK hf ?_
      simp only [Platform.restrict]
      rw [if_pos ⟨o, hf, hPD K n i v o rfl hK hf⟩]
      exact hco

/-- **Every run of a program safe under the restricted platform keeps the protocol**: each
configuration it reaches asks the platform at data arguments only. -/
theorem platData_of_safe {P : Platform} {A : VTy} {e : Expr}
    (hS : SafeRuns (ℍ := ℍ) P.restrict A e) :
    ∀ c, PSteps (ℍ := ℍ) P (init P e) c →
      PlatData P c ∧ PSteps (ℍ := ℍ) P.restrict (init P.restrict e) c.toRestrict := by
  intro c h
  induction h with
  | refl =>
      have hr : PSteps (ℍ := ℍ) P.restrict (init P.restrict e) (init P e).toRestrict := .refl
      exact ⟨platData_of_safeAt (hS _ hr), hr⟩
  | tail _ hbc ih =>
      obtain ⟨hPD, hr⟩ := ih
      have hr' := hr.tail (pstep_restrict hPD hbc)
      exact ⟨platData_of_safeAt (hS _ hr'), hr'⟩

/-! ### B5 -/

/-- **The bump run follows a complete run** (`bump_follows`, at the configurations a bump run
reaches): from configurations related by `g`, where the bump side is reachable from the start, has
a finite memory, names nothing outside `Y` and has its windows for the steps to go, the bump run
takes a step wherever the given run does (`SafeRuns`'s progress and `bumpSimAt`), allocates
outside `Y` and outside every name of its earlier configurations, and ends `Final` where the given
run does. -/
theorem bump_follows_at {P : Platform} (hP : P.Respects) {A : VTy} {e : Expr}
    (hsafe : SafeRuns (ℍ := ℍ) P A e) (hPD : ∀ c, PSteps (ℍ := ℍ) P (init P e) c → PlatData P c) :
    ∀ (cs : List (Conf P)) (cA cB : Conf P) (g : Loc → Loc) (Y : Finset Loc),
      PRun (ℍ := ℍ) P (cA :: cs) → (∀ c, (cA :: cs).getLast? = some c → Final P A c) →
      RelAt g cA cB → BlocksAffine g cB.μ cB.e → AffineAbove g cB.μ cB.e cs.length →
      PSteps (ℍ := ℍ) P (init P e) cB → FinDom cB.μ → (∀ ℓ, Named cB.μ cB.e ℓ → ℓ ∈ Y) →
      ∃ (cs' : List (Conf P)) (gs : ℕ → Loc → Loc), cs'.length = cs.length ∧
        PRun (ℍ := ℍ) P (cB :: cs') ∧
        (∀ k ℓ, Allocated (cB :: cs') k ℓ →
          ℓ ∉ Y ∧ ∀ j c, j ≤ k → (cB :: cs')[j]? = some c → ¬ Named c.μ c.e ℓ) ∧
        (∀ c, (cB :: cs').getLast? = some c → Final P A c) ∧
        ∀ k (cA' cB' : Conf P), (cA :: cs)[k]? = some cA' → (cB :: cs')[k]? = some cB' →
          RelAt (gs k) cA' cB' := by
  intro cs
  induction cs with
  | nil =>
    intro cA cB g Y _ hF hR _ _ _ _ _
    refine ⟨[], fun _ => g, rfl, .one cB, ?_, ?_, ?_⟩
    · rintro k ℓ ⟨c, c', -, hc', -⟩
      simp at hc'
    · intro c hc
      simp only [List.getLast?_singleton, Option.some.injEq] at hc
      subst hc
      exact final_of_relAt hR (hF cA (by simp))
    · intro k cA' cB' h₁ h₂
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
        subst h₁; subst h₂; exact hR
      | succ k => simp at h₁
  | cons cA₁ cs₁ ih =>
    intro cA cB g Y hrun hF hR hB hAff hreach hfin hY
    cases hrun with
    | cons hstepA hrun₁ =>
      have hprog : ∃ cB'', PStep (ℍ := ℍ) P cB cB'' := by
        rcases hsafe cB hreach with ⟨v, hv, -, -⟩ | h
        · exact absurd hstepA (not_pstep_of_val (w := v.mapLoc g) (by rw [hR.2.1, hv]; rfl))
        · exact h
      obtain ⟨cB₁, g₁, hstepB, hfresh, -, hR₁, hB₁, hAff₁⟩ :=
        bumpSimAt P Y g cA cA₁ cB cs₁.length hP hfin hAff (hPD cB hreach) hR hB hstepA hprog
      obtain ⟨d₁, hd₁⟩ := finDom_pstep hstepB hfin
      obtain ⟨cs₁', gs₁, hlen, hrun', hbump, hF', hrel⟩ :=
        ih cA₁ cB₁ g₁ (Y ∪ (namedList cB₁.μ cB₁.e d₁).toFinset) hrun₁
          (fun c hc => hF c (by simpa using hc)) hR₁ hB₁ hAff₁ (hreach.tail hstepB) ⟨d₁, hd₁⟩
          (fun ℓ hn => Finset.mem_union_right _ (List.mem_toFinset.mpr (mem_namedList hd₁ hn)))
      refine ⟨cB₁ :: cs₁', fun k => Nat.casesOn k g gs₁, by simp [hlen], .cons hstepB hrun', ?_,
        fun c hc => hF' c (by simpa using hc), ?_⟩
      · intro k ℓ hA
        cases k with
        | zero =>
          obtain ⟨c, c', hc, hc', hn, hs⟩ := hA
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hc hc'
          subst hc; subst hc'
          obtain ⟨hnN, hnY⟩ := hfresh ℓ hn hs
          refine ⟨hnY, fun j c hj hc => ?_⟩
          obtain rfl : j = 0 := by omega
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc; exact hnN
        | succ k =>
          have hA' : Allocated (cB₁ :: cs₁') k ℓ := by
            obtain ⟨c, c', hc, hc', hn, hs⟩ := hA
            exact ⟨c, c', by simpa using hc, by simpa using hc', hn, hs⟩
          obtain ⟨hnY₁, hnN⟩ := hbump k ℓ hA'
          refine ⟨fun h => hnY₁ (Finset.mem_union_left _ h), fun j c hj hc => ?_⟩
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
            subst hc; exact fun hn => hnY₁ (Finset.mem_union_left _ (hY ℓ hn))
          | succ j => exact hnN j c (by omega) (by simpa using hc)
      · intro k cA' cB' h₁ h₂
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
          subst h₁; subst h₂; exact hR
        | succ k => exact hrel k cA' cB' (by simpa using h₁) (by simpa using h₂)

/-- **B5 from B4′** (RESTRUCTURE §2.4): B4′'s `SafeRuns` holds under every allocator and every
platform that keeps its protocol, the restricted one among them, so every run keeps the protocol
(`platData_of_safe`); the bump run from the same start is never stuck where the given run steps,
and `bumpSimAt` makes its step the given step's preimage, so it follows the given run to its end
(`bump_follows_at`); it reuses nothing, so it releases each cell once (`releasedOnce_of_ends`). -/
theorem releasedOnceReuse_of_soundContracts {J : TypingJ} {M : B.BWorld}
    (hC : B.SoundContracts (ℍ := ℍ) J M) : B.ReleasedOnceReuse (ℍ := ℍ) J M := by
  intro P hP Γ γ S A e hD hle hJ hW cs hrun hF
  have hsafe := (hC P hP Γ γ S A e hD hle hJ hW).1
  have hsafeR := (hC P.restrict (restrict_respects hP) Γ γ S A e hD hle hJ hW).1
  obtain ⟨cs', gs, hlen, hrun', hbump, hF', hrel⟩ :=
    bump_follows_at hP hsafe (fun c hc => (platData_of_safe hsafeR c hc).1) cs _ _ id
      (locsOf (substAll γ e)).toFinset hrun hF (relAt_init _) (fun _ _ _ _ _ => rfl)
      (affineAbove_id _ _ _) .refl ⟨[], fun _ h => absurd rfl h⟩
      (fun _ hn => List.mem_toFinset.mpr (named_init hn))
  have hB : Bump (init P (substAll γ e) :: cs') := fun k ℓ hA => (hbump k ℓ hA).2
  exact ⟨cs', gs, hlen, hrun', hB,
    releasedOnce_of_ends (init_vacant _ cs') (final_vacant hF') (noReuse_of_bump hB), hF', hrel⟩

/-- **B5 at today's unr-free kernel and BoLo.** -/
theorem releasedOnceReuse_tier1NU : B.ReleasedOnceReuse (ℍ := ℍ) tier1NU (B.coreB (ℍ := ℍ)) :=
  releasedOnceReuse_of_soundContracts soundContracts_tier1NU


end Targets

end
