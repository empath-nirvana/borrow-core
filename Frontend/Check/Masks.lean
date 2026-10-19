import Core.Fundamental
import Core.Records

/-!
# Frontend — Check — the use masks of a split  `[spec §3, §10]`

A node of the typed term at a split (`Ctx.SplitP Γ Γ₁ Γ₂`) carries the use masks of its two parts
(`Masks`): which slots of the node's context each part uses, as the checker found them (`Fam.u`,
`Frontend/Check/Fam.lean`). The typed derivation relates them to the split it is at
(`SplitMasks`, a premise of every typed split rule, `Frontend/Check/TDerives.lean`):

* a slot a part uses is live in that part's context;
* a slot live in both parts' contexts is used by both.

So the slots a split gives to both parts, which `Ctx.SplitP` admits only at a persistent type
(`dup`), are exactly the slots both masks hold (`SplitMasks.both_iff`, `SplitMasks.both_persistent`).
That is the copy set: a persistent value used on both sides of a split is copied, and no other
(`Frontend/Check/Copies.lean`).
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa

/-- The use masks of a split's two parts, over the slots of the node's context: at each slot,
whether the left part uses it and whether the right part does. One list, so that a body placed
at a use moves one list past the use's slots (`Masks.ins`). -/
structure Masks where
  ms : List (Bool × Bool)
  deriving Inhabited, DecidableEq

/-- The left part's mask. -/
def Masks.u₁ (m : Masks) : List Bool := m.ms.map Prod.fst

/-- The right part's mask. -/
def Masks.u₂ (m : Masks) : List Bool := m.ms.map Prod.snd

/-- The masks of two parts, slot by slot. -/
def Masks.of (a b : List Bool) : Masks := ⟨List.zip a b⟩

theorem Masks.of_u₁ {a b : List Bool} (h : a.length = b.length) : (Masks.of a b).u₁ = a := by
  simp [Masks.of, Masks.u₁, List.map_fst_zip, h]

theorem Masks.of_u₂ {a b : List Bool} (h : a.length = b.length) : (Masks.of a b).u₂ = b := by
  simp [Masks.of, Masks.u₂, List.map_snd_zip, h]

/-- **The masks of a split's parts are the ones its contexts have**: pointwise, a slot a part uses
is live in its context, and a slot live in both contexts is used by both.  `[spec §3]` -/
inductive SplitMasks : Ctx VTy → Ctx VTy → List Bool → List Bool → Prop where
  | nil : SplitMasks [] [] [] []
  | cons {A₁ A₂ : VTy} {l₁ l₂ a b : Bool} {Γ₁ Γ₂ : Ctx VTy} {as bs : List Bool}
      (h₁ : a = true → l₁ = true) (h₂ : b = true → l₂ = true)
      (hd : l₁ = true → l₂ = true → a = true ∧ b = true) (h : SplitMasks Γ₁ Γ₂ as bs) :
      SplitMasks (⟨A₁, l₁⟩ :: Γ₁) (⟨A₂, l₂⟩ :: Γ₂) (a :: as) (b :: bs)

/-- Whether slot `k` of `Γ` is live. -/
def liveAt (Γ : Ctx VTy) (k : Nat) : Bool := (Γ[k]?.map Slot.live).getD false

/-- The relation at a node's masks. -/
abbrev Masks.Rel (m : Masks) (Γ₁ Γ₂ : Ctx VTy) : Prop := SplitMasks Γ₁ Γ₂ m.u₁ m.u₂

/-- `d` unused slots inserted at position `c` of a use mask. -/
def insMask (d : Nat) : Nat → List Bool → List Bool
  | 0, u => List.replicate d false ++ u
  | c + 1, a :: u => a :: insMask d c u
  | _ + 1, [] => List.replicate d false

theorem insMask_eq (d : Nat) : ∀ (c : Nat) (u : List Bool),
    insMask d c u = u.take c ++ List.replicate d false ++ u.drop c
  | 0, u => by simp [insMask]
  | c + 1, a :: u => by simp [insMask, insMask_eq d c u]
  | _ + 1, [] => by simp [insMask]

/-- `d` unused slots inserted at position `c` of both masks. -/
def insPair (d : Nat) : Nat → List (Bool × Bool) → List (Bool × Bool)
  | 0, u => List.replicate d (false, false) ++ u
  | c + 1, a :: u => a :: insPair d c u
  | _ + 1, [] => List.replicate d (false, false)

/-- Both masks with `d` unused slots inserted at position `c`. -/
def Masks.ins (d c : Nat) (m : Masks) : Masks := ⟨insPair d c m.ms⟩

theorem insPair_fst (d : Nat) : ∀ (c : Nat) (u : List (Bool × Bool)),
    (insPair d c u).map Prod.fst = insMask d c (u.map Prod.fst)
  | 0, u => by simp [insPair, insMask, List.map_replicate]
  | c + 1, a :: u => by simp [insPair, insMask, insPair_fst d c u]
  | _ + 1, [] => by simp [insPair, insMask, List.map_replicate]

theorem insPair_snd (d : Nat) : ∀ (c : Nat) (u : List (Bool × Bool)),
    (insPair d c u).map Prod.snd = insMask d c (u.map Prod.snd)
  | 0, u => by simp [insPair, insMask, List.map_replicate]
  | c + 1, a :: u => by simp [insPair, insMask, insPair_snd d c u]
  | _ + 1, [] => by simp [insPair, insMask, List.map_replicate]

theorem Masks.ins_u₁ (d c : Nat) (m : Masks) : (m.ins d c).u₁ = insMask d c m.u₁ :=
  insPair_fst d c m.ms

theorem Masks.ins_u₂ (d c : Nat) (m : Masks) : (m.ins d c).u₂ = insMask d c m.u₂ :=
  insPair_snd d c m.ms

/-- Whether both parts use slot `i`: the copy set. -/
def Masks.both (m : Masks) (i : Nat) : Bool := match m.ms[i]? with
  | some (a, b) => a && b
  | none => false

/-- A mask of no slot, as long as `u`. -/
def noUse (u : List Bool) : List Bool := u.map fun _ => false

/-- The slots a mask holds are live in `Γ`, and the mask is as long as `Γ`. -/
def UsedLive (u : List Bool) (Γ : Ctx VTy) : Prop :=
  u.length = Γ.length ∧ ∀ k, u.getD k false = true → liveAt Γ k = true

namespace SplitMasks

theorem length {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool} (h : SplitMasks Γ₁ Γ₂ u₁ u₂) :
    u₁.length = Γ₁.length ∧ u₂.length = Γ₁.length ∧ Γ₂.length = Γ₁.length := by
  induction h with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons _ _ _ _ ih => simp [ih.1, ih.2.1, ih.2.2]

/-- The relation at the masks of two parts. -/
theorem rel_of {Γ₁ Γ₂ : Ctx VTy} {a b : List Bool} (h : SplitMasks Γ₁ Γ₂ a b) :
    (Masks.of a b).Rel Γ₁ Γ₂ := by
  have hl : a.length = b.length := by have := h.length; omega
  show SplitMasks Γ₁ Γ₂ (Masks.of a b).u₁ (Masks.of a b).u₂
  rw [Masks.of_u₁ hl, Masks.of_u₂ hl]; exact h

/-- **The slots both parts receive are the slots both masks hold.** -/
theorem both_iff {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool} (h : SplitMasks Γ₁ Γ₂ u₁ u₂) :
    ∀ k, (liveAt Γ₁ k = true ∧ liveAt Γ₂ k = true) ↔
      (u₁.getD k false = true ∧ u₂.getD k false = true) := by
  induction h with
  | nil => intro k; simp [liveAt]
  | @cons A₁ A₂ l₁ l₂ a b _ _ _ _ h₁ h₂ hd _ ih =>
      intro k
      cases k with
      | zero =>
          simp only [liveAt, List.getElem?_cons_zero, Option.map_some, Option.getD_some,
            List.getD_cons_zero]
          constructor
          · rintro ⟨e₁, e₂⟩; exact hd e₁ e₂
          · rintro ⟨e₁, e₂⟩; exact ⟨h₁ e₁, h₂ e₂⟩
      | succ k => simpa [liveAt] using ih k

/-- Two masks of no slot. -/
theorem replicate (d : Nat) : ∀ {Γ₁ Γ₂ : Ctx VTy}, Γ₁.length = d → Γ₂.length = d →
    (∀ k, ¬ (liveAt Γ₁ k = true ∧ liveAt Γ₂ k = true)) →
    SplitMasks Γ₁ Γ₂ (List.replicate d false) (List.replicate d false)
  | [], [], h₁, _, _ => by subst h₁; exact .nil
  | ⟨A₁, l₁⟩ :: Γ₁, ⟨A₂, l₂⟩ :: Γ₂, h₁, h₂, hn => by
      simp only [List.length_cons] at h₁ h₂
      subst h₁
      rw [List.replicate_succ]
      refine .cons (by simp) (by simp) (fun e₁ e₂ => absurd ⟨by simpa [liveAt] using e₁, by simpa [liveAt] using e₂⟩
        (hn 0)) (replicate _ rfl (by omega) fun k hk => hn (k + 1) (by simpa [liveAt] using hk))
  | [], _ :: _, h₁, h₂, _ => by simp at h₁ h₂; omega
  | _ :: _, [], h₁, h₂, _ => by simp at h₁ h₂; omega

theorem append {a₁ a₂ b₁ b₂ : Ctx VTy} {u₁ u₂ v₁ v₂ : List Bool}
    (ha : SplitMasks a₁ a₂ u₁ u₂) (hb : SplitMasks b₁ b₂ v₁ v₂) :
    SplitMasks (a₁ ++ b₁) (a₂ ++ b₂) (u₁ ++ v₁) (u₂ ++ v₂) := by
  induction ha with
  | nil => exact hb
  | cons h₁ h₂ hd _ ih => exact .cons h₁ h₂ hd ih

theorem split_at : ∀ (c : Nat) {a₁ a₂ b₁ b₂ : Ctx VTy} {u₁ u₂ : List Bool}, a₁.length = c →
    a₂.length = c → SplitMasks (a₁ ++ b₁) (a₂ ++ b₂) u₁ u₂ →
    SplitMasks a₁ a₂ (u₁.take c) (u₂.take c) ∧ SplitMasks b₁ b₂ (u₁.drop c) (u₂.drop c)
  | 0, [], [], _, _, _, _, _, _, h => by simpa using ⟨SplitMasks.nil, h⟩
  | c + 1, _ :: a₁, _ :: a₂, _, _, _, _, h₁, h₂, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁ h₂
      simp only [List.cons_append] at h
      cases h with
      | cons k₁ k₂ kd h =>
          obtain ⟨ha, hb⟩ := split_at c h₁ h₂ h
          exact ⟨.cons k₁ k₂ kd ha, hb⟩
  | 0, _ :: _, _, _, _, _, _, h₁, _, _ => by simp at h₁
  | 0, [], _ :: _, _, _, _, _, _, h₂, _ => by simp at h₂
  | _ + 1, [], _, _, _, _, _, h₁, _, _ => by simp at h₁
  | _ + 1, _ :: _, [], _, _, _, _, _, h₂, _ => by simp at h₂

/-- **Inserted slots that no part uses and no two parts share**: the masks with the slots
inserted. -/
theorem ins {a₁ a₂ b₁ b₂ p₁ p₂ : Ctx VTy} {m : Masks} {c d : Nat}
    (hm : m.Rel (a₁ ++ b₁) (a₂ ++ b₂)) (h₁ : a₁.length = c) (h₂ : a₂.length = c)
    (hp : SplitMasks p₁ p₂ (List.replicate d false) (List.replicate d false)) :
    (m.ins d c).Rel (a₁ ++ p₁ ++ b₁) (a₂ ++ p₂ ++ b₂) := by
  obtain ⟨ha, hb⟩ := split_at c h₁ h₂ hm
  show SplitMasks _ _ (m.ins d c).u₁ (m.ins d c).u₂
  rw [Masks.ins_u₁, Masks.ins_u₂]
  simpa [insMask_eq, List.append_assoc] using (ha.append hp).append hb

/-- A slot both parts use is live in the split's context, at a persistent type. -/
theorem both_persistent {Γ Γ₁ Γ₂ : Ctx VTy} {m : Masks} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hm : m.Rel Γ₁ Γ₂) : ∀ k, m.u₁.getD k false = true → m.u₂.getD k false = true →
      ∃ s, Γ[k]? = some s ∧ s.live = true ∧ s.ty.Persistent := by
  intro k e₁ e₂
  have hb := ((both_iff hm k).mpr ⟨e₁, e₂⟩)
  clear hm e₁ e₂
  induction hs generalizing k with
  | nil => simp [liveAt] at hb
  | left _ ih | right _ ih | dead _ ih =>
      cases k with
      | zero => simp [liveAt] at hb
      | succ k => simpa using ih k (by simpa [liveAt] using hb)
  | dup hT _ ih =>
      cases k with
      | zero => exact ⟨_, rfl, rfl, hT⟩
      | succ k => simpa using ih k (by simpa [liveAt] using hb)

/-- A part's mask holds only live slots of its context. -/
theorem left_live {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool} (h : SplitMasks Γ₁ Γ₂ u₁ u₂) :
    UsedLive u₁ Γ₁ := by
  induction h with
  | nil => exact ⟨rfl, fun k hk => by simp at hk⟩
  | cons h₁ _ _ _ ih =>
      refine ⟨by simp [ih.1], fun k hk => ?_⟩
      cases k with
      | zero => simpa [liveAt] using h₁ (by simpa using hk)
      | succ k => simpa [liveAt] using ih.2 k (by simpa using hk)

theorem right_live {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool} (h : SplitMasks Γ₁ Γ₂ u₁ u₂) :
    UsedLive u₂ Γ₂ := by
  induction h with
  | nil => exact ⟨rfl, fun k hk => by simp at hk⟩
  | cons _ h₂ _ _ ih =>
      refine ⟨by simp [ih.1], fun k hk => ?_⟩
      cases k with
      | zero => simpa [liveAt] using h₂ (by simpa using hk)
      | succ k => simpa [liveAt] using ih.2 k (by simpa using hk)

/-- **A split that gives one part every slot** (`split_kill'`): that part's mask, and none for the
other. -/
theorem kill_right : ∀ {Γ : Ctx VTy} {u : List Bool}, UsedLive u Γ →
    SplitMasks Γ (kill Γ) u (noUse u)
  | [], [], _ => .nil
  | ⟨A, l⟩ :: Γ, a :: u, ⟨hl, hu⟩ => by
      simp only [kill, List.map_cons, noUse] at *
      exact .cons (fun h => by simpa [liveAt] using hu 0 (by simpa using h)) (by simp)
        (fun _ h => by simp at h)
        (kill_right ⟨by simpa using hl, fun k hk => by simpa [liveAt] using hu (k + 1) (by simpa using hk)⟩)
  | [], _ :: _, ⟨hl, _⟩ => by simp at hl
  | _ :: _, [], ⟨hl, _⟩ => by simp at hl

/-- The split of a consumed context into two copies of it, at masks of no slot. -/
theorem dead : ∀ {Γ : Ctx VTy} {u : List Bool}, Ctx.Dead Γ → u.length = Γ.length →
    SplitMasks Γ Γ (noUse u) (noUse u)
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, .cons h, hl => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      exact .cons (by simp) (by simp) (fun h _ => by simp at h) (dead h hl)
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

end SplitMasks

end BoCa.Fig16.LogRel.Core.Check
