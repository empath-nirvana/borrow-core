import Core.TreeHeadlines

/-!
# Pool spike: the machine, and the table its branches are verified at

A configuration is the memory, at most one **active** branch, and a pool of branches each
**ready** (a closed program not yet started) or **parked** at the operation `(m₀, i₀)` with its
evaluation context and payload. A step: the active branch takes a `Step1`; an active branch
stopped at `(m₀, i₀)` parks; an active value finishes; with no branch active, any ready branch
starts or any parked branch is resumed at the answer `()`. Any branch of the pool may be chosen,
so every schedule of segments is a run of the machine.

The branches are verified at `cerwpT (opTableP T) Q`. `opTableP` is `opTableT` with the
continuation's share `contShareP` in place of `contShareT`: the resume asks for a re-reading of the
records of the stop's list that the share is relevant to (`RelFT`), present in the resume list,
where `contShareT` asks for a re-reading of the whole stop list and `extFT` against it. The
difference is the point of the spike's answer (`PoolSpike.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Pool
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE freeE opPayload)

/-! ### Contexts around a primitive application are unique -/

theorem plug_prim_not_val {a : Prim} (ha : a ≠ .store) {x : Val} :
    ∀ (K : Kont), ¬ IsVal (K.plug (.app (.prim a) x.1)) := by
  intro K h
  have h' := K.isVal_of_plug h
  cases h' with
  | storeV _ => exact ha rfl

/-- **A context around a primitive application of values is unique.** -/
theorem plug_prim_inj {a b : Prim} (ha : a ≠ .store) (hb : b ≠ .store) {x y : Val} :
    ∀ {K K' : Kont}, K.plug (.app (.prim a) x.1) = K'.plug (.app (.prim b) y.1) →
      K = K' ∧ a = b ∧ x = y := by
  intro K
  induction K with
  | hole =>
      intro K' h
      cases K' with
      | hole =>
          simp only [Kont.plug, Expr.app.injEq, Expr.prim.injEq] at h
          exact ⟨rfl, h.1, Subtype.ext h.2⟩
      | appR f K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (h.2 ▸ x.2) (plug_prim_not_val hb K')
      | appL K' v =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (h.1 ▸ IsVal.prim) (plug_prim_not_val hb K')
      | _ => simp [Kont.plug] at h
  | pairL K e ih =>
      intro K' h
      cases K' with
      | pairL K' e' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.1; exact ⟨by rw [h₁, h.2], h₂, h₃⟩
      | pairR v K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (by rw [h.1]; exact v.2) (plug_prim_not_val ha K)
      | _ => simp [Kont.plug] at h
  | pairR v K ih =>
      intro K' h
      cases K' with
      | pairL K' e' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (by rw [← h.1]; exact v.2) (plug_prim_not_val hb K')
      | pairR v' K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.2
          exact ⟨by rw [h₁, Subtype.ext h.1], h₂, h₃⟩
      | _ => simp [Kont.plug] at h
  | letpair K e ih =>
      intro K' h
      cases K' with
      | letpair K' e' =>
          simp only [Kont.plug, Expr.letpair.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.1; exact ⟨by rw [h₁, h.2], h₂, h₃⟩
      | _ => simp [Kont.plug] at h
  | case K e₁ e₂ ih =>
      intro K' h
      cases K' with
      | case K' e₁' e₂' =>
          simp only [Kont.plug, Expr.case.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.1; exact ⟨by rw [h₁, h.2.1, h.2.2], h₂, h₃⟩
      | _ => simp [Kont.plug] at h
  | appR f K ih =>
      intro K' h
      cases K' with
      | hole =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (h.2 ▸ y.2) (plug_prim_not_val ha K)
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.2; exact ⟨by rw [h₁, h.1], h₂, h₃⟩
      | appL K' v =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (by rw [h.2]; exact v.2) (plug_prim_not_val ha K)
      | _ => simp [Kont.plug] at h
  | appL K v ih =>
      intro K' h
      cases K' with
      | hole =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (h.1 ▸ IsVal.prim) (plug_prim_not_val ha K)
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (by rw [← h.2]; exact v.2) (plug_prim_not_val hb K')
      | appL K' v' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.1
          exact ⟨by rw [h₁, Subtype.ext h.2], h₂, h₃⟩
      | _ => simp [Kont.plug] at h
  | seq K e ih =>
      intro K' h
      cases K' with
      | seq K' e' =>
          simp only [Kont.plug, Expr.seq.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h.1; exact ⟨by rw [h₁, h.2], h₂, h₃⟩
      | _ => simp [Kont.plug] at h
  | inj₁ K ih =>
      intro K' h
      cases K' with
      | inj₁ K' =>
          simp only [Kont.plug, Expr.inj₁.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h; exact ⟨by rw [h₁], h₂, h₃⟩
      | _ => simp [Kont.plug] at h
  | inj₂ K ih =>
      intro K' h
      cases K' with
      | inj₂ K' =>
          simp only [Kont.plug, Expr.inj₂.injEq] at h
          obtain ⟨h₁, h₂, h₃⟩ := ih h; exact ⟨by rw [h₁], h₂, h₃⟩
      | _ => simp [Kont.plug] at h

/-! ### The machine -/

/-- A branch of the pool. -/
inductive PEnt where
  /-- A closed program, not yet started. -/
  | ready (e : Expr)
  /-- Stopped at the pool's operation, in the context `K`, with the payload `v`. -/
  | parked (K : Kont) (v : Val)

/-- A configuration of the pool machine. -/
structure PCfg where
  μ : Heap
  act : Option Expr
  pool : List PEnt

/-- **A step of the pool machine** at the operation `(m₀, i₀)`. -/
inductive PStep (m₀ i₀ : UInt32) : PCfg → PCfg → Prop
  | run {μ μ' : Heap} {e e' : Expr} {pool : List PEnt} :
      Step1 (ℍ := ℍ) μ e μ' e' → PStep m₀ i₀ ⟨μ, some e, pool⟩ ⟨μ', some e', pool⟩
  | park {μ : Heap} {K : Kont} {v : Val} {pool : List PEnt} :
      K.HasHnd m₀ = false →
      PStep m₀ i₀ ⟨μ, some (K.plug (performE (.val (opPayload m₀ i₀ v)))), pool⟩
        ⟨μ, none, .parked K v :: pool⟩
  | done {μ : Heap} {v : Val} {pool : List PEnt} :
      PStep m₀ i₀ ⟨μ, some v.1, pool⟩ ⟨μ, none, pool⟩
  | resume {μ : Heap} {K : Kont} {v : Val} {p₁ p₂ : List PEnt} :
      PStep m₀ i₀ ⟨μ, none, p₁ ++ .parked K v :: p₂⟩ ⟨μ, some (K.plug (.val .unit)), p₁ ++ p₂⟩
  | start {μ : Heap} {e : Expr} {p₁ p₂ : List PEnt} :
      PStep m₀ i₀ ⟨μ, none, p₁ ++ .ready e :: p₂⟩ ⟨μ, some e, p₁ ++ p₂⟩

/-- Runs of the pool machine, of a counted length. -/
inductive PRun (m₀ i₀ : UInt32) : Nat → PCfg → PCfg → Prop
  | refl (c : PCfg) : PRun m₀ i₀ 0 c c
  | step {t : Nat} {c c' c'' : PCfg} :
      PRun m₀ i₀ t c c' → PStep (ℍ := ℍ) m₀ i₀ c' c'' → PRun m₀ i₀ (t + 1) c c''

/-! ### The table -/

/-- What the resume list keeps of a stop list: every record of it the share is relevant to,
re-read. -/
def KeepRel {K K' : WCactus} (Θ' : CodeTy) (ls : List (SRecT K)) (ls' : List (SRecT K'))
    (ρ : TRes K) : Prop :=
  ∀ r ∈ rsOfT ls, RelFT r ρ → ∃ r' ∈ rsOfT ls', RecRR Θ' r r'

/-- **The continuation's share, resumed at the records it is relevant to.** As `contShareT`,
with the resume list's condition `KeepRel` read against the stop list itself: no re-reading of
the stop list's other records is asked for. -/
def contShareP (en : OpEntT) (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (K : Kont) (v : Val) (Ψ : ContT) : TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    (∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → Ψ (fdAt en v F O') w' O' k' ls' (K.plug (.val a)) σ') ∧
    (en.q ≠ .lin → ∀ P, en.fin = some P →
      P k w' ls' (K.dead.plug (BoLo.raiseE (.val (BoLo.cancelVal none)))) ρ')

/-- `opTableT` at `contShareP`. -/
def opTableP (T : OpTabT) : TableT := fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ en.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.PA k w ls v ρa ∧ contShareP en F k w ls O K v Ψ ρk

theorem opTableP_local (T : OpTabT) : (opTableP T).Local := by
  intro F k w ls O t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩ := h
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu,
    fun w' ρ' ls' O' hE hr hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      hΨ _ _ _ k' hk _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).1 k' hk a σ σ' hB hcσ),
      (hcont w' ρ' ls' O' hE hr hx hO).2⟩⟩

/-- **`contShareP` gives `contShareT`'s resume**: a re-reading of the whole stop list, with
`extFT` against it, keeps the relevant records. So every resume `contShareT` admits, `contShareP`
admits. -/
theorem keepRel_of_extFT {K K' : WCactus} {Θ' : CodeTy} {ls : List (SRecT K)}
    {lsR ls' : List (SRecT K')} {ρ : TRes K} {ρ' : TRes K'} (hl : SRecsRR Θ' ls lsR)
    (hr : RR (sem Θ') ρ ρ') (hx : extFT lsR ls' ρ') : KeepRel Θ' ls ls' ρ := by
  intro r hr₀ hrel
  obtain ⟨r', hr', hrr⟩ := hl.mem_fwd hr₀
  exact ⟨r', hx r' hr' ((RelFT.rr_iff hrr hr).mp hrel), hrr⟩

/-- **A stop at the pool's operation, at every extension of the world.** -/
theorem cerwpP_perform {T : OpTabT} {Q : TPostV} {F : TFrame} (K : Kont) {m i : UInt32}
    {v : Val} {en : OpEntT} (hK : K.HasHnd m = false) (hT : T m i = some en)
    (ha : en.abort = false) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      en.oc w₀ O₀ ∧ ∃ ρa ρk : TRes w₀.K, ResUT.CompS ρa ρk ρ₀ ∧ en.PA n w₀ ls₀ v ρa ∧
        contShareP en F n w₀ ls₀ O₀ K v (cerwpTC (ℍ := ℍ) (opTableP T) Q n) ρk) :
    cerwpT (ℍ := ℍ) (opTableP T) Q F n w ls O (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [cerwpT_eq]
  refine twp_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK)
    fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => Or.inr ?_
  obtain ⟨hoc, ρa, ρk, hc, hA, hs⟩ := h w₀ ρ₀ ls₀ O₀ hE hr hl hO
  exact ⟨K, m, i, v, en, rfl, hK, hT, ha, hoc, ρa, ρk, hc, hA, hs⟩

end BoCa.Fig16.Tree.Wp.Pool

end
