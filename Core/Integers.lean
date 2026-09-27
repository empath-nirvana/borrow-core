import Core.Compat

/-!
# Core — Integers  `[spec §8]`

`I32` and `I64` (`VTy.int`), the literals and the host operations. The relation holds a literal
of the width at `∅` (`vCE`'s `int` clause), so the integer types are persistent, `Imm̲ 'b I = I`,
and they outlive every lifetime (`Types.lean`, `Persistent.lean`).

Each host operation `op` is typed `!(A ⊸ B)` at its signature (`hostArg op`, `hostRes op`), the
table of `SPEC.md` §8 read call-by-value. `hostOp_compatX` proves every operation sound at every
host `ℍ`: it uses only that `ℍ.call` answers a literal (a boolean, an optional literal) of the
stated type on well-typed arguments, which holds by the construction of `Host.call`. Nothing
about what the operations compute is used.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Signatures -/

/-- `I32`.  `[spec §8]` -/
abbrev VTy.i32 : VTy := .int .w32

/-- `I64`.  `[spec §8]` -/
abbrev VTy.i64 : VTy := .int .w64

/-- `1 ⊕ 1`, the tests' result: `inj₁ ()` is false, `inj₂ ()` true (`Val.bool`). -/
abbrev VTy.boolT : VTy := .sum .unit .unit

/-- The width of a literal. -/
def _root_.BoCa.IntLit.width : IntLit → Width
  | .i32 _ => .w32
  | .i64 _ => .w64

/-- The argument type of a host operation.  `[spec §8]` -/
def hostArg : HostOp → VTy
  | .bin w _ => .tensor (.int w) (.int w)
  | .div w _ => .tensor (.int w) (.int w)
  | .un w _ => .int w
  | .eqz w => .int w
  | .rel w _ => .tensor (.int w) (.int w)
  | .wrap => .int .w64
  | .extend_s => .int .w32
  | .extend_u => .int .w32
  | .extend32_s => .int .w64

/-- The result type of a host operation: `I`, `I ⊕ 1` for the partial operations, `1 ⊕ 1` for
the tests.  `[spec §8]` -/
def hostRes : HostOp → VTy
  | .bin w _ => .int w
  | .div w _ => .sum (.int w) .unit
  | .un w _ => .int w
  | .eqz _ => .boolT
  | .rel _ _ => .boolT
  | .wrap => .int .w32
  | .extend_s => .int .w64
  | .extend_u => .int .w64
  | .extend32_s => .int .w64

/-- `hostArg op ⊸ hostRes op` at value type: `U (A ⊸ F B)`.  `[spec §8]` -/
abbrev hostSig (op : HostOp) : VTy := .lolli (hostArg op) (hostRes op)

/-! ### The relation at the integer types -/

theorem vP_int_iff {w : Width} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vP (.int w) ls δ v ρ ↔ ρ = PMap.empty ∧ v.IsInt w := Iff.rfl

theorem vP_lit (c : IntLit) {ls : List SRec} {δ : LSub} :
    vP (.int c.width) ls δ ⟨.prim (.lit c), .prim⟩ PMap.empty := by
  cases c with
  | i32 n => exact ⟨rfl, n, rfl⟩
  | i64 n => exact ⟨rfl, n, rfl⟩

theorem vP_i32 (n : UInt32) {ls : List SRec} {δ : LSub} :
    vP (.int .w32) ls δ (Val.i32 n) PMap.empty := ⟨rfl, n, rfl⟩

theorem vP_i64 (n : UInt64) {ls : List SRec} {δ : LSub} :
    vP (.int .w64) ls δ (Val.i64 n) PMap.empty := ⟨rfl, n, rfl⟩

theorem vP_bool (b : Bool) {ls : List SRec} {δ : LSub} :
    vP .boolT ls δ (Val.bool b) PMap.empty := by
  cases b
  · exact Or.inl ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩
  · exact Or.inr ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

theorem vP_opt {w : Width} {o : Option Val} {ls : List SRec} {δ : LSub}
    (h : ∀ r, o = some r → vP (.int w) ls δ r PMap.empty) :
    vP (.sum (.int w) .unit) ls δ (Val.opt o) PMap.empty := by
  cases o with
  | some r => exact Or.inl ⟨r, pure_sep_mk rfl (h r rfl)⟩
  | none => exact Or.inr ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

/-- A pair of integers of one width, at `∅`. -/
theorem vP_int_pair {w : Width} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (.tensor (.int w) (.int w)) ls δ v ρ) :
    ρ = PMap.empty ∧ ∃ a b : Val, v = .pair a b ∧ a.IsInt w ∧ b.IsInt w := by
  obtain ⟨a, b, hk⟩ := h
  obtain ⟨he, ρ₁, ρ₂, hc, ⟨e₁, ha⟩, ⟨e₂, hb⟩⟩ := pure_sep_iff.mp hk
  subst e₁ e₂
  exact ⟨eq_empty_of_compS_empty hc, a, b, he, ha, hb⟩

/-! ### Every host answers at the stated type -/

/-- On an argument in the relation at `hostArg op`, every host answers, with a value in the
relation at `hostRes op` holding nothing.  By the construction of `Host.call`: the argument
decodes to literals of the stated width, and the answer is encoded at the stated type.
`[spec §8]` -/
theorem host_call_sound (H : Host) (op : HostOp) {ls ls' : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes} (h : vP (hostArg op) ls δ v ρ) :
    ρ = PMap.empty ∧ ∃ r, H.call op v = some r ∧ vP (hostRes op) ls' δ r PMap.empty := by
  cases op with
  | bin w o =>
      obtain ⟨rfl, a, b, rfl, ha, hb⟩ := vP_int_pair h
      refine ⟨rfl, ?_⟩
      cases w <;> obtain ⟨n, rfl⟩ := ha <;> obtain ⟨m, rfl⟩ := hb
      · exact ⟨_, rfl, vP_i32 _⟩
      · exact ⟨_, rfl, vP_i64 _⟩
  | div w o =>
      obtain ⟨rfl, a, b, rfl, ha, hb⟩ := vP_int_pair h
      refine ⟨rfl, ?_⟩
      cases w <;> obtain ⟨n, rfl⟩ := ha <;> obtain ⟨m, rfl⟩ := hb
      · refine ⟨_, rfl, vP_opt fun r hr => ?_⟩
        obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hr
        exact vP_i32 k
      · refine ⟨_, rfl, vP_opt fun r hr => ?_⟩
        obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hr
        exact vP_i64 k
  | un w o =>
      obtain ⟨rfl, ha⟩ := h
      refine ⟨rfl, ?_⟩
      cases w <;> obtain ⟨n, rfl⟩ := ha
      · exact ⟨_, rfl, vP_i32 _⟩
      · exact ⟨_, rfl, vP_i64 _⟩
  | eqz w =>
      obtain ⟨rfl, ha⟩ := h
      refine ⟨rfl, ?_⟩
      cases w <;> obtain ⟨n, rfl⟩ := ha
      · exact ⟨_, rfl, vP_bool _⟩
      · exact ⟨_, rfl, vP_bool _⟩
  | rel w o =>
      obtain ⟨rfl, a, b, rfl, ha, hb⟩ := vP_int_pair h
      refine ⟨rfl, ?_⟩
      cases w <;> obtain ⟨n, rfl⟩ := ha <;> obtain ⟨m, rfl⟩ := hb
      · exact ⟨_, rfl, vP_bool _⟩
      · exact ⟨_, rfl, vP_bool _⟩
  | wrap =>
      obtain ⟨rfl, n, rfl⟩ := h
      exact ⟨rfl, _, rfl, vP_i32 _⟩
  | extend_s =>
      obtain ⟨rfl, n, rfl⟩ := h
      exact ⟨rfl, _, rfl, vP_i64 _⟩
  | extend_u =>
      obtain ⟨rfl, n, rfl⟩ := h
      exact ⟨rfl, _, rfl, vP_i64 _⟩
  | extend32_s =>
      obtain ⟨rfl, n, rfl⟩ := h
      exact ⟨rfl, _, rfl, vP_i64 _⟩

/-! ### Compatibility -/

/-- A literal is in the relation at its width.  `[spec §8]` -/
theorem lit_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.int c.width) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  exact wpTS_val ls ⟨.prim (.lit c), .prim⟩ (fun ls' => vP (.int c.width) ls' δ) _ (vP_lit c)

/-- Every host operation is sound at `!(hostArg op ⊸ F (hostRes op))`, at every host: one
host step, which changes no memory, answers in the relation at `∅`.  `[spec §8]` -/
theorem hostOp_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim (.host op))) (.bang (hostSig op)) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  refine wpTS_val ls (Val.prim (.host op)) _ _ ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨rfl, r, hr, hres⟩ := host_call_sound ℍ op (ls' := ls') hv
  exact wpTS_head (fun μ => Head.host μ op v r hr) rfl ls' _ _ (wpTS_val ls' r _ _ hres)

end BoCa.Fig16.LogRel.Core
