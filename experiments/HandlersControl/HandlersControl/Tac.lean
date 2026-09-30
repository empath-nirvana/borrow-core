import HandlersAsBorrows

/-!
# A tactic for consumed contexts

`dead` proves `Ctx.Dead Γ` for a context of consumed slots ending in `[]` or in a hypothesis.
`[about ours]`
-/

namespace HandlersControl

/-- Prove `Ctx.Dead Γ` by `cons` steps down to `[]` or a hypothesis. -/
syntax "dead" : tactic
macro_rules
  | `(tactic| dead) => `(tactic| first
      | assumption
      | exact BoCa.Ctx.Dead.nil
      | (apply BoCa.Ctx.Dead.cons; dead))

end HandlersControl
