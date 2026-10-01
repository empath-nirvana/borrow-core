import Core.EffPrograms

/-!
# Backend — kernel programs

The programs of `Core/` that the surface cannot spell, compiled by `bcc kernel`: the acceptance
programs of spec §19 whose operations the backend lowers (`Backend/Clos/Unwind.lean`). Each is a
closed term with a `CDerives` derivation in `Core/EffPrograms.lean`.
-/

namespace Backend
open BoCa.Fig16.LogRel.Core.EffPrograms

/-- The kernel programs `bcc kernel` compiles, by name. -/
def kernelPrograms : List (String × BoCa.Expr) :=
  [ ("log-outside", logOutside),
    ("fail-outside", failOutside),
    ("reborrow-raise", reborrowRaise),
    ("log-in-borrow", logInBorrow),
    ("tick-answering", tickAnsProg 3) ]

/-- The kernel programs whose operations the backend does not lower: control operations
(`perform`), whose continuations are captured. -/
def kernelProgramsControl : List (String × BoCa.Expr) :=
  [ ("log-outside-native", nLogOutside),
    ("fail-outside-native", nFailOutside),
    ("tick-native", tickProg 3),
    ("take", takeProg 1),
    ("store-cancel", storeCancel) ]

end Backend
