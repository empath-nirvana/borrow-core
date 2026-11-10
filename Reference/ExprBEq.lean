import Paper.S1_Syntax.Definitions

/-!
# Reference — `==` on the erased term

The structural `BEq` of `BoCa.Expr`, derived once: the falsifier recognises the erased lend
combinators by it (`Reference/Falsify.lean`, `instrument`), and the old backend's conversion its
recognised terms (`Backend/Clos/Convert.lean`).
-/

deriving instance BEq for BoCa.Expr
