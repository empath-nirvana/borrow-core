-- The negative tests of scripts/check-type-eq.sh: each declaration compares kernel types outside
-- the helper, and `gate-census type-eq+scripts/census-neg/type-eq.lean` must list it (at `main`).
def Frontend.Check.negBeq (A B : Frontend.Check.CVTy) : Bool := A == B
def Frontend.Check.negDecide (C D : Frontend.Check.CCTy) : Bool := decide (C = D)
def Frontend.Check.negFind (S : Frontend.Check.CRow) (o : Frontend.Check.COpSig) : Bool :=
  (S.find? (· == o)).isSome
def Frontend.Check.negAlpha (A B : Frontend.Check.CVTy) : Bool :=
  BoCa.Fig16.LogRel.Core.VTy.alphaB [] A B
def Frontend.Sugar.negElab (A B : Frontend.Check.CVTy) : Bool := decide (A = B)
def Frontend.Check.negViaCore (ks : List BoCa.Fig16.LogRel.Core.FoldP.Bnd)
    (k : BoCa.Fig16.LogRel.Core.FoldP.Bnd) : BoCa.Expr :=
  BoCa.Fig16.LogRel.Core.FoldP.callE ks k
def Backend2.negHandle (g h : Backend2.HNode) : Bool :=
  decide (BoCa.Fig16.LogRel.Core.CTy.effOf g.S .unit = BoCa.Fig16.LogRel.Core.CTy.effOf h.S .unit) &&
    decide (g.E = h.E)
