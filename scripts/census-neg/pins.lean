-- The negative tests of scripts/check-pins.sh: `gate-census pins+scripts/census-neg/pins.lean` must
-- refuse each of these declarations.
def Backend2.installConsume (x : Backend2.Var) (b : Backend2.Tm) : Backend2.Tm := .consume .unused x b
def Backend2.theRule : Backend2.ConsumeRule := .consume
def Backend2.useRule (x : Backend2.Var) (b : Backend2.Tm) : Backend2.Tm := .consume Backend2.theRule x b
