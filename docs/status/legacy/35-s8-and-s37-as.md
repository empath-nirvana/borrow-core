
§8 and §37 as restated in 0.70 are implemented in `Support/Dynamics/Floats.lean` (`NaNs`, every
float operation at a resolution, `NaNEq` and its lemmas), `Support/Dynamics/Host.lean`
(`Prim`, `wasmHostAt`, `Host.Conforms`, `wasmHostAt_conforms`, `wasmHost_conforms`),
`Backend/Clos/Interp.lean` (`closHost`), `Target/Flat/Interp.lean` (`flatHost`) and
`Backend/Flat/Lower.lean` (`hostVals` without the NaN test); no change to `CDerives`, the relation,
the machine, `Core/`, `Paper/` or the checker.
