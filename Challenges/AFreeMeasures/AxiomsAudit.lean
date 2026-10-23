module

public import AFreeStatements.WaveConeBridge
public import AFreeStatements.FirstOrderMain
public import AFreeStatements.GeneralMain
public import AFreeStatements.WaveConeBridgeK
public import AFreeStatements.MeasureRhs
public import AFreeStatements.VariableCoeff
public import AFreeStatements.Alberti
public import AFreeStatements.TensorPow
public import AFreeStatements.BD
public import AFreeStatements.BDOrth
public import AFreeStatements.Hyperplane
public import AFreeStatements.CovectorKernel
public import AFreeStatements.InteriorProductKernel
public import AFreeStatements.SimpleLinAlg
public import AFreeStatements.SimpleAE
public import AFreeStatements.SimpleCounterexample
public import AFreeStatements.SpanAbsCont
public import AFreeStatements.DivRank
public import AFreeStatements.BesselCompact
public import AFreeStatements.RademacherConverse
public import AFreeStatements.DecompBundleExists
public import AFreeStatements.DecompBundleIff
public import AFreeStatements.AKMassExists
public import AFreeStatements.MetricCurrentAC
public import AFreeStatements.FlatChain

/-!
# Axiom report

The axioms used by the 25 main theorems. Each must be exactly `propext`, `Classical.choice` and
`Quot.sound`; `scripts/check_axioms.py` checks the output of
`lake env lean Challenges/AFreeMeasures/AxiomsAudit.lean`.
-/

#print axioms AFree.mem_waveConeFirstOrder_iff_complexSymbol
#print axioms AFree.polar_mem_waveConeFirstOrder
#print axioms AFree.polar_mem_waveCone
#print axioms AFree.mem_waveCone_iff_complexSymbol
#print axioms AFree.polar_mem_waveCone_of_eq_measure
#print axioms AFree.polar_mem_waveCone_var
#print axioms AFree.polar_lebesgueSingularPart_eq_tensor
#print axioms AFree.polar_lebesgueSingularPart_eq_tensorPow
#print axioms AFree.polar_lebesgueSingularPart_eq_symmTensor
#print axioms AFree.polar_lebesgueSingularPart_eq_symmTensor_orth
#print axioms AFree.exists_hyperplane_of_boundaryless
#print axioms AFree.exists_covector_interiorProduct_eq_zero
#print axioms AFree.interiorProduct_eq_zero_iff_mem_kvecSpan
#print axioms AFree.isSimpleKVec_of_mem_kvecSpan
#print axioms AFree.ae_isSimpleKVec_of_isLocNormalCurrent
#print axioms AFree.not_ae_isSimpleKVec_example
#print axioms AFree.absolutelyContinuous_of_span_eq_top
#print axioms AFree.rank_polar_le_of_div_eq
#print axioms AFree.exists_compact_besselPotential
#print axioms AFree.absolutelyContinuous_of_ae_differentiableAt
#print axioms AFree.exists_isDecompBundle
#print axioms AFree.decompBundle_eq_top_iff
#print axioms AFree.exists_isAKMass
#print axioms AFree.absolutelyContinuous_of_isAKMass
#print axioms AFree.isTopFlatChain_iff_isMetricCurrent
