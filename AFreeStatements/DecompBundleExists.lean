module

public import AFree.Defs
public import AFree.Proofs.DecompBundleExistsProof

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-- Every finite measure has a decomposability bundle `V(μ, ·)` ([AM, Section 2.7 and
Lemma 2.3]). -/
theorem exists_isDecompBundle {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    ∃ V, IsDecompBundle μ V := by exact AFree.DecompBundleExistsProof.result μ

end AFree
