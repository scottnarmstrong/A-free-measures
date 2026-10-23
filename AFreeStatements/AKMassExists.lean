module

public import AFree.Defs
public import AFree.Proofs.AKMassExistsProof

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-- [AK, Definition 2.6]: a metric functional with finite mass has a mass `‖T‖`, the least finite
measure satisfying [AK, (2.2)]. -/
theorem exists_isAKMass {d k : ℕ} (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ)
    (hT : IsMetricFunctional k T) (hfin : ∃ μ, IsAKMassAdmissible T μ) :
    ∃ μ, IsAKMass T μ := by exact AFree.AKMassExistsProof.result T hT hfin

end AFree
