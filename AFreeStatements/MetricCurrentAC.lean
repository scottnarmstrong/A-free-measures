module

public import AFree.Defs
public import AFree.Proofs.MetricCurrentACProof

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-- [DPR, Theorem 1.15]: the mass `‖T‖` of every metric `d`-current `T` in `ℝ^d` is absolutely
continuous with respect to `𝓛^d`. -/
theorem absolutelyContinuous_of_isAKMass {d : ℕ} (T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ)
    (hT : IsMetricCurrent d T) (μ : Measure (Vec d)) (hμ : IsAKMass T μ) : μ ≪ volume := by exact AFree.MetricCurrentACProof.result T hT μ hμ

end AFree
