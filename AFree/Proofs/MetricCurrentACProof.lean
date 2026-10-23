module

public import AFree.TopCurrents.Assembly.CurrAC

/-!
# Proof of [DPR, Theorem 1.15], absolute continuity

The mass of a top-dimensional metric current satisfies `‖T‖ ≪ 𝓛^d`. The proof is `AFree.curr_ac`.
-/

public section

open MeasureTheory

namespace AFree.MetricCurrentACProof

open PDE

/-- [DPR, Theorem 1.15]: `‖T‖ ≪ 𝓛^d` for a top-dimensional metric current `T`. -/
theorem result {d : ℕ} (T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ)
    (hT : IsMetricCurrent d T) (μ : Measure (Vec d)) (hμ : IsAKMass T μ) : μ ≪ volume :=
  curr_ac hT hμ

end AFree.MetricCurrentACProof
