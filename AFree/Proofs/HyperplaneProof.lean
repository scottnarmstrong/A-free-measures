module

public import AFree.Paper.Currents

/-!
# Proof of [DPR, Corollary 1.9]
-/

public section

open MeasureTheory

namespace AFree.HyperplaneProof

open AFree PDE

/-- [DPR, Corollary 1.9]: for boundaryless `(d-1)`-currents, the polars lie a.e. in `Λ_{d-1}(V)` for a hyperplane `V`. -/
theorem result {d r : ℕ}
    (T : Fin r → VectorMeasure (Vec d) (KVec d (d - 1)))
    (hT : ∀ i, IsBoundaryOn Set.univ (T i) 0)
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ V : Submodule ℝ (Vec d), Module.finrank ℝ V = d - 1 ∧
      ∀ i, polar (T i) x ∈ kvecSpan V (d - 1) :=
  ae_exists_hyperplane_of_boundaryless T hT μ hμ

end AFree.HyperplaneProof
