module

public import AFree.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import AFree.Proofs.HyperplaneProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Corollary 1.9]: for normal `(d-1)`-currents `T₁, …, T_r` on `ℝ^d` without boundary and a
locally finite measure `μ ≪ ‖Tᵢ‖`, at `μˢ`-almost every point there is a hyperplane `V` with
`T⃗ᵢ(x) ∈ Λ_{d-1}(V)` for all `i`. -/
theorem exists_hyperplane_of_boundaryless {d r : ℕ}
    (T : Fin r → VectorMeasure (Vec d) (KVec d (d - 1)))
    (hT : ∀ i, IsBoundaryOn Set.univ (T i) 0)
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ V : Submodule ℝ (Vec d), Module.finrank ℝ V = d - 1 ∧
      ∀ i, polar (T i) x ∈ kvecSpan V (d - 1) := by exact AFree.HyperplaneProof.result T hT μ hμ

end AFree
