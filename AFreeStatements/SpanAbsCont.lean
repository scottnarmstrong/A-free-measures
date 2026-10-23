module

public import AFree.Defs
public import AFree.Proofs.SpanAbsContProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Corollary 1.12]: if `μ ≪ ‖Tᵢ‖` for normal `1`-currents `T₁, …, T_d` on `ℝ^d` whose
polars span `ℝ^d` at `μ`-almost every point, then `μ ≪ 𝓛^d`. -/
theorem absolutelyContinuous_of_span_eq_top {d : ℕ}
    (T : Fin d → VectorMeasure (Vec d) (KVec d 1)) (hT : ∀ i, IsNormalCurrentOn Set.univ (T i))
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i))
    (hspan : ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤) :
    μ ≪ volume := by exact AFree.SpanAbsContProof.result T hT μ hμ hspan

end AFree
