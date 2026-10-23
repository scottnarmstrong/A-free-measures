module

public import AFree.Paper.Currents

/-!
# Proof of [DPR, Corollary 1.12]
-/

public section

open MeasureTheory

namespace AFree.SpanAbsContProof

open AFree PDE

/-- [DPR, Corollary 1.12]: if the polars of `d` normal 1-currents span `ℝ^d` `μ`-a.e. and `μ ≪ |Tᵢ|`, then `μ ≪ 𝓛^d`. -/
theorem result {d : ℕ}
    (T : Fin d → VectorMeasure (Vec d) (KVec d 1)) (hT : ∀ i, IsNormalCurrentOn Set.univ (T i))
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i))
    (hspan : ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤) :
    μ ≪ volume :=
  absolutelyContinuous_of_span_polar_eq_top T hT μ hμ hspan

end AFree.SpanAbsContProof
