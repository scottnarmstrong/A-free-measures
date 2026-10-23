module

public import AFree.Defs
public import AFree.Proofs.RademacherConverseProof

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal unitInterval

namespace AFree

open PDE

/-- [DPR, Theorem 1.14] (converse of Rademacher's theorem): if every Lipschitz function on `ℝ^d`
is differentiable `μ`-almost everywhere, then `μ ≪ 𝓛^d`. -/
theorem absolutelyContinuous_of_ae_differentiableAt {d : ℕ} (μ : Measure (Vec d))
    [IsLocallyFiniteMeasure μ]
    (hμ : ∀ f : Vec d → ℝ, (∃ K, LipschitzWith K f) → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x) :
    μ ≪ volume := by exact AFree.RademacherConverseProof.result μ hμ

end AFree
