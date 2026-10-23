module

public import AFree.Rademacher.Chain

/-!
# Proof of [DPR, Theorem 1.14]
-/

public section

open MeasureTheory

namespace AFree.RademacherConverseProof

open AFree PDE

/-- [DPR, Theorem 1.14]: if every Lipschitz function is differentiable `μ`-a.e.,
then `μ ≪ 𝓛^d`. -/
theorem result {d : ℕ} (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ f : Vec d → ℝ, (∃ K, LipschitzWith K f) → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x) :
    μ ≪ volume :=
  Rademacher.thm_rademacher μ hμ

end AFree.RademacherConverseProof
