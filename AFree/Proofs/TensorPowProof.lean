module

public import AFree.Paper.TensorPow

/-!
# Proof of [DPR, Theorem 1.6]
-/

public section

open MeasureTheory

namespace AFree.TensorPowProof

open AFree PDE

/-- [DPR, Theorem 1.6] (rank-one structure `a ⊗ b^{⊗ r}` of `Dʳu`). -/
theorem result {d ℓ r : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)) (hDr : IsDerivMeasureOn Ω u r Dr) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Dr),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Dr) x = fun p => a p.1 * ∏ m, b (p.2 m) :=
  ae_polar_lebesgueSingularPart_tensorPow hΩ hDr

end AFree.TensorPowProof
