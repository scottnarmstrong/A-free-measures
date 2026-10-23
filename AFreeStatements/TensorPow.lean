module

public import AFree.Defs
public import AFree.Proofs.TensorPowProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.6]: if the `r`-th derivative `Dʳu` of `u ∈ L¹(Ω; ℝ^ℓ)` is a measure, then at
`|Dʳu|ˢ`-almost every point its polar is `a ⊗ b^{⊗r}` with `a ≠ 0` and `b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_tensorPow {d ℓ r : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)) (hDr : IsDerivMeasureOn Ω u r Dr) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Dr),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Dr) x = fun p => a p.1 * ∏ m, b (p.2 m) := by exact AFree.TensorPowProof.result Ω hΩ u Dr hDr

end AFree
