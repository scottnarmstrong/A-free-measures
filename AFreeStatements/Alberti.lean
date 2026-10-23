module

public import AFree.Defs
public import AFree.Proofs.AlbertiProof

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Theorem 1.5] (Alberti's rank-one theorem): for `u ∈ BV(Ω; ℝ^ℓ)`, at `|Dˢu|`-almost
every point the polar of `Dˢu` is `a ⊗ b` with `a ≠ 0` and `b ≠ 0`. -/
theorem polar_lebesgueSingularPart_eq_tensor {d ℓ : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)) (hDu : IsBVGradientOn Ω u Du) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Du),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Du) x = fun p => a p.1 * b p.2 := by exact AFree.AlbertiProof.result Ω hΩ u Du hDu

end AFree
