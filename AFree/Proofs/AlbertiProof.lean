module

public import AFree.Proofs.FirstOrderMainProof
public import AFree.Paper.AlbertiAssembly

@[expose] public section

open MeasureTheory Matrix

namespace AFree.AlbertiProof

open PDE AFree

/-- [DPR, Theorem 1.5]: the singular part of `Du` for `u ∈ BV` has rank-one polar, obtained from
[DPR, Theorem 1.1] for the curl operator. -/
theorem result {d ℓ : ℕ}
    (Ω : Set (Vec d)) (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)) (hDu : IsBVGradientOn Ω u Du) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Du),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Du) x = fun p => a p.1 * b p.2 :=
  polar_lebesgueSingularPart_eq_tensor_of_main Du
    (albertiInstance_of_main
      (fun Ω hΩ A A₀ μ hμ hfree => FirstOrderMainProof.result Ω hΩ A A₀ μ hμ hfree)
      hΩ u Du hDu)

end AFree.AlbertiProof
