module

public import AFree.Paper.Curl
public import AFree.Measure.PolarFacts

/-!
# Alberti's rank-one theorem from Theorem 1.1 for the curl

Proof of [DPR, Theorem 1.5]. Theorem 1.1 for the curl operator enters only through the hypothesis
`hmain`; `albertiInstance_of_main` supplies it from the main theorem.
-/

public section

open MeasureTheory

namespace AFree

open PDE

/-- The instance of Theorem 1.1 for the curl operator applied to `Du`. -/
theorem albertiInstance_of_main {d ℓ : ℕ}
    (hmainThm : ∀ (Ω : Set (Vec d)), IsOpen Ω →
      ∀ (A : Fin d → Matrix (Fin ℓ × Fin d × Fin d) (Fin ℓ × Fin d) ℝ)
        (A₀ : Matrix (Fin ℓ × Fin d × Fin d) (Fin ℓ × Fin d) ℝ)
        (μ : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)), euclideanVariation μ Ωᶜ = 0 →
        IsFirstOrderFree Ω A A₀ μ →
        ∀ᵐ x ∂(euclideanVariation μ).singularPart volume, polar μ x ∈ waveConeFirstOrder A)
    {Ω : Set (Vec d)} (hΩ : IsOpen Ω) (u : Vec d → Vec ℓ)
    (Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)) (hDu : IsBVGradientOn Ω u Du) :
    ∀ᵐ x ∂(euclideanVariation Du).singularPart volume,
      polar Du x ∈ waveConeFirstOrder (curlCoeff ℓ d) :=
  hmainThm Ω hΩ (curlCoeff ℓ d) 0 Du hDu.2.1 (isFirstOrderFree_curl_of_isBVGradientOn hDu)

/-- [DPR, Theorem 1.5]: Alberti's theorem, from the instance of Theorem 1.1 for the curl operator,
which is taken as the hypothesis `hmain`. -/
theorem polar_lebesgueSingularPart_eq_tensor_of_main {d ℓ : ℕ}
    (Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ))
    (hmain : ∀ᵐ x ∂(euclideanVariation Du).singularPart volume,
      polar Du x ∈ waveConeFirstOrder (curlCoeff ℓ d)) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Du),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Du) x = fun p => a p.1 * b p.2 := by
  rw [← euclideanVariation_lebesgueSingularPart] at hmain
  filter_upwards [hmain, polar_lebesgueSingularPart_ae Du,
    piEuclideanNorm_polar_eq_one (lebesgueSingularPart Du)] with x h1 h2 h3
  rw [← h2] at h1
  refine exists_ne_zero_rankOne_of_mem_waveCone_curl h1 ?_
  intro h0
  rw [h0] at h3
  simp [piEuclideanNorm] at h3

end AFree
