module

public import AFree.Paper.TensorPow.Curl
public import AFree.Paper.TensorPow.PermDeriv

/-!
# `Dʳu` is `𝒜`-free

The `r`-th derivative of a function, when it is a measure, is free for the curl-type operator (proof of
[DPR, Theorem 1.6]).
-/

public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- If `Dʳ u` is the `r`-th derivative of `u` on the open set `Ω` as a measure,
then `Dʳ u` is `𝒜`-free for the curl-type operator `𝒜 = Σ_m A_m ∂_m` (with `A₀ = 0`). -/
theorem isFirstOrderFree_curlr_of_isDerivMeasureOn {d ℓ r : ℕ} {Ω : Set (Vec d)}
    {u : Vec d → Vec ℓ} {Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)}
    (h : IsDerivMeasureOn Ω u r Dr) : IsFirstOrderFree Ω (curlrCoeff ℓ d r) 0 Dr := by
  intro φ hφ
  have hψ : ∀ m, IsTestFunctionOn Ω (euclideanCoordDeriv m φ) := fun m =>
    ⟨contDiff_euclideanCoordDeriv hφ.1 m, hasCompactSupport_euclideanCoordDeriv hφ.2.1 m,
      (tsupport_euclideanCoordDeriv_subset_tsupport m φ).trans hφ.2.2⟩
  have hinv : ∀ ψ, IsTestFunctionOn Ω ψ → ∀ (k : Fin ℓ) (β : Fin r → Fin d),
      (∫ᵛ x, ψ x ∂•Dr) (k, β) = (-1) ^ r * ∫ x in Ω, u x k * iteratedCoordDeriv β ψ x := by
    intro ψ hψ' k β
    rw [h.2.2 ψ hψ' k β, ← mul_assoc, ← mul_pow]
    simp
  rw [Matrix.zero_mulVec]
  funext ⟨k, α, hh, i, j⟩
  rw [curlrCoeff_sum_mulVec, hinv _ (hψ j), hinv _ (hψ i),
    iteratedCoordDeriv_update_coordDeriv hφ.1 α hh j i]
  simp

end AFree
