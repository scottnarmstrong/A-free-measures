module

public import AFree.Proofs.FirstOrderMainProof
public import AFree.Measure.Decomp.Singular
public import AFree.Paper.TensorPow.Cone
public import AFree.Paper.TensorPow.Free

/-!
# Theorem 1.6: rank-one structure of higher derivatives

[DPR, Theorem 1.6]. The first-order main theorem `polar_mem_waveConeFirstOrder` is the only external
input of this module.
-/

public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {d ℓ r : ℕ}

/-- The polar of `Dʳu` lies in the wave cone of the curl-type operator
`|Dʳu|ˢ`-a.e. -/
theorem ae_polar_mem_waveConeFirstOrder_curlr {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec ℓ} {Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)}
    (hDr : IsDerivMeasureOn Ω u r Dr) :
    ∀ᵐ x ∂(euclideanVariation Dr).singularPart volume,
      polar Dr x ∈ waveConeFirstOrder (curlrCoeff ℓ d r) :=
  FirstOrderMainProof.result Ω hΩ (curlrCoeff ℓ d r) 0 Dr hDr.2.1
    (isFirstOrderFree_curlr_of_isDerivMeasureOn hDr)

/-- For `|(Dʳu)ˢ|`-a.e. `x`, the polar of `(Dʳu)ˢ` lies in the
wave cone and has norm one. -/
theorem ae_polar_lebesgueSingularPart_mem_waveCone_curlr {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec ℓ} {Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)}
    (hDr : IsDerivMeasureOn Ω u r Dr) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Dr),
      polar (lebesgueSingularPart Dr) x ∈ waveConeFirstOrder (curlrCoeff ℓ d r) ∧
        piEuclideanNorm (polar (lebesgueSingularPart Dr) x) = 1 ∧
        polar (lebesgueSingularPart Dr) x ≠ 0 :=
  ae_polar_lebesgueSingularPart_mem Dr _ (ae_polar_mem_waveConeFirstOrder_curlr hΩ hDr)

/-- A nonzero element of the wave cone of the curl-type operator is
`a ⊗ b^{⊗ r}` with `a ≠ 0`, `b ≠ 0`. -/
theorem exists_ne_zero_tensorPow_of_mem_waveCone_curlr {P : Fin ℓ × (Fin r → Fin d) → ℝ}
    (hP : P ∈ waveConeFirstOrder (curlrCoeff ℓ d r)) (hne : P ≠ 0) :
    ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧ P = fun p => a p.1 * ∏ m, b (p.2 m) := by
  obtain ⟨ξ, hξ, hξP⟩ := hP
  have hsq : ∑ j, ξ j * ξ j = 1 := by
    have := vecEuclideanNorm_sq ξ
    rw [hξ] at this
    simpa [vecNormSq, vecDot] using this.symm
  obtain ⟨a, ha⟩ := curlr_cone hsq hξP
  have hP' : P = fun p => a p.1 * ∏ m, ξ (p.2 m) := funext fun ⟨k, α⟩ => ha k α
  refine ⟨a, ?_, ξ, ?_, hP'⟩
  · rintro rfl
    exact hne (by rw [hP']; funext p; simp)
  · rintro rfl
    have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    rw [this] at hξ
    exact zero_ne_one hξ

/-- [DPR, Theorem 1.6]: for `|(Dʳu)ˢ|`-a.e. `x` the polar of `(Dʳu)ˢ` is
`p ↦ a_{p₁} ∏_m b_{p₂(m)}` with `a ≠ 0`, `b ≠ 0`. -/
theorem ae_polar_lebesgueSingularPart_tensorPow {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec ℓ} {Dr : VectorMeasure (Vec d) (Fin ℓ × (Fin r → Fin d) → ℝ)}
    (hDr : IsDerivMeasureOn Ω u r Dr) :
    ∀ᵐ x ∂euclideanVariation (lebesgueSingularPart Dr),
      ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧
        polar (lebesgueSingularPart Dr) x = fun p => a p.1 * ∏ m, b (p.2 m) := by
  filter_upwards [ae_polar_lebesgueSingularPart_mem_waveCone_curlr hΩ hDr] with x hx
  exact exists_ne_zero_tensorPow_of_mem_waveCone_curlr hx.1 hx.2.2

end AFree
