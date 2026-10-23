module

public import AFree.Defs

/-!
# Curl-free gradients and the wave cone of the curl

Proof of [DPR, Theorem 1.5]: the distributional gradient `Du` of a BV map is curl-free, and the wave
cone of the curl operator consists of the rank-one matrices `a ⊗ ξ`.

Encoding: `ℝ^{ℓ×d}` is `Fin ℓ × Fin d → ℝ` with entries `(k, j) = ∂ⱼ uₖ`; the curl target is
`Fin ℓ × Fin d × Fin d → ℝ`.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- `(curl μ)_{k,i,j} = ∂_j μ_{k i} − ∂_i μ_{k j}` as a first-order
operator. -/
def curlCoeff (ℓ d : ℕ) : Fin d → Matrix (Fin ℓ × Fin d × Fin d) (Fin ℓ × Fin d) ℝ :=
  fun m r c => if c.1 = r.1 then
    ((if c.2 = r.2.1 ∧ m = r.2.2 then 1 else 0) - (if c.2 = r.2.2 ∧ m = r.2.1 then 1 else 0))
    else 0

/-- The curl symbol: `(Σ_m ξ_m A_m) P = P_{k i} ξ_j − P_{k j} ξ_i`. -/
theorem curlCoeff_symbol_mulVec {ℓ d : ℕ} (ξ : Vec d) (P : Fin ℓ × Fin d → ℝ) :
    (∑ m, ξ m • curlCoeff ℓ d m) *ᵥ P =
      fun r => P (r.1, r.2.1) * ξ r.2.2 - P (r.1, r.2.2) * ξ r.2.1 := by
  funext r
  obtain ⟨k, i, j⟩ := r
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, curlCoeff,
    smul_eq_mul, Fintype.sum_prod_type]
  simp [mul_sub, sub_mul, Finset.sum_sub_distrib, ite_and, mul_comm]

/-- The distributional gradient of a BV map is curl-free. -/
theorem isFirstOrderFree_curl_of_isBVGradientOn {d ℓ : ℕ} {Ω : Set (Vec d)} {u : Vec d → Vec ℓ}
    {Du : VectorMeasure (Vec d) (Fin ℓ × Fin d → ℝ)}
    (h : IsBVGradientOn Ω u Du) : IsFirstOrderFree Ω (curlCoeff ℓ d) 0 Du := by
  intro φ hφ
  have hψ : ∀ m, IsTestFunctionOn Ω (euclideanCoordDeriv m φ) := fun m =>
    ⟨contDiff_euclideanCoordDeriv hφ.1 m, hasCompactSupport_euclideanCoordDeriv hφ.2.1 m,
      (tsupport_euclideanCoordDeriv_subset_tsupport m φ).trans hφ.2.2⟩
  have hw : ∀ m k i, (∫ᵛ x, euclideanCoordDeriv m φ x ∂•Du) (k, i) =
      -∫ x in Ω, u x k * euclideanCoordDeriv i (euclideanCoordDeriv m φ) x := fun m k i => by
    rw [h.2.2 _ (hψ m) k i, neg_neg]
  have hsym : ∀ i j, euclideanCoordDeriv i (euclideanCoordDeriv j φ) =
      euclideanCoordDeriv j (euclideanCoordDeriv i φ) := fun i j =>
    euclideanCoordSecondDeriv_comm_fun hφ.1 j i
  rw [Matrix.zero_mulVec]
  funext r
  obtain ⟨k, i, j⟩ := r
  have key : (∑ m, curlCoeff ℓ d m *ᵥ (∫ᵛ x, euclideanCoordDeriv m φ x ∂•Du)) (k, i, j) =
      (∫ᵛ x, euclideanCoordDeriv j φ x ∂•Du) (k, i) -
        (∫ᵛ x, euclideanCoordDeriv i φ x ∂•Du) (k, j) := by
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, curlCoeff, Fintype.sum_prod_type]
    simp [sub_mul, Finset.sum_sub_distrib, ite_and]
  rw [key, hw, hw, hsym i j]
  simp

/-- The wave cone of the curl is the set of rank-one matrices `a ⊗ ξ`
with `|ξ| = 1`. -/
theorem mem_waveCone_curl_iff {ℓ d : ℕ} {P : Fin ℓ × Fin d → ℝ} :
    P ∈ waveConeFirstOrder (curlCoeff ℓ d) ↔
      ∃ a : Vec ℓ, ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧ P = fun p => a p.1 * ξ p.2 := by
  constructor
  · rintro ⟨ξ, hξ, hP⟩
    rw [curlCoeff_symbol_mulVec] at hP
    have hrel : ∀ k i j, P (k, i) * ξ j = P (k, j) * ξ i := fun k i j =>
      sub_eq_zero.1 (congrFun hP (k, i, j))
    have hsq : ∑ j, ξ j * ξ j = 1 := by
      have := vecEuclideanNorm_sq ξ
      rw [hξ] at this
      simpa [vecNormSq, vecDot] using this.symm
    refine ⟨fun k => ∑ j, P (k, j) * ξ j, ξ, hξ, ?_⟩
    funext ⟨k, i⟩
    simp only
    calc P (k, i) = P (k, i) * ∑ j, ξ j * ξ j := by rw [hsq, mul_one]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, hrel k i j]; ring
  · rintro ⟨a, ξ, hξ, rfl⟩
    refine ⟨ξ, hξ, ?_⟩
    rw [curlCoeff_symbol_mulVec]
    funext r
    simp only [Pi.zero_apply]
    ring

/-- A nonzero element of the wave cone of the curl factors as `a ⊗ b`
with `a ≠ 0` and `b ≠ 0`. -/
theorem exists_ne_zero_rankOne_of_mem_waveCone_curl {ℓ d : ℕ} {P : Fin ℓ × Fin d → ℝ}
    (hP : P ∈ waveConeFirstOrder (curlCoeff ℓ d)) (hne : P ≠ 0) :
    ∃ a : Vec ℓ, a ≠ 0 ∧ ∃ b : Vec d, b ≠ 0 ∧ P = fun p => a p.1 * b p.2 := by
  obtain ⟨a, ξ, hξ, rfl⟩ := mem_waveCone_curl_iff.1 hP
  refine ⟨a, ?_, ξ, ?_, rfl⟩
  · rintro rfl
    exact hne (by funext p; simp)
  · rintro rfl
    have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    rw [this] at hξ
    exact zero_ne_one hξ

end AFree
