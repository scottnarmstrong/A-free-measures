module

public import AFree.Rademacher.Chain.WideMain
public import AFree.Rademacher.Chain.PertLocal
public import AFree.Rademacher.Lusin

/-!
# The local cone-null compact sets

Compact cone-null subsets chosen locally in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE MeasureTheory Set
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- Inner regularity with a factor `2`. -/
theorem exists_isCompact_half (μ : Measure (Vec d)) [IsFiniteMeasure μ] {A : Set (Vec d)}
    (hA : MeasurableSet A) : ∃ K ⊆ A, IsCompact K ∧ μ A ≤ 2 * μ K := by
  by_cases h0 : μ A = 0
  · exact ⟨∅, empty_subset _, isCompact_empty, by simp [h0]⟩
  have hne : μ A ≠ ∞ := measure_ne_top μ A
  have hε : μ A / 2 ≠ 0 := (ENNReal.div_pos h0 (by simp)).ne'
  obtain ⟨K, hKA, hK, hlt⟩ := hA.exists_isCompact_lt_add hne hε
  refine ⟨K, hKA, hK, ?_⟩
  have hhalf : μ A / 2 + μ A / 2 = μ A := ENNReal.add_halves _
  have hne2 : μ A / 2 ≠ ∞ := ENNReal.div_ne_top hne (by simp)
  have : μ A / 2 < μ K := by
    have h' : μ A / 2 + μ A / 2 < μ K + μ A / 2 := by rwa [hhalf]
    exact (ENNReal.add_lt_add_iff_right hne2).1 h'
  calc μ A = 2 * (μ A / 2) := by rw [ENNReal.mul_div_cancel (by simp) (by simp)]
    _ ≤ 2 * μ K := by gcongr

/-- For `x̄` and `r` with the frame vector `e_k` within `ω` of
`e_k(x̄)` on `B̄(x̄, r)`, and `ω < cos β`, every measurable `F ⊆ E ∩ B̄(x̄, r)` contains a compact
`C(e_k(x̄), β)`-null `K` with `μ F ≤ 2 μ K`. -/
theorem pert_local_cone_null {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)} {i : Fin d}
    {m : ℕ} {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (hS : Setting μ V i m δ E e) {k : Fin d} (hk : (k : ℕ) < m) {xb : Vec d} {r ω β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < Real.pi / 2) (hωβ : ω < Real.cos β)
    (hec : ∀ y, ‖y - xb‖ ≤ r → vecEuclideanNorm (e y k - e xb k) ≤ ω) {F : Set (Vec d)}
    (hF : MeasurableSet F) (hFE : F ⊆ E ∩ Metric.closedBall xb r) :
    ∃ K ⊆ F, IsCompact K ∧ IsCNull (cone (e xb k) β) K ∧ μ F ≤ 2 * μ K := by
  have := hS.finite
  have hCV : ∀ᵐ x ∂μ, x ∈ F → ∀ w ∈ V x, w ∈ cone (e xb k) β → w = 0 := by
    refine Filter.Eventually.of_forall fun x hx w hw hwc => ?_
    obtain ⟨hxE, hxb⟩ := hFE hx
    have hxb' : ‖x - xb‖ ≤ r := by
      have := Metric.mem_closedBall.1 hxb
      rwa [dist_eq_norm] at this
    have h0 : vecDot (e x k) w = 0 := hS.perp x hxE k hk w hw
    have h1 : vecDot w (e xb k) = vecDot w (e xb k - e x k) := by
      rw [vecDot_sub_right, vecDot_comm w (e x k), h0]; ring
    have h2 := abs_vecDot_le_vecEuclideanNorm_mul w (e xb k - e x k)
    rw [vecEuclideanNorm_sub_comm] at h2
    have h3 := hec x hxb'
    have h4 : vecEuclideanNorm w * Real.cos β ≤ vecEuclideanNorm w * ω := by
      calc vecEuclideanNorm w * Real.cos β = Real.cos β * vecEuclideanNorm w := by ring
        _ ≤ vecDot w (e xb k) := hwc
        _ ≤ |vecDot w (e xb k - e x k)| := by rw [h1]; exact le_abs_self _
        _ ≤ vecEuclideanNorm w * vecEuclideanNorm (e x k - e xb k) := h2
        _ ≤ vecEuclideanNorm w * ω := mul_le_mul_of_nonneg_left h3 (vecEuclideanNorm_nonneg _)
    have h5 : vecEuclideanNorm w ≤ 0 := by
      by_contra hpos
      replace hpos := lt_of_not_ge hpos
      linarith [(mul_le_mul_iff_of_pos_left hpos).1 h4]
    exact vecEuclideanNorm_eq_zero_iff.1 (le_antisymm h5 (vecEuclideanNorm_nonneg _))
  obtain ⟨F', hF'F, hF'm, hF'null, hF'μ⟩ := prop_wideconenull hS.test hF
    (IsFrame.norm_eq_one hS.frame xb k) hβ0 hβ2 hCV
  obtain ⟨K, hKF', hK, hμK⟩ := exists_isCompact_half μ hF'm
  exact ⟨K, hKF'.trans hF'F, hK, hF'null.mono hKF', by rwa [hF'μ] at hμK⟩

end AFree.Rademacher
