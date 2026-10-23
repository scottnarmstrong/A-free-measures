module

public import AFree.Rademacher.Chain.PertLocal

/-!
# Constants, cone angle, local radii and disjoint sums of the single-stage perturbation

Helpers for the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- The cone angle `β = arccos c` for `0 < c ≤ 1/8`: `β ∈ (0, π/2)`, `cos β = c` and
`2 / tan β ≤ 3 c`. -/
theorem cone_angle {c : ℝ} (hc : 0 < c) (hc8 : c ≤ 1 / 8) :
    0 < Real.arccos c ∧ Real.arccos c < Real.pi / 2 ∧ Real.cos (Real.arccos c) = c ∧
      2 / Real.tan (Real.arccos c) ≤ 3 * c := by
  have hβ0 : 0 < Real.arccos c := Real.arccos_pos.2 (by linarith)
  have hβ2 : Real.arccos c < Real.pi / 2 := Real.arccos_lt_pi_div_two.2 hc
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos (by linarith) (by linarith)
  refine ⟨hβ0, hβ2, hcos, ?_⟩
  have hsin : Real.sin (Real.arccos c) = Real.sqrt (1 - c ^ 2) := Real.sin_arccos c
  have hs : 2 / 3 ≤ Real.sqrt (1 - c ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [Real.tan_eq_sin_div_cos, hcos, hsin, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- Continuity radius: the frame and the gradient of a `C¹` function stay `ω`-, `θ`-close to
their values at `x̄` on a small ball. -/
theorem exists_local_radius {e : Vec d → Fin d → Vec d} (he : IsFrame e) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (xb : Vec d) {ω θ : ℝ} (hω : 0 < ω) (hθ : 0 < θ) :
    ∃ η : ℝ, 0 < η ∧ ∀ y, ‖y - xb‖ < η → (∀ j, vecEuclideanNorm (e y j - e xb j) ≤ ω) ∧
      vecEuclideanNorm (euclGrad f y - euclGrad f xb) ≤ θ := by
  have hec : ∀ j, ∀ᶠ y in 𝓝 xb, vecEuclideanNorm (e y j - e xb j) < ω := by
    intro j
    have hc : Continuous fun y => vecEuclideanNorm (e y j - e xb j) :=
      continuous_vecEuclideanNorm.comp (((continuous_apply j).comp he.1).sub continuous_const)
    have h0 : vecEuclideanNorm (e xb j - e xb j) < ω := by
      rw [sub_self, vecEuclideanNorm_eq_zero_iff.2 rfl]; exact hω
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  have hgc : Continuous (euclGrad f) := by
    refine continuous_pi fun i => ?_
    exact ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hgrad : ∀ᶠ y in 𝓝 xb, vecEuclideanNorm (euclGrad f y - euclGrad f xb) < θ := by
    have hc : Continuous fun y => vecEuclideanNorm (euclGrad f y - euclGrad f xb) :=
      continuous_vecEuclideanNorm.comp (hgc.sub continuous_const)
    have h0 : vecEuclideanNorm (euclGrad f xb - euclGrad f xb) < θ := by
      rw [sub_self, vecEuclideanNorm_eq_zero_iff.2 rfl]; exact hθ
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  have hall := (Filter.eventually_all.2 hec).and hgrad
  obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.1 hall
  refine ⟨η, hη, fun y hy => ?_⟩
  have := hηP (by rwa [dist_eq_norm])
  exact ⟨fun j => (this.1 j).le, this.2.le⟩

/-- Sums of functions with pairwise disjoint supports. -/
theorem sum_disjoint_support (T : Finset (Vec d)) (B : Vec d → Set (Vec d))
    (φ : Vec d → Vec d → ℝ) (hφ : ∀ p ∈ T, ContDiff ℝ (⊤ : ℕ∞) (φ p))
    (hsupp : ∀ p ∈ T, tsupport (φ p) ⊆ B p)
    (hdis : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → Disjoint (B p) (B q)) :
    (∀ p ∈ T, ∀ y ∈ B p, (∑ q ∈ T, φ q y) = φ p y ∧
      fderiv ℝ (fun z => ∑ q ∈ T, φ q z) y = fderiv ℝ (φ p) y) ∧
    (∀ y, (∀ p ∈ T, y ∉ B p) → (∑ q ∈ T, φ q y) = 0 ∧
      fderiv ℝ (fun z => ∑ q ∈ T, φ q z) y = 0) := by
  have hdiff : ∀ y, ∀ q ∈ T, DifferentiableAt ℝ (φ q) y :=
    fun y q hq => (hφ q hq).differentiable (by simp) y
  have hnot : ∀ q ∈ T, ∀ y, y ∉ B q → φ q y = 0 ∧ fderiv ℝ (φ q) y = 0 := by
    intro q hq y hy
    have hy' : y ∉ tsupport (φ q) := fun h => hy (hsupp q hq h)
    exact ⟨image_eq_zero_of_notMem_tsupport hy', fderiv_of_notMem_tsupport ℝ hy'⟩
  refine ⟨fun p hp y hy => ?_, fun y hy => ?_⟩
  · have hne : ∀ q ∈ T, q ≠ p → y ∉ B q := fun q hq hqp hyq =>
      (hdis q hq p hp hqp).le_bot ⟨hyq, hy⟩
    refine ⟨?_, ?_⟩
    · exact Finset.sum_eq_single p (fun q hq hqp => (hnot q hq y (hne q hq hqp)).1)
        (fun h => absurd hp h)
    · rw [fderiv_fun_sum (fun q hq => hdiff y q hq)]
      refine Finset.sum_eq_single p (fun q hq hqp => (hnot q hq y (hne q hq hqp)).2)
        (fun h => absurd hp h)
  · refine ⟨Finset.sum_eq_zero fun q hq => (hnot q hq y (hy q hq)).1, ?_⟩
    rw [fderiv_fun_sum (fun q hq => hdiff y q hq)]
    exact Finset.sum_eq_zero fun q hq => (hnot q hq y (hy q hq)).2

end AFree.Rademacher
