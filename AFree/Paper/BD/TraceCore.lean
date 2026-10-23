module

public import AFree.Defs
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# A singular measure cannot be tested against an absolutely continuous one

If `∫ φ P dν = ∫_Ω g φ` for all test functions `φ` and `ν` is a finite measure, then `P = 0` `ν`-a.e. on
every Lebesgue-null set inside `Ω`. This is Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`
on open sets, applied on the bounded open sets `U = Ω ∩ B_n` with `σ = ν + Lebesgue ∣_U`.
-/

public section

open MeasureTheory PDE

namespace AFree

namespace BD

variable {d : ℕ}

theorem integrable_mul_of_test {μ : Measure (Vec d)} {f φ : Vec d → ℝ} (hf : Integrable f μ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) : Integrable (fun x => φ x * f x) μ := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
  exact hf.bdd_mul hφ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- On a bounded open `U ⊆ Ω`: `P = 0` `ν`-a.e. on a Lebesgue-null set `N ∩ U`. -/
theorem ae_eq_zero_on_null_of_test_bounded {Ω U : Set (Vec d)} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (hUfin : volume U < ⊤) (ν : Measure (Vec d)) [IsFiniteMeasure ν] {P g : Vec d → ℝ}
    (hP : Integrable P ν) (hg : MemLp g 2 (volume.restrict Ω))
    (hid : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∫ x, φ x * P x ∂ν = ∫ x in Ω, g x * φ x)
    {N : Set (Vec d)} (hN : MeasurableSet N) (hN0 : volume N = 0) :
    ∀ᵐ x ∂ν, x ∈ N → x ∈ U → P x = 0 := by
  set lam : Measure (Vec d) := volume.restrict U with hlam
  have : IsFiniteMeasure lam := ⟨by rw [hlam, Measure.restrict_apply_univ]; exact hUfin⟩
  have hgU : Integrable g lam :=
    (hg.mono_measure (Measure.restrict_mono hUΩ le_rfl)).integrable one_le_two
  set σ : Measure (Vec d) := ν + lam with hσ
  have hνσ : ν ≪ σ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hlσ : lam ≪ σ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hF1 : Integrable (fun x => (ν.rnDeriv σ x).toReal * P x) σ :=
    (integrable_toReal_rnDeriv_mul_iff hνσ).2 hP
  have hF2 : Integrable (fun x => (lam.rnDeriv σ x).toReal * g x) σ :=
    (integrable_toReal_rnDeriv_mul_iff hlσ).2 hgU
  have hF : Integrable (fun x => (ν.rnDeriv σ x).toReal * P x -
      (lam.rnDeriv σ x).toReal * g x) σ := hF1.sub hF2
  have h0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hF.locallyIntegrable.locallyIntegrableOn U) (fun φ hφ hc hs => by
      have hT : IsTestFunctionOn Ω φ := ⟨hφ, hc, hs.trans hUΩ⟩
      have hc' := hφ.continuous
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub (integrable_mul_of_test hF1 hc' hc) (integrable_mul_of_test hF2 hc' hc),
        sub_eq_zero]
      have e1 : ∫ x, φ x * ((ν.rnDeriv σ x).toReal * P x) ∂σ = ∫ x, φ x * P x ∂ν := by
        rw [← integral_toReal_rnDeriv_mul hνσ (f := fun x => φ x * P x)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      have e2 : ∫ x, φ x * ((lam.rnDeriv σ x).toReal * g x) ∂σ = ∫ x, φ x * g x ∂lam := by
        rw [← integral_toReal_rnDeriv_mul hlσ (f := fun x => φ x * g x)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [e1, e2, hid φ hT, hlam]
      have hz : ∀ x ∈ Ω \ U, g x * φ x = 0 := by
        intro x hx
        have : φ x = 0 := by
          by_contra hne
          exact hx.2 (hs (subset_tsupport _ hne))
        simp [this]
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hUΩ hz]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm]))
  have hpos : ∀ᵐ x ∂ν, 0 < (ν.rnDeriv σ x).toReal := by
    filter_upwards [Measure.rnDeriv_pos hνσ, hνσ.ae_le (Measure.rnDeriv_lt_top ν σ)] with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2.ne
  have hlamN : lam N = 0 := by
    rw [hlam, Measure.restrict_apply hN]
    exact measure_mono_null Set.inter_subset_left hN0
  have hr2 : ∀ᵐ x ∂σ, x ∈ N → lam.rnDeriv σ x = 0 := by
    have h1 := Measure.setLIntegral_rnDeriv' hlσ hN
    rw [hlamN] at h1
    exact (ae_restrict_iff' hN).1
      ((lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _)).1 h1)
  filter_upwards [hpos, hνσ.ae_le h0, hνσ.ae_le hr2] with x h1 h2 h3 hxN hxU
  have h4 := h2 hxU
  rw [h3 hxN, ENNReal.toReal_zero, zero_mul, sub_zero] at h4
  exact (mul_eq_zero.1 h4).resolve_left h1.ne'

/-- `P = 0` `ν`-a.e. on every Lebesgue-null set inside the open set `Ω`. -/
theorem ae_eq_zero_on_null_of_test {Ω : Set (Vec d)} (hΩ : IsOpen Ω) (ν : Measure (Vec d))
    [IsFiniteMeasure ν] {P g : Vec d → ℝ} (hP : Integrable P ν)
    (hg : MemLp g 2 (volume.restrict Ω))
    (hid : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∫ x, φ x * P x ∂ν = ∫ x in Ω, g x * φ x)
    {N : Set (Vec d)} (hN : MeasurableSet N) (hN0 : volume N = 0) :
    ∀ᵐ x ∂ν, x ∈ N → x ∈ Ω → P x = 0 := by
  have key : ∀ n : ℕ, ∀ᵐ x ∂ν, x ∈ N → x ∈ Ω ∩ Metric.ball (0 : Vec d) n → P x = 0 := fun n =>
    ae_eq_zero_on_null_of_test_bounded hΩ (hΩ.inter Metric.isOpen_ball) Set.inter_subset_left
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_ball_lt_top) ν hP hg hid hN hN0
  filter_upwards [ae_all_iff.2 key] with x hx hxN hxΩ
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n hxN ⟨hxΩ, by simpa using hn⟩

end BD

end AFree
