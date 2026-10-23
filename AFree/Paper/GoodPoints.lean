module

public import AFree.Defs
public import AFree.Measure.Doubling
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Good blow-up points

`σˢ`-a.e. point lies in `Ω`, sees `σˢ` on every ball, and satisfies the differentiation properties (i) of
[DPR, proof of Theorem 1.1] (the `σˢ`-averages of `|P - P(x)|` tend to `0`, the `σᵃ`-mass of `|P|` is
negligible against `σˢ`) and, in place of the tangent-measure step (ii), `σˢ` is doubling along a sequence of scales. Cubes `Q_r(x)` are `Metric.closedBall x r` on
`Vec d` (sup metric).
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AFree

open PDE

section aux

variable {ι : Type*} [Fintype ι]

lemma piEuclideanNorm_le (v : ι → ℝ) :
    piEuclideanNorm v ≤ Real.sqrt (Fintype.card ι) * ‖v‖ := by
  unfold piEuclideanNorm
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, v i * v i ≤ ∑ _i : ι, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_le_pi_norm v i
        have h2 : |v i| ≤ ‖v‖ := by simpa using this
        calc v i * v i = |v i| ^ 2 := by rw [sq_abs]; ring
          _ ≤ ‖v‖ ^ 2 := by gcongr
    _ = _ := by simp

lemma piEuclideanNorm_nonneg' (v : ι → ℝ) : 0 ≤ piEuclideanNorm v := Real.sqrt_nonneg _

lemma continuous_piEuclideanNorm : Continuous (piEuclideanNorm (ι := ι)) := by
  unfold piEuclideanNorm
  fun_prop

end aux

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The `σˢ`-averages of `|P - P(x)|` over balls tend to `0` at `σˢ`-a.e. point. -/
lemma ae_tendsto_good_G2 (s : Measure (Vec d)) [IsFiniteMeasure s] {P : Vec d → ι → ℝ}
    (hPi : Integrable P s) :
    ∀ᵐ x ∂s, Tendsto (fun r => (∫ y in Metric.closedBall x r, piEuclideanNorm (P y - P x) ∂s) /
        (s (Metric.closedBall x r)).toReal) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily s).ae_tendsto_average_norm_sub
    hPi.locallyIntegrable] with x hx
  have hx' := hx.comp (Besicovitch.tendsto_filterAt s x)
  have hc : Continuous fun p : ι → ℝ => piEuclideanNorm p := continuous_piEuclideanNorm
  refine squeeze_zero (fun r => ?_) (fun r => ?_)
    (by simpa using hx'.const_mul (Real.sqrt (Fintype.card ι)))
  · exact div_nonneg (integral_nonneg fun y => Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  · simp only [setAverage_eq, smul_eq_mul, Measure.real]
    rw [div_eq_inv_mul, ← mul_assoc, mul_comm (Real.sqrt _), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ENNReal.toReal_nonneg)
    rw [← integral_const_mul]
    have hi : Integrable (fun y => ‖P y - P x‖) (s.restrict (Metric.closedBall x r)) :=
      ((hPi.sub (integrable_const _)).norm).restrict
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => Real.sqrt_nonneg _)
      (hi.const_mul _) (Eventually.of_forall fun y => piEuclideanNorm_le _)

/-- The `σᵃ`-mass of `|P|` on balls is negligible against `σˢ` at `σˢ`-a.e. point. -/
lemma ae_tendsto_good_G3 (σ : Measure (Vec d)) [IsFiniteMeasure σ] {P : Vec d → ι → ℝ}
    (hPm : Measurable P) (hPi : Integrable P σ) :
    ∀ᵐ x ∂σ.singularPart volume, Tendsto (fun r => (∫ y in Metric.closedBall x r,
        piEuclideanNorm (P y) ∂volume.withDensity (σ.rnDeriv volume)) /
        (σ.singularPart volume (Metric.closedBall x r)).toReal) (𝓝[>] 0) (𝓝 0) := by
  set s := σ.singularPart volume with hs
  set a := volume.withDensity (σ.rnDeriv volume) with ha
  have hnm : Measurable fun y => piEuclideanNorm (P y) :=
    continuous_piEuclideanNorm.measurable.comp hPm
  have hale : a ≤ σ := Measure.withDensity_rnDeriv_le σ volume
  have hint : Integrable (fun y => piEuclideanNorm (P y)) σ := by
    refine Integrable.mono' (hPi.norm.const_mul (Real.sqrt (Fintype.card ι)))
      hnm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (piEuclideanNorm_nonneg' _)]
    exact piEuclideanNorm_le _
  have hinta : Integrable (fun y => piEuclideanNorm (P y)) a := hint.mono_measure hale
  set ρ : Measure (Vec d) := a.withDensity fun y => ENNReal.ofReal (piEuclideanNorm (P y))
    with hρ
  have hρfin : IsFiniteMeasure ρ := by
    refine ⟨?_⟩
    rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hinta.lintegral_lt_top
  have hac : ρ ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous _ _)
  have hperp : ρ ⟂ₘ s :=
    (Measure.mutuallySingular_singularPart σ volume).symm.mono_ac hac
      Measure.AbsolutelyContinuous.rfl
  have h1 := Besicovitch.ae_tendsto_rnDeriv ρ s
  have h2 : ∀ᵐ x ∂s, ρ.rnDeriv s x = 0 :=
    Measure.rnDeriv_eq_zero_of_mutuallySingular hperp Measure.AbsolutelyContinuous.rfl
  filter_upwards [h1, h2] with x hx hx0
  rw [hx0] at hx
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx
  simp only [ENNReal.toReal_zero] at this
  refine this.congr fun r => ?_
  simp only [Function.comp_apply, ENNReal.toReal_div]
  congr 1
  rw [hρ, withDensity_apply _ Metric.isClosed_closedBall.measurableSet,
    integral_eq_lintegral_of_nonneg_ae
      (f := fun y => piEuclideanNorm (P y)) (Eventually.of_forall fun y => piEuclideanNorm_nonneg' _)
      hnm.aestronglyMeasurable.restrict]

/-- σˢ-a.e. point is a good blow-up point (it lies in `Ω` and has the properties listed in the module doc). -/
theorem ae_goodPoint {d : ℕ} {ι : Type*} [Fintype ι] (σ : Measure (Vec d)) [IsFiniteMeasure σ]
    {P : Vec d → ι → ℝ} (hPm : Measurable P) (hPi : Integrable P σ)
    {Ω : Set (Vec d)} (hΩ : σ Ωᶜ = 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᵐ x ∂σ.singularPart volume, x ∈ Ω ∧
      (∀ r, 0 < r → 0 < σ.singularPart volume (Metric.closedBall x r)) ∧
      Tendsto (fun r => (∫ y in Metric.closedBall x r, piEuclideanNorm (P y - P x)
          ∂σ.singularPart volume) / (σ.singularPart volume (Metric.closedBall x r)).toReal)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => (∫ y in Metric.closedBall x r, piEuclideanNorm (P y)
          ∂volume.withDensity (σ.rnDeriv volume)) /
            (σ.singularPart volume (Metric.closedBall x r)).toReal) (𝓝[>] 0) (𝓝 0) ∧
      ∀ r₀, 0 < r₀ → ∃ r ∈ Set.Ioo 0 r₀,
        ENNReal.ofReal (t ^ (d + 1)) * σ.singularPart volume (Metric.closedBall x r) ≤
          σ.singularPart volume (Metric.closedBall x (t * r)) := by
  have hle : σ.singularPart volume ≤ σ := Measure.singularPart_le σ volume
  have hPs : Integrable P (σ.singularPart volume) := hPi.mono_measure hle
  have hΩs : ∀ᵐ x ∂σ.singularPart volume, x ∈ Ω := by
    rw [ae_iff]
    exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hle Ωᶜ).trans hΩ.le)
  filter_upwards [hΩs, ae_doubling_scales (σ.singularPart volume)
    (Measure.mutuallySingular_singularPart σ volume) ht0 ht1,
    ae_tendsto_good_G2 (σ.singularPart volume) hPs, ae_tendsto_good_G3 σ hPm hPi]
    with x hxΩ hd2 hG2 hG3
  exact ⟨hxΩ, hd2.1, hG2, hG3, hd2.2.2⟩

/-- If `σˢ(E) > 0`, some point of `E` is a good blow-up point. -/
theorem exists_goodPoint {d : ℕ} {ι : Type*} [Fintype ι] (σ : Measure (Vec d)) [IsFiniteMeasure σ]
    {P : Vec d → ι → ℝ} (hPm : Measurable P) (hPi : Integrable P σ)
    {Ω : Set (Vec d)} (hΩ : σ Ωᶜ = 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {E : Set (Vec d)} (hpos : 0 < σ.singularPart volume E) :
    ∃ x₀ ∈ E, x₀ ∈ Ω ∧
      (∀ r, 0 < r → 0 < σ.singularPart volume (Metric.closedBall x₀ r)) ∧
      Tendsto (fun r => (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y - P x₀)
          ∂σ.singularPart volume) / (σ.singularPart volume (Metric.closedBall x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y)
          ∂volume.withDensity (σ.rnDeriv volume)) /
            (σ.singularPart volume (Metric.closedBall x₀ r)).toReal) (𝓝[>] 0) (𝓝 0) ∧
      ∀ r₀, 0 < r₀ → ∃ r ∈ Set.Ioo 0 r₀,
        ENNReal.ofReal (t ^ (d + 1)) * σ.singularPart volume (Metric.closedBall x₀ r) ≤
          σ.singularPart volume (Metric.closedBall x₀ (t * r)) := by
  obtain ⟨x, hxE, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (ae_restrict_of_ae (ae_goodPoint σ hPm hPi hΩ ht0 ht1))
  exact ⟨x, hxE, hx⟩

end AFree
