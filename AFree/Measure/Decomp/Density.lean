module

public import AFree.Measure.PolarFacts

/-!
# Vector measures with density

For a finite measure `σ` and
`P` with `σ`-integrable coordinates, `T = σ.withDensityᵥ P` is a vector measure with
`T(E) = ∫_E P dσ`. Here `σ` lives on an arbitrary measurable space.
-/

public section

open MeasureTheory Filter

namespace AFree

open PDE

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

/-- A function with integrable coordinates is integrable. -/
theorem integrable_of_coord_integrable {σ : Measure X} {P : X → ι → ℝ}
    (hP : ∀ i, Integrable (fun x => P x i) σ) : Integrable P σ :=
  integrable_pi_iff.2 hP

/-- The Euclidean norm of an integrable `ι → ℝ`-valued function is integrable. -/
theorem integrable_piEuclideanNorm_of_coord {σ : Measure X} {P : X → ι → ℝ}
    (hP : ∀ i, Integrable (fun x => P x i) σ) :
    Integrable (fun x => piEuclideanNorm (P x)) σ := by
  refine Integrable.mono' (g := fun x => ∑ i, |P x i|)
    (integrable_finsetSum _ fun i _ => (hP i).abs)
    (continuous_piEuclideanNorm.comp_aestronglyMeasurable
      (integrable_of_coord_integrable hP).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (piEuclideanNorm_nonneg _)]
  exact piEuclideanNorm_le_sum_abs _

/-- The coordinates of `σ.withDensityᵥ P` on Borel sets. -/
theorem withDensityᵥ_apply_coord {σ : Measure X} {P : X → ι → ℝ}
    (hP : ∀ i, Integrable (fun x => P x i) σ) {E : Set X} (hE : MeasurableSet E) (i : ι) :
    σ.withDensityᵥ P E i = ∫ x in E, P x i ∂σ := by
  rw [withDensityᵥ_apply (integrable_of_coord_integrable hP) hE]
  exact eval_integral (fun j => (hP j).restrict) i

variable {σ : Measure X} {P : X → ι → ℝ}

/-- `|T| ≤ (|P| σ)` as measures, `T = σ.withDensityᵥ P`:
`|T|(E) ≤ ∫_E |P| dσ` for every Borel `E`. -/
theorem euclideanVariation_withDensityᵥ_le (hP : ∀ i, Integrable (fun x => P x i) σ) :
    euclideanVariation (σ.withDensityᵥ P) ≤
      σ.withDensity fun x => ENNReal.ofReal (piEuclideanNorm (P x)) := by
  have hPn := integrable_piEuclideanNorm_of_coord hP
  refine euclideanVariation_le_of_forall _ fun E hE => ?_
  set a := σ.withDensityᵥ P E with ha
  have hai : ∀ i, a i = ∫ x in E, P x i ∂σ := fun i => withDensityᵥ_apply_coord hP hE i
  have h1 : piEuclideanNorm a * piEuclideanNorm a = ∫ x in E, ∑ i, a i * P x i ∂σ := by
    rw [integral_finsetSum _ fun i _ => ((hP i).const_mul (a i)).restrict, ← sq,
      ← sum_mul_self_eq_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, ← hai i]
  have h2 : ∫ x in E, ∑ i, a i * P x i ∂σ ≤ ∫ x in E, piEuclideanNorm a * piEuclideanNorm (P x) ∂σ :=
    integral_mono (integrable_finsetSum _ fun i _ => ((hP i).const_mul (a i)).restrict)
      (hPn.const_mul _).restrict fun x => sum_mul_le_piEuclideanNorm_mul a (P x)
  rw [integral_const_mul] at h2
  have hnn : 0 ≤ ∫ x in E, piEuclideanNorm (P x) ∂σ :=
    integral_nonneg fun x => piEuclideanNorm_nonneg _
  have h3 : piEuclideanNorm a ≤ ∫ x in E, piEuclideanNorm (P x) ∂σ := by
    by_cases h0 : piEuclideanNorm a = 0
    · rw [h0]; exact hnn
    · have hpos : 0 < piEuclideanNorm a := lt_of_le_of_ne (piEuclideanNorm_nonneg _) (Ne.symm h0)
      exact le_of_mul_le_mul_left (h1 ▸ h2) hpos
  rw [withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal hPn.integrableOn
      (Eventually.of_forall fun x => piEuclideanNorm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h3

/-- `|T| ≪ σ`. -/
theorem euclideanVariation_withDensityᵥ_absolutelyContinuous
    (hP : ∀ i, Integrable (fun x => P x i) σ) :
    euclideanVariation (σ.withDensityᵥ P) ≪ σ :=
  (Measure.absolutelyContinuous_of_le (euclideanVariation_withDensityᵥ_le hP)).trans
    (withDensity_absolutelyContinuous _ _)

/-- `|T|(E) = 0` whenever `σ E = 0`. -/
theorem euclideanVariation_withDensityᵥ_eq_zero (hP : ∀ i, Integrable (fun x => P x i) σ)
    {E : Set X} (hE : σ E = 0) : euclideanVariation (σ.withDensityᵥ P) E = 0 :=
  euclideanVariation_withDensityᵥ_absolutelyContinuous hP hE

/-- `P = h Q` `σ`-a.e., with `h = (d|T|/dσ)_ℝ` and `Q = polar T`. -/
theorem withDensityᵥ_ae_eq_rnDeriv_smul_polar [IsFiniteMeasure σ]
    (hP : ∀ i, Integrable (fun x => P x i) σ) :
    P =ᵐ[σ] fun x =>
      ((euclideanVariation (σ.withDensityᵥ P)).rnDeriv σ x).toReal •
        polar (σ.withDensityᵥ P) x := by
  have hac := euclideanVariation_withDensityᵥ_absolutelyContinuous hP
  have key : ∀ i, (fun x => P x i) =ᵐ[σ] fun x =>
      ((euclideanVariation (σ.withDensityᵥ P)).rnDeriv σ x).toReal *
        polar (σ.withDensityᵥ P) x i := by
    intro i
    have hint : Integrable (fun x =>
        ((euclideanVariation (σ.withDensityᵥ P)).rnDeriv σ x).toReal *
          polar (σ.withDensityᵥ P) x i) σ :=
      (integrable_toReal_rnDeriv_mul_iff hac).2 (integrable_polar_apply _ i)
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => (hP i).integrableOn) (fun s _ _ => hint.integrableOn) fun s hs _ => ?_
    rw [← withDensityᵥ_apply_coord hP hs, ← coordMeasure_apply,
      coordMeasure_eq_setIntegral _ i hs]
    simp_rw [← smul_eq_mul]
    exact (setIntegral_rnDeriv_smul hac hs).symm
  filter_upwards [ae_all_iff.2 key] with x hx
  funext i
  exact hx i

/-- For bounded Borel `g`, `∫ᵛ g dT = ∫ g P dσ`. -/
theorem integral_withDensityᵥ_eq [IsFiniteMeasure σ] (hP : ∀ i, Integrable (fun x => P x i) σ)
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ∫ᵛ x, g x ∂•(σ.withDensityᵥ P) = ∫ x, g x • P x ∂σ := by
  have hac := euclideanVariation_withDensityᵥ_absolutelyContinuous hP
  have hb := withDensityᵥ_ae_eq_rnDeriv_smul_polar hP
  have hgP : ∀ i, Integrable (fun x => g x * P x i) σ := fun i =>
    (hP i).bdd_mul hg.aestronglyMeasurable (Eventually.of_forall hC)
  funext i
  rw [integral_smul_vectorMeasure_apply _ hg hC,
    eval_integral (f := fun x => g x • P x) (fun j => by simpa using hgP j) i]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_toReal_rnDeriv_mul hac (f := fun x => g x * polar (σ.withDensityᵥ P) x i)]
  refine integral_congr_ae ?_
  filter_upwards [hb] with x hx
  have := congrFun hx i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [this]; ring

/-- If `|P| = 1` `σ`-a.e., then `|T| = σ` and `polar T = P`
`σ`-a.e. -/
theorem euclideanVariation_withDensityᵥ_eq_of_norm_eq_one [IsFiniteMeasure σ]
    (hP : ∀ i, Integrable (fun x => P x i) σ) (h1 : ∀ᵐ x ∂σ, piEuclideanNorm (P x) = 1) :
    euclideanVariation (σ.withDensityᵥ P) = σ ∧
      polar (σ.withDensityᵥ P) =ᵐ[σ] P := by
  have hac := euclideanVariation_withDensityᵥ_absolutelyContinuous hP
  have hb := withDensityᵥ_ae_eq_rnDeriv_smul_polar hP
  have hQ : ∀ᵐ x ∂σ, ((euclideanVariation (σ.withDensityᵥ P)).rnDeriv σ x ≠ 0) →
      piEuclideanNorm (polar (σ.withDensityᵥ P) x) = 1 :=
    Measure.ae_rnDeriv_ne_zero_imp_of_ae σ (piEuclideanNorm_polar_eq_one _)
  have hone : ∀ᵐ x ∂σ, (euclideanVariation (σ.withDensityᵥ P)).rnDeriv σ x = 1 := by
    filter_upwards [hb, h1, hQ] with x hx h1x hQx
    have hne : (euclideanVariation (σ.withDensityᵥ P)).rnDeriv σ x ≠ 0 := by
      intro h0
      rw [hx, h0] at h1x
      simp [piEuclideanNorm] at h1x
    have hQ1 := hQx hne
    rw [hx, piEuclideanNorm_smul, hQ1, mul_one,
      abs_of_nonneg ENNReal.toReal_nonneg] at h1x
    exact ENNReal.toReal_eq_one_iff _ |>.1 h1x
  refine ⟨?_, ?_⟩
  · rw [← Measure.withDensity_rnDeriv_eq _ _ hac, withDensity_congr_ae hone, withDensity_const, one_smul]
  · filter_upwards [hb, hone] with x hx hx1
    rw [hx, hx1]
    simp

end AFree
