module

public import AFree.TopCurrents.WithDensityInt
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# The representation `T = u_#`

If `T ∈ M_d(ℝ^d)` satisfies `‖T‖ ≪ 𝓛^d` (the conclusion of [DPR, Theorem 1.15]), then `T = u_#` ([AK, Theorem 3.8]). The theorem `usharp_of_curr_ac`
takes this absolute continuity as a hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu AFree.MetricCurrents.AKExt

private lemma measurable_jacDet' {d : ℕ} (π : Fin d → Vec d → ℝ) : Measurable (jacDet π) := by
  have h : ∀ i j, Measurable fun x : Vec d => fderiv ℝ (π i) x (Pi.single j 1) :=
    fun i j => measurable_fderiv_apply_const ℝ (π i) (Pi.single j 1)
  unfold jacDet
  simp only [Matrix.det_apply, jacMat, Matrix.of_apply]
  refine Finset.measurable_sum _ fun σ _ => ?_
  refine Measurable.const_smul ?_ _
  exact Finset.measurable_prod _ fun i _ => h _ _

variable {d : ℕ} {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}

private lemma isAKMass_tv (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) : IsAKMass T ν.totalVariation := by
  have h := nu_mass_eq_variation hT hν (akMassMeasure_isAKMass hT)
  rw [← h]; exact akMassMeasure_isAKMass hT

/-- Under `‖T‖ ≪ 𝓛^d`, `ν = u 𝓛^d` with `u ∈ L¹`, unique a.e. -/
theorem usharp_density_existence (hT : IsMetricCurrent d T)
    (hac : ∀ μ, IsAKMass T μ → μ ≪ volume) {ν : SignedMeasure (Vec d)} (hν : IsNuMeasure T ν) :
    Integrable (ν.rnDeriv volume) volume ∧ ν = volume.withDensityᵥ (ν.rnDeriv volume) ∧
    ∀ u' : Vec d → ℝ, Integrable u' volume → ν = volume.withDensityᵥ u' →
      u' =ᵐ[volume] ν.rnDeriv volume := by
  have h1 : ν.totalVariation ≪ volume := hac _ (isAKMass_tv hT hν)
  have h2 : ν ≪ᵥ (volume : Measure (Vec d)).toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    simpa using h1
  have h3 := SignedMeasure.withDensityᵥ_rnDeriv_eq ν volume h2
  refine ⟨SignedMeasure.integrable_rnDeriv _ _, h3.symm, fun u' hu' he => ?_⟩
  exact hu'.ae_eq_of_withDensityᵥ_eq (SignedMeasure.integrable_rnDeriv _ _) (he ▸ h3.symm)

/-- Part (a): `T(f, π) = ∫ f u det Dπ dx`, given `ν = u 𝓛^d`. -/
theorem usharp_jacobian_representation (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) {u : Vec d → ℝ} (hu : Integrable u volume)
    (hνu : ν = volume.withDensityᵥ u) {f : Vec d → ℝ} (hf : IsBddLipFun f)
    {π : Fin d → Vec d → ℝ} (hπ : IsLipTuple π) : T f π = usharp u f π := by
  obtain ⟨Cf, hCf⟩ := hf.2
  choose K hK using hπ
  have hρ := isMollifierKernel_stdMollifier d
  obtain ⟨hunif, hsm, -, hae, hmin⟩ := mollmap hρ hK
  set ψn : ℕ → Fin d → Vec d → ℝ :=
    fun n i => mollLip (stdMollifier d) (1 / ((n : ℝ) + 1)) (π i) with hψn
  have hbd : ∀ n x, |jacDet (ψn n) x| ≤ ∏ i, (K i : ℝ) := by
    intro n x
    have := hmin d id id Function.injective_id n x
    rw [Matrix.submatrix_id_id] at this
    exact this
  have hJ : ∀ n, T f (ψn n) = ∫ x, f x * u x * jacDet (ψn n) x := by
    intro n
    have hψ : ∀ i, ContDiff ℝ 1 (ψn n i) := fun i =>
      (hsm i n).1.of_le (by exact_mod_cast le_top)
    have hM : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψn n i) y‖ ≤ M := by
      choose L hL using fun i => exists_lipschitzWith_of_eucl (hsm i n).2
      refine ⟨∑ i, (L i : ℝ), fun i y => ?_⟩
      exact (norm_fderiv_le_of_lipschitz ℝ (hL i)).trans
        (Finset.single_le_sum (f := fun i => (L i : ℝ)) (fun j _ => (L j).2) (Finset.mem_univ i))
    rw [nu_jacobian_integral hT hν hf hψ hM, hνu]
    have hmeas : Measurable fun x => f x * jacDet (ψn n) x :=
      (lipFun_continuous hf.1).measurable.mul (measurable_jacDet' _)
    rw [integral_withDensityᵥ_real hu hmeas (C := Cf * ∏ i, (K i : ℝ)) fun x => by
      rw [abs_mul]
      exact mul_le_mul (hCf x) (hbd n x) (abs_nonneg _) ((abs_nonneg _).trans (hCf x))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hlim := hT.2.2.2.2.1 f hf π (fun i => ⟨K i, hK i⟩) ψn
    ⟨Finset.univ.sup K, fun n i => isEucl_mono (Finset.le_sup (Finset.mem_univ i)) (hsm i n).2⟩
    (fun i x => (hunif i).tendsto_at x)
  have hlim2 : Tendsto (fun n => ∫ x, f x * u x * jacDet (ψn n) x) atTop
      (𝓝 (∫ x, f x * u x * jacDet π x)) := by
    have hm : Measurable f := (lipFun_continuous hf.1).measurable
    refine tendsto_integral_of_dominated_convergence (fun x => Cf * |u x| * ∏ i, (K i : ℝ)) ?_ ?_ ?_ ?_
    · intro n
      exact (hm.aestronglyMeasurable.mul hu.aestronglyMeasurable).mul
        (measurable_jacDet' _).aestronglyMeasurable
    · exact (hu.abs.const_mul _).mul_const _
    · intro n
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hCf x) le_rfl (abs_nonneg _) ((abs_nonneg _).trans (hCf x)))
        (hbd n x) (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans (hCf x)) (abs_nonneg _))
    · have := hae d id id Function.injective_id
      filter_upwards [this] with x hx
      simp only [Matrix.submatrix_id_id] at hx
      exact (tendsto_const_nhds.mul hx : _)
  have := tendsto_nhds_unique hlim (hlim2.congr fun n => (hJ n).symm)
  rw [this]
  rfl

/-- Part (b): `‖T‖ = |u| 𝓛^d`, given `ν = u 𝓛^d`. -/
theorem usharp_mass_is_abs_u (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) {u : Vec d → ℝ} (hu : Integrable u volume)
    (hνu : ν = volume.withDensityᵥ u) : IsAKMass T (uMass u) := by
  have h := isAKMass_tv hT hν
  have : ν.totalVariation = uMass u := by
    rw [SignedMeasure.totalVariation_eq_variation, hνu, Measure.variation_withDensityᵥ hu]
    simp [uMass, Real.enorm_eq_ofReal_abs]
  rwa [this] at h

/-- Representation ([AK, Theorem 3.8]): for `T ∈ M_d(ℝ^d)` with `‖T‖ ≪ 𝓛^d`
(the conclusion of [DPR, Theorem 1.15]), `ν = u 𝓛^d` with `u ∈ L¹` unique a.e., `T(f,π) = ∫ f u det Dπ`
and `‖T‖ = |u| 𝓛^d`. -/
theorem usharp_of_curr_ac (hT : IsMetricCurrent d T) (hac : ∀ μ, IsAKMass T μ → μ ≪ volume)
    {ν : SignedMeasure (Vec d)} (hν : IsNuMeasure T ν) :
    ∃ u : Vec d → ℝ, Integrable u volume ∧ ν = volume.withDensityᵥ u ∧
      (∀ u' : Vec d → ℝ, Integrable u' volume → ν = volume.withDensityᵥ u' → u' =ᵐ[volume] u) ∧
      (∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, IsLipTuple π →
        T f π = ∫ x, f x * u x * jacDet π x) ∧ IsAKMass T (uMass u) := by
  obtain ⟨hi, he, hu⟩ := usharp_density_existence hT hac hν
  exact ⟨_, hi, he, hu, fun f hf π hπ => usharp_jacobian_representation hT hν hi he hf hπ,
    usharp_mass_is_abs_u hT hν hi he⟩

end AFree
