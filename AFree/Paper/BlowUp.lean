module

public import AFree.Defs
public import AFree.Paper.FreePair
public import AFree.Paper.GoodPoints
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-!
# The blow-up

The rescaled measures `σ_r`, `ν_r` around a point `x₀` and their properties, for a single radius `r > 0`,
as in [DPR, proof of Theorem 1.1]. The radii `r_j` are chosen elsewhere.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- T(y) = (y − x₀)/r. -/
noncomputable def blowMap {d : ℕ} (x₀ : Vec d) (r : ℝ) : Vec d → Vec d := fun y => r⁻¹ • (y - x₀)

/-- c · T_♯τ. -/
noncomputable def blowMeasure {d : ℕ} (x₀ : Vec d) (r : ℝ) (c : ℝ≥0∞) (τ : Measure (Vec d)) :
    Measure (Vec d) := c • τ.map (blowMap x₀ r)

/-- P_r(z) = P(x₀ + r z). -/
def blowDensity {d : ℕ} {ι : Type*} (x₀ : Vec d) (r : ℝ) (P : Vec d → ι → ℝ) : Vec d → ι → ℝ :=
  fun z => P (x₀ + r • z)

/-- The normalising constant `c(r) = σˢ(Q_r(x₀))⁻¹`. -/
noncomputable def blowConst (σ : Measure (Vec d)) (x₀ : Vec d) (r : ℝ) : ℝ≥0∞ :=
  (σ.singularPart volume (Metric.closedBall x₀ r))⁻¹

/-- `T` as a homeomorphism, for `r ≠ 0`. -/
noncomputable def blowHomeo (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) : Vec d ≃ₜ Vec d :=
  (Homeomorph.subRight x₀).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))

lemma measurable_blowMap (x₀ : Vec d) (r : ℝ) : Measurable (blowMap x₀ r) := by
  unfold blowMap; fun_prop

lemma contDiff_blowMap (x₀ : Vec d) (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (blowMap x₀ r) := by
  unfold blowMap
  exact (contDiff_const (c := r⁻¹)).smul (contDiff_id.sub (contDiff_const (c := x₀)))

lemma measurableEmbedding_blowMap (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) :
    MeasurableEmbedding (blowMap x₀ r) :=
  (blowHomeo x₀ hr).measurableEmbedding

lemma blowDensity_blowMap {ι : Type*} (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) (P : Vec d → ι → ℝ)
    (y : Vec d) : blowDensity x₀ r P (blowMap x₀ r y) = P y := by
  simp only [blowDensity, blowMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]

lemma blowMap_preimage_closedBall (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    blowMap x₀ r ⁻¹' Metric.closedBall 0 ρ = Metric.closedBall x₀ (r * ρ) := by
  ext y
  simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm, blowMap, sub_zero]
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr]

/-- `B_r ⊆ Q_r`. -/
theorem euclideanBall_subset_closedBall {r : ℝ} (hr : 0 ≤ r) :
    euclideanBall (0 : Vec d) r ⊆ Metric.closedBall 0 r := by
  intro x hx
  simp only [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  have h1 : x i ^ 2 ≤ vecNormSq x := sq_apply_le_vecNormSq x i
  have h2 : vecNormSq x < r ^ 2 := by
    simpa [euclideanBall, euclideanSqDist] using hx
  rw [Real.norm_eq_abs]
  exact abs_le.2 (abs_le_of_sq_le_sq' (by linarith) hr)

/-- `Q_r ⊆ closure B_{√d r}`. -/
theorem closedBall_subset_euclideanClosedBall (r : ℝ) :
    Metric.closedBall (0 : Vec d) r ⊆ euclideanClosedBall 0 (Real.sqrt d * r) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hxi : ∀ i, x i ^ 2 ≤ r ^ 2 := fun i => by
    have := (norm_le_pi_norm x i).trans hx
    rw [Real.norm_eq_abs] at this
    exact sq_le_sq' (by linarith [abs_nonneg (x i), neg_abs_le (x i)]) (le_trans (le_abs_self _) this)
  show vecNormSq (x - 0) ≤ (Real.sqrt d * r) ^ 2
  rw [sub_zero, vecNormSq_eq_sum_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := Finset.sum_le_sum fun i _ => hxi i
    _ = _ := by simp

/-- `Q_t ⊆ B_{1/2}` for `t = 1/(4√d)`. -/
theorem closedBall_badset_subset (hd : 0 < d) :
    Metric.closedBall (0 : Vec d) (1 / (4 * Real.sqrt d)) ⊆ euclideanBall 0 (1 / 2) := by
  intro x hx
  have h := closedBall_subset_euclideanClosedBall _ hx
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have e : Real.sqrt d * (1 / (4 * Real.sqrt d)) = 1 / 4 := by field_simp
  rw [e] at h
  show vecNormSq (x - 0) < (1 / 2) ^ 2
  have h' : vecNormSq (x - 0) ≤ (1 / 4) ^ 2 := h
  nlinarith

section measures

variable (x₀ : Vec d) (r : ℝ)

/-- Linearity: `σ_r = α_r + ν_r`. -/
theorem blowMeasure_eq_add (c : ℝ≥0∞) (σ : Measure (Vec d))
    [σ.HaveLebesgueDecomposition volume] :
    blowMeasure x₀ r c σ = blowMeasure x₀ r c (volume.withDensity (σ.rnDeriv volume)) +
      blowMeasure x₀ r c (σ.singularPart volume) := by
  unfold blowMeasure
  conv_lhs => rw [Measure.haveLebesgueDecomposition_add σ volume]
  rw [Measure.map_add _ _ (measurable_blowMap x₀ r), smul_add, add_comm]

lemma volume_blowMap_image_null {N : Set (Vec d)} (hr : r ≠ 0) (hN : volume N = 0) :
    volume (blowMap x₀ r '' N) = 0 := by
  have : blowMap x₀ r '' N = (fun z => x₀ + r • z) ⁻¹' N := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [blowMap, smul_smul, mul_inv_cancel₀ hr] using hy
    · intro hz
      refine ⟨x₀ + r • z, hz, ?_⟩
      simp [blowMap, smul_smul, inv_mul_cancel₀ hr]
  rw [this]
  have h2 : (fun z : Vec d => x₀ + r • z) ⁻¹' N =
      (fun z : Vec d => r • z) ⁻¹' ((fun w => x₀ + w) ⁻¹' N) := rfl
  rw [h2, Measure.addHaar_preimage_smul volume hr, measure_preimage_add, hN, mul_zero]

/-- `ν_j ⟂ Lebesgue`. -/
theorem blowMeasure_singularPart_mutuallySingular (c : ℝ≥0∞) (σ : Measure (Vec d))
    (hr : r ≠ 0) :
    blowMeasure x₀ r c (σ.singularPart volume) ⟂ₘ volume := by
  obtain ⟨S, hS, hS0, hS1⟩ := Measure.mutuallySingular_singularPart σ volume
  have hemb := measurableEmbedding_blowMap x₀ hr
  refine ⟨blowMap x₀ r '' S, hemb.measurableSet_image.2 hS, ?_, ?_⟩
  · unfold blowMeasure
    rw [Measure.smul_apply, hemb.map_apply, hemb.injective.preimage_image, hS0, smul_zero]
  · have : (blowMap x₀ r '' S)ᶜ = blowMap x₀ r '' Sᶜ := ((blowHomeo x₀ hr).image_compl S).symm
    rw [this]
    exact volume_blowMap_image_null x₀ r hr hS1

/-- `ν(Q₁) = 1`. -/
theorem blowMeasure_closedBall_one (σ : Measure (Vec d)) (hr : 0 < r)
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    (hfin : σ.singularPart volume (Metric.closedBall x₀ r) < ∞) :
    blowMeasure x₀ r (blowConst σ x₀ r) (σ.singularPart volume) (Metric.closedBall 0 1) = 1 := by
  unfold blowMeasure blowConst
  rw [Measure.smul_apply, Measure.map_apply (measurable_blowMap x₀ r)
    Metric.isClosed_closedBall.measurableSet, blowMap_preimage_closedBall x₀ hr, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin.ne

/-- `ν(B_{1/2}) ≥ t^{d+1}` for `t = 1/(4√d)`, from the doubling property of `σˢ`. -/
theorem blowMeasure_euclideanBall_half_ge (σ : Measure (Vec d)) (hd : 0 < d) (hr : 0 < r)
    (hpos : 0 < σ.singularPart volume (Metric.closedBall x₀ r))
    (hfin : σ.singularPart volume (Metric.closedBall x₀ r) < ∞)
    (hG4 : ENNReal.ofReal ((1 / (4 * Real.sqrt d)) ^ (d + 1)) *
        σ.singularPart volume (Metric.closedBall x₀ r) ≤
      σ.singularPart volume (Metric.closedBall x₀ ((1 / (4 * Real.sqrt d)) * r))) :
    ENNReal.ofReal ((1 / (4 * Real.sqrt d)) ^ (d + 1)) ≤
      blowMeasure x₀ r (blowConst σ x₀ r) (σ.singularPart volume) (euclideanBall 0 (1 / 2)) := by
  set t := 1 / (4 * Real.sqrt d) with ht
  set m := σ.singularPart volume (Metric.closedBall x₀ r) with hm
  have hmeas : MeasurableSet (euclideanBall (0 : Vec d) (1 / 2)) := by
    have : euclideanBall (0 : Vec d) (1 / 2) = (fun x : Vec d => vecNormSq (x - 0)) ⁻¹' Iio ((1 / 2) ^ 2) := by
      ext x; rfl
    rw [this]
    refine measurableSet_Iio.preimage ?_
    unfold vecNormSq vecDot
    fun_prop
  have hsub : Metric.closedBall x₀ (t * r) ⊆ blowMap x₀ r ⁻¹' euclideanBall 0 (1 / 2) := by
    rw [mul_comm, ← blowMap_preimage_closedBall x₀ hr]
    exact preimage_mono (closedBall_badset_subset hd)
  unfold blowMeasure blowConst
  rw [Measure.smul_apply, Measure.map_apply (measurable_blowMap x₀ r) hmeas, smul_eq_mul]
  calc ENNReal.ofReal (t ^ (d + 1)) = m⁻¹ * (ENNReal.ofReal (t ^ (d + 1)) * m) := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel hpos.ne' hfin.ne, mul_one]
    _ ≤ _ := by gcongr; exact hG4.trans (measure_mono hsub)

end measures

section delta

variable {ι : Type*} [Fintype ι]

/-- `δ(r)`. -/
noncomputable def blowDelta (σ : Measure (Vec d)) (x₀ : Vec d) (P : Vec d → ι → ℝ) (r : ℝ) : ℝ :=
  (∫ z in Metric.closedBall 0 1, piEuclideanNorm (blowDensity x₀ r P z)
      ∂blowMeasure x₀ r (blowConst σ x₀ r) (volume.withDensity (σ.rnDeriv volume))) +
  ∫ z in Metric.closedBall 0 1, piEuclideanNorm (blowDensity x₀ r P z - P x₀)
      ∂blowMeasure x₀ r (blowConst σ x₀ r) (σ.singularPart volume)

lemma integral_blowMeasure_closedBall (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞)
    (τ : Measure (Vec d)) (f : Vec d → ℝ) :
    ∫ z in Metric.closedBall 0 1, f z ∂blowMeasure x₀ r c τ =
      c.toReal * ∫ y in Metric.closedBall x₀ r, f (blowMap x₀ r y) ∂τ := by
  have hemb := measurableEmbedding_blowMap x₀ hr.ne'
  unfold blowMeasure
  rw [Measure.restrict_smul, integral_smul_measure, smul_eq_mul,
    Measure.restrict_map hemb.measurable Metric.isClosed_closedBall.measurableSet,
    hemb.integral_map, blowMap_preimage_closedBall x₀ hr, mul_one]

/-- `δ(r)` is the `σᵃ`-ratio plus the `σˢ`-average at radius `r`. -/
theorem blowDelta_eq (σ : Measure (Vec d)) (x₀ : Vec d) (P : Vec d → ι → ℝ) {r : ℝ}
    (hr : 0 < r) :
    blowDelta σ x₀ P r =
      (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y)
          ∂volume.withDensity (σ.rnDeriv volume)) /
          (σ.singularPart volume (Metric.closedBall x₀ r)).toReal +
      (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y - P x₀)
          ∂σ.singularPart volume) /
          (σ.singularPart volume (Metric.closedBall x₀ r)).toReal := by
  unfold blowDelta
  rw [integral_blowMeasure_closedBall x₀ hr, integral_blowMeasure_closedBall x₀ hr]
  simp only [blowDensity_blowMap x₀ hr.ne', blowConst, ENNReal.toReal_inv, div_eq_inv_mul]

/-- At a point where both ratios tend to `0`, `δ(r) → 0` as `r ↓ 0`. -/
theorem tendsto_blowDelta (σ : Measure (Vec d)) (x₀ : Vec d) (P : Vec d → ι → ℝ)
    (hG2 : Tendsto (fun r => (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y - P x₀)
          ∂σ.singularPart volume) / (σ.singularPart volume (Metric.closedBall x₀ r)).toReal)
        (𝓝[>] 0) (𝓝 0))
    (hG3 : Tendsto (fun r => (∫ y in Metric.closedBall x₀ r, piEuclideanNorm (P y)
          ∂volume.withDensity (σ.rnDeriv volume)) /
            (σ.singularPart volume (Metric.closedBall x₀ r)).toReal) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (blowDelta σ x₀ P) (𝓝[>] 0) (𝓝 0) := by
  have := hG3.add hG2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (blowDelta_eq σ x₀ P hr).symm

end delta

/-- `B₁ ⊆ Q₁`. -/
theorem euclideanBall_one_subset_closedBall_one :
    euclideanBall (0 : Vec d) 1 ⊆ Metric.closedBall 0 1 :=
  euclideanBall_subset_closedBall zero_le_one

/-- `Q₁ ⊆ T(Ω)` when `Q_r(x₀) ⊆ Ω`. -/
theorem closedBall_one_subset_blowMap_image {Ω : Set (Vec d)} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (hΩ : Metric.closedBall x₀ r ⊆ Ω) : Metric.closedBall (0 : Vec d) 1 ⊆ blowMap x₀ r '' Ω := by
  intro z hz
  refine ⟨x₀ + r • z, hΩ ?_, ?_⟩
  · have := blowMap_preimage_closedBall x₀ hr 1
    rw [mul_one] at this
    rw [← this]
    simpa [blowMap, smul_smul, inv_mul_cancel₀ hr.ne'] using hz
  · simp [blowMap, smul_smul, inv_mul_cancel₀ hr.ne']

section free

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma isTestFunctionOn_comp_blowMap {Ω : Set (Vec d)} (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0)
    {ψ : Vec d → ℝ} (hψ : IsTestFunctionOn (blowMap x₀ r '' Ω) ψ) :
    IsTestFunctionOn Ω (ψ ∘ blowMap x₀ r) := by
  refine ⟨hψ.1.comp (contDiff_blowMap x₀ r), hψ.2.1.comp_homeomorph (blowHomeo x₀ hr), ?_⟩
  have h : tsupport (ψ ∘ blowMap x₀ r) = blowMap x₀ r ⁻¹' tsupport ψ :=
    tsupport_comp_eq_preimage ψ (blowHomeo x₀ hr)
  rw [h]
  intro y hy
  obtain ⟨y', hy', e⟩ := hψ.2.2 hy
  rwa [← (blowHomeo x₀ hr).injective e]

lemma hasFDerivAt_blowMap (x₀ : Vec d) (r : ℝ) (y : Vec d) :
    HasFDerivAt (blowMap x₀ r) (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) y := by
  unfold blowMap
  exact ((hasFDerivAt_id y).sub_const x₀).const_smul r⁻¹

lemma euclideanCoordDeriv_comp_blowMap (x₀ : Vec d) (r : ℝ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (ℓ : Fin d) (y : Vec d) :
    euclideanCoordDeriv ℓ (ψ ∘ blowMap x₀ r) y = r⁻¹ * euclideanCoordDeriv ℓ ψ (blowMap x₀ r y) := by
  have hd : DifferentiableAt ℝ ψ (blowMap x₀ r y) :=
    (hψ.differentiable (by simp)) _
  unfold euclideanCoordDeriv
  rw [((hd.hasFDerivAt).comp y (hasFDerivAt_blowMap x₀ r y)).fderiv]
  simp

omit [Fintype κ] in
/-- The rescaled equation. -/
theorem blowUp_equation {Ω : Set (Vec d)} {A : Fin d → Matrix κ ι ℝ} {A₀ : Matrix κ ι ℝ}
    {σ : Measure (Vec d)} {P : Vec d → ι → ℝ} (h : IsFreePair Ω A A₀ σ P) (x₀ : Vec d)
    {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) {ψ : Vec d → ℝ}
    (hψ : IsTestFunctionOn (blowMap x₀ r '' Ω) ψ) :
    r • (A₀ *ᵥ ∫ z, ψ z • blowDensity x₀ r P z ∂blowMeasure x₀ r c σ) =
      ∑ ℓ, A ℓ *ᵥ ∫ z, euclideanCoordDeriv ℓ ψ z • blowDensity x₀ r P z
        ∂blowMeasure x₀ r c σ := by
  have hemb := measurableEmbedding_blowMap x₀ hr.ne'
  have key := h.2 _ (isTestFunctionOn_comp_blowMap x₀ hr.ne' hψ)
  have e0 : ∫ z, ψ z • blowDensity x₀ r P z ∂blowMeasure x₀ r c σ =
      c.toReal • ∫ y, ψ (blowMap x₀ r y) • P y ∂σ := by
    unfold blowMeasure
    rw [integral_smul_measure, hemb.integral_map]
    simp only [blowDensity_blowMap x₀ hr.ne']
  have e1 : ∀ ℓ, ∫ z, euclideanCoordDeriv ℓ ψ z • blowDensity x₀ r P z ∂blowMeasure x₀ r c σ =
      c.toReal • ∫ y, euclideanCoordDeriv ℓ ψ (blowMap x₀ r y) • P y ∂σ := by
    intro ℓ
    unfold blowMeasure
    rw [integral_smul_measure, hemb.integral_map]
    simp only [blowDensity_blowMap x₀ hr.ne']
  have e2 : ∀ ℓ, ∫ y, euclideanCoordDeriv ℓ (ψ ∘ blowMap x₀ r) y • P y ∂σ =
      r⁻¹ • ∫ y, euclideanCoordDeriv ℓ ψ (blowMap x₀ r y) • P y ∂σ := by
    intro ℓ
    rw [← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [euclideanCoordDeriv_comp_blowMap x₀ r hψ.1 ℓ y, smul_smul]
  simp only [Function.comp_apply, e2, Matrix.mulVec_smul] at key
  rw [e0]
  simp only [e1, Matrix.mulVec_smul, ← Finset.smul_sum]
  rw [smul_comm, key, Finset.smul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun ℓ _ => ?_)
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

end free

end AFree
