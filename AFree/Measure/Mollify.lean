module

public import AFree.Analysis.Bump
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import PDEFoundation.Measure.EuclideanVectorIntegral

/-!
# Mollification of measures

For a finite measure
`τ` and `f ∈ L¹(τ; E)`, `(fτ)_ε(x) = ∫ φ_ε(x - y) f(y) dτ(y)`; smoothness by differentiation
under the integral sign, the `L¹` bound on `U`, the Fubini identity and uniform convergence.
-/

@[expose] public section

open MeasureTheory Filter Topology Set PDE

namespace AFree

section Smooth

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The kernel integral `x ↦ ∫ Φ (x - y) • f y ∂τ` underlying the mollification. -/
noncomputable def kernelIntegral (Φ : Vec d → ℝ) (τ : Measure (Vec d)) (f : Vec d → E)
    (x : Vec d) : E :=
  ∫ y, Φ (x - y) • f y ∂τ

lemma aestronglyMeasurable_kernel {Φ : Vec d → ℝ} (hΦ : Continuous Φ) {τ : Measure (Vec d)}
    {f : Vec d → E} (hf : Integrable f τ) (x : Vec d) :
    AEStronglyMeasurable (fun y => Φ (x - y) • f y) τ :=
  (hΦ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hf.aestronglyMeasurable

lemma integrable_kernel {Φ : Vec d → ℝ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    {τ : Measure (Vec d)} {f : Vec d → E} (hf : Integrable f τ) (x : Vec d) :
    Integrable (fun y => Φ (x - y) • f y) τ := by
  obtain ⟨C, hC⟩ := hΦ.bounded_above_of_compact_support hc
  refine (hf.norm.const_mul C).mono' (aestronglyMeasurable_kernel hΦ hf x)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

lemma integrable_kernel_deriv {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hc : HasCompactSupport Φ)
    {τ : Measure (Vec d)} {f : Vec d → E} (hf : Integrable f τ) (x : Vec d) :
    Integrable (fun y => (fderiv ℝ Φ (x - y)).smulRight (f y)) τ := by
  have hΦ' : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hΦ'.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  refine (hf.norm.const_mul C).mono'
    (ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.smulRightL ℝ (Vec d) E)
      (hΦ'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      hf.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

lemma hasFDerivAt_kernelIntegral {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hc : HasCompactSupport Φ)
    {τ : Measure (Vec d)} {f : Vec d → E} (hf : Integrable f τ) (x : Vec d) :
    HasFDerivAt (kernelIntegral Φ τ f)
      (∫ y, (fderiv ℝ Φ (x - y)).smulRight (f y) ∂τ) x := by
  have hΦ' : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hΦ'.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  have hmeas : ∀ z, AEStronglyMeasurable
      (fun y => (fderiv ℝ Φ (z - y)).smulRight (f y)) τ := fun z =>
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.smulRightL ℝ (Vec d) E)
      (hΦ'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hf.aestronglyMeasurable
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (F' := fun z y => (fderiv ℝ Φ (z - y)).smulRight (f y)) (bound := fun y => C * ‖f y‖) Filter.univ_mem
    (Eventually.of_forall fun z => aestronglyMeasurable_kernel hΦ.continuous hf z)
    (integrable_kernel hΦ.continuous hc hf x) (hmeas x)
    (Eventually.of_forall fun y z _ => ?_) (hf.norm.const_mul C)
    (Eventually.of_forall fun y z _ => ?_)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · have h1 : HasFDerivAt (fun z : Vec d => Φ (z - y)) (fderiv ℝ Φ (z - y)) z :=
      by
        have h := (hΦ.differentiable one_ne_zero (z - y)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).sub_const y)
        simpa [Function.comp_def] using h
    exact h1.smul_const (f y)

lemma fderiv_kernelIntegral_apply [CompleteSpace E] {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hc : HasCompactSupport Φ)
    {τ : Measure (Vec d)} {f : Vec d → E} (hf : Integrable f τ) (x v : Vec d) :
    fderiv ℝ (kernelIntegral Φ τ f) x v = ∫ y, fderiv ℝ Φ (x - y) v • f y ∂τ := by
  have hΦ' : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  rw [(hasFDerivAt_kernelIntegral hΦ hc hf x).fderiv]
  rw [ContinuousLinearMap.integral_apply (integrable_kernel_deriv hΦ hc hf x)]
  rfl

lemma contDiff_nat_kernelIntegral [CompleteSpace E] {τ : Measure (Vec d)} {f : Vec d → E}
    (hf : Integrable f τ) (n : ℕ) :
    ∀ Φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      ContDiff ℝ n (kernelIntegral Φ τ f) := by
  induction n with
  | zero =>
    intro Φ hΦ hc
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_kernelIntegral (hΦ.of_le (by exact_mod_cast le_top)) hc hf x).continuousAt
  | succ m ih =>
    intro Φ hΦ hc
    have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_kernelIntegral h1 hc hf x).differentiableAt, ?_, fun v => ?_⟩
    · intro h; exact absurd h (by exact_mod_cast WithTop.coe_ne_top)
    · have hfun : (fun x => fderiv ℝ (kernelIntegral Φ τ f) x v) =
          kernelIntegral (fun z => fderiv ℝ Φ z v) τ f := by
        funext x
        exact fderiv_kernelIntegral_apply h1 hc hf x v
      rw [hfun]
      refine ih _ ?_ ?_
      · exact (hΦ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const
      · exact (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun A : Vec d →L[ℝ] ℝ => A v) (by simp)

/-- Smoothness of the kernel integral `x ↦ ∫ Φ (x - y) • f y ∂τ` for smooth compactly supported
`Φ`; internal step of the smoothness of the mollification. -/
theorem contDiff_kernelIntegral [CompleteSpace E] {Φ : Vec d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hc : HasCompactSupport Φ) {τ : Measure (Vec d)} {f : Vec d → E} (hf : Integrable f τ) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelIntegral Φ τ f) :=
  contDiff_infty.2 fun n => contDiff_nat_kernelIntegral hf n Φ hΦ hc

/-- The mollification `(fτ)_ε(x) = ∫ φ_ε(x - y) f(y) dτ(y)`. -/
noncomputable def mollify (ε : ℝ) (τ : Measure (Vec d)) (f : Vec d → E) : Vec d → E :=
  fun x => ∫ y, scaledMollifier ε (x - y) • f y ∂τ

/-- The mollified measure `τ_ε = (1 τ)_ε`. -/
noncomputable def mollifyMeasure (ε : ℝ) (τ : Measure (Vec d)) : Vec d → ℝ :=
  mollify ε τ (fun _ => (1 : ℝ))

/-- Smoothness of `(fτ)_ε`. -/
theorem contDiff_mollify [CompleteSpace E] {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    {f : Vec d → E} (hf : Integrable f τ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify ε τ f) :=
  contDiff_kernelIntegral (contDiff_scaledMollifier ε) (hasCompactSupport_scaledMollifier hε) hf

/-- The derivative formula for `(fτ)_ε`. -/
theorem fderiv_mollify [CompleteSpace E] {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    {f : Vec d → E} (hf : Integrable f τ) (x v : Vec d) :
    fderiv ℝ (mollify ε τ f) x v =
      ∫ y, (fderiv ℝ (scaledMollifier ε) (x - y) v) • f y ∂τ :=
  fderiv_kernelIntegral_apply ((contDiff_scaledMollifier ε).of_le (by exact_mod_cast le_top))
    (hasCompactSupport_scaledMollifier hε) hf x v

end Smooth

section L1

variable {d : ℕ}

lemma integrable_scaledMollifier {ε : ℝ} (hε : 0 < ε) :
    Integrable (scaledMollifier (d := d) ε) :=
  ((contDiff_scaledMollifier ε).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_scaledMollifier hε)

lemma lintegral_scaledMollifier_sub {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    ∫⁻ x, ENNReal.ofReal (scaledMollifier ε (x - y)) = 1 := by
  rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (scaledMollifier (d := d) ε x)) y,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_scaledMollifier hε)
      (Eventually.of_forall (scaledMollifier_nonneg hε.le)), integral_scaledMollifier hε]
  simp

lemma isOpen_thickening (U : Set (Vec d)) (ε : ℝ) :
    IsOpen {y : Vec d | ∃ x ∈ U, x ∈ euclideanBall y ε} := by
  have : {y : Vec d | ∃ x ∈ U, x ∈ euclideanBall y ε} =
      ⋃ x ∈ U, {y : Vec d | vecNormSq (x - y) < ε ^ 2} := by
    ext y; simp [euclideanBall, euclideanSqDist]
  rw [this]
  refine isOpen_biUnion fun x _ => isOpen_lt ?_ continuous_const
  exact (contDiff_vecNormSq (d := d)).continuous.comp (continuous_const.sub continuous_id)

lemma scaledMollifier_eq_zero_of_notMem {ε : ℝ} (hε : 0 < ε) {x y : Vec d}
    (h : x ∉ euclideanBall y ε) : scaledMollifier ε (x - y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  apply h
  have := tsupport_scaledMollifier_subset hε hx
  simpa [euclideanBall, euclideanSqDist] using this

/-- Core of the `L¹` bound: a nonnegative continuous function dominated by the mollification of
an integrable `G ≥ 0` has `U`-integral at most the `G`-integral over `U^ε`. -/
theorem setIntegral_le_integral_thickening {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    [IsFiniteMeasure τ] {U : Set (Vec d)} (hU : MeasurableSet U) {G : Vec d → ℝ}
    (hG : Integrable G τ) (hG0 : ∀ y, 0 ≤ G y) {h : Vec d → ℝ} (hh : Continuous h)
    (h0 : ∀ x, 0 ≤ h x) (hle : ∀ x, h x ≤ ∫ y, scaledMollifier ε (x - y) * G y ∂τ) :
    ∫ x in U, h x ≤ ∫ y in {y | ∃ x ∈ U, x ∈ euclideanBall y ε}, G y ∂τ := by
  set S : Set (Vec d) := {y | ∃ x ∈ U, x ∈ euclideanBall y ε} with hS
  have hSm : MeasurableSet S := (isOpen_thickening U ε).measurableSet
  have hφc : Continuous (scaledMollifier (d := d) ε) := (contDiff_scaledMollifier ε).continuous
  have hGm : AEMeasurable (fun y => ENNReal.ofReal (G y)) τ :=
    hG.aemeasurable.ennreal_ofReal
  have step1 : ∫ x in U, h x = (∫⁻ x in U, ENNReal.ofReal (h x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hh.aestronglyMeasurable
  have step2 : ∫⁻ x in U, ENNReal.ofReal (h x) ≤
      ∫⁻ x in U, ∫⁻ y, ENNReal.ofReal (scaledMollifier ε (x - y)) * ENNReal.ofReal (G y) ∂τ := by
    refine lintegral_mono fun x => ?_
    have hint : Integrable (fun y => scaledMollifier ε (x - y) * G y) τ := by
      simpa using integrable_kernel hφc (hasCompactSupport_scaledMollifier hε) hG x
    calc ENNReal.ofReal (h x) ≤ ENNReal.ofReal (∫ y, scaledMollifier ε (x - y) * G y ∂τ) :=
          ENNReal.ofReal_le_ofReal (hle x)
      _ = ∫⁻ y, ENNReal.ofReal (scaledMollifier ε (x - y) * G y) ∂τ :=
          ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y =>
            mul_nonneg (scaledMollifier_nonneg hε.le _) (hG0 y))
      _ = _ := by
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (scaledMollifier_nonneg hε.le _)]
  have step3 : ∫⁻ x in U, ∫⁻ y, ENNReal.ofReal (scaledMollifier ε (x - y)) *
      ENNReal.ofReal (G y) ∂τ =
      ∫⁻ y, ∫⁻ x in U, ENNReal.ofReal (scaledMollifier ε (x - y)) *
        ENNReal.ofReal (G y) ∂volume ∂τ := by
    refine lintegral_lintegral_swap ?_
    have hA : AEMeasurable (fun z : Vec d × Vec d =>
        ENNReal.ofReal (scaledMollifier ε (z.1 - z.2))) ((volume.restrict U).prod τ) :=
      (ENNReal.measurable_ofReal.comp (hφc.measurable.comp measurable_sub)).aemeasurable
    have hB : AEMeasurable (fun z : Vec d × Vec d => ENNReal.ofReal (G z.2))
        ((volume.restrict U).prod τ) := hGm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact hA.mul hB
  have step4 : ∫⁻ y, ∫⁻ x in U, ENNReal.ofReal (scaledMollifier ε (x - y)) *
        ENNReal.ofReal (G y) ∂volume ∂τ ≤ ∫⁻ y in S, ENNReal.ofReal (G y) ∂τ := by
    rw [← lintegral_indicator hSm]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      calc (∫⁻ x in U, ENNReal.ofReal (scaledMollifier ε (x - y))) * ENNReal.ofReal (G y)
          ≤ 1 * ENNReal.ofReal (G y) := by
            gcongr
            calc _ ≤ ∫⁻ x, ENNReal.ofReal (scaledMollifier ε (x - y)) :=
                  setLIntegral_le_lintegral _ _
              _ = 1 := lintegral_scaledMollifier_sub hε y
        _ = _ := one_mul _
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x ∈ U, ENNReal.ofReal (scaledMollifier ε (x - y)) * ENNReal.ofReal (G y) = 0 := by
        intro x hx
        rw [scaledMollifier_eq_zero_of_notMem hε (fun hxb => hy ⟨x, hx, hxb⟩)]
        simp
      rw [setLIntegral_congr_fun hU this]
      simp
  have hfin : ∫⁻ y in S, ENNReal.ofReal (G y) ∂τ ≠ ⊤ :=
    (hG.integrableOn (s := S)).lintegral_lt_top.ne
  rw [step1]
  calc _ ≤ (∫⁻ y in S, ENNReal.ofReal (G y) ∂τ).toReal :=
        ENNReal.toReal_mono hfin (step2.trans (step3.trans_le step4))
    _ = _ := (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0)
        hG.aestronglyMeasurable.restrict).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- For a Borel set `U`, `∫_U |(fτ)_ε| ≤ ∫_{U^ε} |f| dτ`, where
`U^ε = {y | B_ε(y) ∩ U ≠ ∅}`. -/
theorem integral_norm_mollify_le {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d)) [IsFiniteMeasure τ]
    {f : Vec d → E} (hf : Integrable f τ) {U : Set (Vec d)} (hU : MeasurableSet U) :
    ∫ x in U, ‖mollify ε τ f x‖ ≤
      ∫ y in {y | ∃ x ∈ U, x ∈ euclideanBall y ε}, ‖f y‖ ∂τ := by
  refine setIntegral_le_integral_thickening hε τ hU hf.norm (fun _ => norm_nonneg _)
    (contDiff_mollify hε τ hf).continuous.norm (fun _ => norm_nonneg _) fun x => ?_
  have hint : Integrable (fun y => scaledMollifier ε (x - y) * ‖f y‖) τ := by
    simpa using integrable_kernel (contDiff_scaledMollifier ε).continuous
      (hasCompactSupport_scaledMollifier hε) hf.norm x
  refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (scaledMollifier_nonneg hε.le _)]

/-- Euclidean version of the `L¹` bound for `E = Vec k`, with the Euclidean norm of the codomain. -/
theorem integral_vecEuclideanNorm_mollify_le {k : ℕ} {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    [IsFiniteMeasure τ] {f : Vec d → Vec k} (hf : Integrable f τ) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    ∫ x in U, vecEuclideanNorm (mollify ε τ f x) ≤
      ∫ y in {y | ∃ x ∈ U, x ∈ euclideanBall y ε}, vecEuclideanNorm (f y) ∂τ := by
  have hcoord : ∀ i, Integrable (fun y => f y i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).integrable_comp hf
  have hGint : Integrable (fun y => vecEuclideanNorm (f y)) τ :=
    integrable_vecEuclideanNorm_of_coord f hcoord
  have hcont : Continuous (fun x => vecEuclideanNorm (mollify ε τ f x)) := by
    have h1 := (contDiff_mollify hε τ hf).continuous
    unfold vecEuclideanNorm
    refine Real.continuous_sqrt.comp ?_
    have : Continuous (fun x : Vec k => vecNormSq x) := (contDiff_vecNormSq (d := k)).continuous
    exact this.comp h1
  refine setIntegral_le_integral_thickening hε τ hU hGint (fun _ => vecEuclideanNorm_nonneg _)
    hcont (fun _ => vecEuclideanNorm_nonneg _) fun x => ?_
  have hint : Integrable (fun y => scaledMollifier ε (x - y) • f y) τ :=
    integrable_kernel (contDiff_scaledMollifier ε).continuous
      (hasCompactSupport_scaledMollifier hε) hf x
  have hint2 : Integrable (fun y => scaledMollifier ε (x - y) * vecEuclideanNorm (f y)) τ := by
    simpa using integrable_kernel (contDiff_scaledMollifier ε).continuous
      (hasCompactSupport_scaledMollifier hε) hGint x
  have hcoord2 : ∀ i, Integrable (fun y => (scaledMollifier ε (x - y) • f y) i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).integrable_comp hint
  have heq : mollify ε τ f x = fun i => ∫ y, (scaledMollifier ε (x - y) • f y) i ∂τ := by
    funext i
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).integral_comp_comm
      hint).symm
  rw [heq]
  refine (vecEuclideanNorm_integral_le_integral_vecEuclideanNorm
    (fun y => scaledMollifier ε (x - y) • f y) hcoord2).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [vecEuclideanNorm_smul, abs_of_nonneg (scaledMollifier_nonneg hε.le _)]

section Fubini

variable {d : ℕ}

/-- Nonnegativity of `τ_ε`. -/
theorem mollifyMeasure_nonneg {ε : ℝ} (hε : 0 ≤ ε) (τ : Measure (Vec d)) (x : Vec d) :
    0 ≤ mollifyMeasure ε τ x :=
  integral_nonneg fun y => by simpa using scaledMollifier_nonneg hε (x - y)

lemma integrable_prod_kernel {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d)) [IsFiniteMeasure τ]
    {ψ : Vec d → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    Integrable (fun z : Vec d × Vec d => ψ z.1 * scaledMollifier ε (z.1 - z.2))
      (volume.prod τ) := by
  have hφc : Continuous (scaledMollifier (d := d) ε) := (contDiff_scaledMollifier ε).continuous
  have hmeas : Measurable (fun z : Vec d × Vec d => ψ z.1 * scaledMollifier ε (z.1 - z.2)) :=
    (hψ.comp measurable_fst).mul (hφc.measurable.comp measurable_sub)
  have hφint : ∀ y : Vec d, Integrable (fun x => scaledMollifier (d := d) ε (x - y)) :=
    fun y => Integrable.comp_sub_right (integrable_scaledMollifier hε) y
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · refine ((hφint y).const_mul C).mono' (hψ.mul (hφc.measurable.comp
      (measurable_id.sub_const y))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (scaledMollifier_nonneg hε.le _)]
    exact mul_le_mul_of_nonneg_right (hC x) (scaledMollifier_nonneg hε.le _)
  · refine (integrable_const C).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (hmeas.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable
    · have hb : ∀ x, ‖ψ x * scaledMollifier ε (x - y)‖ ≤ C * scaledMollifier ε (x - y) := by
        intro x
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
          (scaledMollifier_nonneg hε.le _)]
        exact mul_le_mul_of_nonneg_right (hC x) (scaledMollifier_nonneg hε.le _)
      have h1 : ∫ x, ‖ψ x * scaledMollifier ε (x - y)‖ ≤ C := by
        calc _ ≤ ∫ x, C * scaledMollifier ε (x - y) :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                ((hφint y).const_mul C) (Eventually.of_forall hb)
          _ = C := by
              rw [integral_const_mul, integral_sub_right_eq_self
                (fun x => scaledMollifier (d := d) ε x) y, integral_scaledMollifier hε, mul_one]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact h1

/-- Integrability of `ψ τ_ε` for bounded Borel `ψ`. -/
theorem integrable_mul_mollifyMeasure {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    [IsFiniteMeasure τ] {ψ : Vec d → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    Integrable (fun x => ψ x * mollifyMeasure ε τ x) := by
  have h := (integrable_prod_kernel hε τ hψ hC).integral_prod_left
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [mollifyMeasure, mollify, smul_eq_mul, mul_one]
  exact integral_const_mul (ψ x) _

/-- Integrability of `y ↦ ∫ ψ(x) φ_ε(x - y) dx` against `τ`. -/
theorem integrable_integral_mul_scaledMollifier {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    [IsFiniteMeasure τ] {ψ : Vec d → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    Integrable (fun y => ∫ x, ψ x * scaledMollifier ε (x - y)) τ :=
  (integrable_prod_kernel hε τ hψ hC).integral_prod_right

/-- Fubini: `∫ ψ τ_ε dx = ∫ (∫ ψ(x) φ_ε(x - y) dx) dτ(y)`. -/
theorem integral_mul_mollifyMeasure {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    [IsFiniteMeasure τ] {ψ : Vec d → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) :
    ∫ x, ψ x * mollifyMeasure ε τ x = ∫ y, (∫ x, ψ x * scaledMollifier ε (x - y)) ∂τ := by
  have h := integral_integral_swap (μ := volume) (ν := τ)
    (f := fun x y => ψ x * scaledMollifier ε (x - y)) (integrable_prod_kernel hε τ hψ hC)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mollifyMeasure, mollify, smul_eq_mul, mul_one]
  exact (integral_const_mul (ψ x) _).symm

end Fubini

section Uniform

variable {d : ℕ}

/-- ε-δ form, uniform in `y`. -/
theorem exists_forall_abs_integral_mul_sub_le {ψ : Vec d → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ y : Vec d,
      |(∫ x, ψ x * scaledMollifier ε (x - y)) - ψ y| ≤ η := by
  obtain ⟨δ, hδ, hδψ⟩ := Metric.uniformContinuous_iff.1
    (hc.uniformContinuous_of_continuous hψ) η hη
  refine ⟨δ / 2, by positivity, fun ε hε y => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hφc : Continuous (scaledMollifier (d := d) ε) := (contDiff_scaledMollifier ε).continuous
  have hφint : Integrable (fun x => scaledMollifier (d := d) ε (x - y)) :=
    Integrable.comp_sub_right (integrable_scaledMollifier hε0) y
  obtain ⟨B, hB⟩ := hψ.bounded_above_of_compact_support hc
  have hψint : Integrable (fun x => ψ x * scaledMollifier ε (x - y)) := by
    refine (hφint.const_mul B).mono' (hψ.mul (hφc.comp (continuous_id.sub continuous_const))
      ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (scaledMollifier_nonneg hε0.le _)]
    exact mul_le_mul_of_nonneg_right (by simpa using hB x) (scaledMollifier_nonneg hε0.le _)
  have hone : ∫ x, scaledMollifier (d := d) ε (x - y) = 1 := by
    rw [integral_sub_right_eq_self (fun x => scaledMollifier (d := d) ε x) y,
      integral_scaledMollifier hε0]
  have heq : (∫ x, ψ x * scaledMollifier ε (x - y)) - ψ y =
      ∫ x, (ψ x - ψ y) * scaledMollifier ε (x - y) := by
    simp_rw [sub_mul]
    rw [integral_sub hψint (hφint.const_mul (ψ y)), integral_const_mul, hone, mul_one]
  rw [heq]
  have hle : ‖∫ x, (ψ x - ψ y) * scaledMollifier ε (x - y)‖ ≤
      ∫ x, η * scaledMollifier ε (x - y) := by
    refine norm_integral_le_of_norm_le (hφint.const_mul η) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (scaledMollifier_nonneg hε0.le _)]
    by_cases hx : x ∈ euclideanBall y ε
    · refine mul_le_mul_of_nonneg_right ?_ (scaledMollifier_nonneg hε0.le _)
      have h1 := (mem_euclideanBall_iff_vecEuclideanNorm_lt hε0).1 hx
      have h2 : dist x y < δ := by
        rw [dist_eq_norm]
        have := norm_le_vecEuclideanNorm (x - y)
        linarith [hε.2]
      have := hδψ h2
      rw [Real.dist_eq] at this
      exact this.le
    · rw [scaledMollifier_eq_zero_of_notMem hε0 hx]; simp
  rw [integral_const_mul, hone, mul_one] at hle
  simpa using hle

end Uniform

end L1

end AFree
