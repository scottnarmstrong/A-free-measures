module

public import AFree.Harmonic.Fourier.Basic
public import Mathlib.Analysis.Fourier.Convolution
public import PDEFoundation.Sobolev.ClassicalLaplacian

/-!
# Derivatives, multipliers and convolution for the Fourier transform on `Vec d`
-/

@[expose] public section

open MeasureTheory PDE
open scoped FourierTransform SchwartzMap Convolution LineDeriv

namespace AFree

noncomputable section

variable {d : ℕ}

/-! ### Derivative rule -/

private abbrev P (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)

private theorem integral_toLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : P d → E) : ∫ x : Vec d, h (WithLp.toLp 2 x) = ∫ v, h v :=
  (PiLp.volume_preserving_toLp (Fin d)).integral_comp' (f := MeasurableEquiv.toLp 2 (Fin d → ℝ)) h

private abbrev eqv (d : ℕ) : P d ≃L[ℝ] Vec d := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

private abbrev toP : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(P d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eqv d)

private abbrev ofP : 𝓢(P d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eqv d).symm

private theorem toP_ofP' (f : 𝓢(P d, ℂ)) : toP (ofP f) = f := by
  ext x; simp

private theorem vecFourierCLM_eq' (f : 𝓢(Vec d, ℂ)) :
    vecFourierCLM f = ofP (𝓕 (toP f)) := rfl

/-- The derivative rule: `F(∂_ℓ f)(ξ) = 2πi ξ_ℓ F f(ξ)`, with `∂_ℓ` the line derivative along
`Pi.single ℓ 1`. -/
theorem vecFourier_lineDeriv (f : 𝓢(Vec d, ℂ)) (ℓ : Fin d) (ξ : Vec d) :
    vecFourier (fun x => lineDeriv ℝ f x (Pi.single ℓ 1)) ξ =
      (2 * Real.pi * Complex.I * (ξ ℓ : ℂ)) * vecFourier f ξ := by
  have h1 : toP (∂_{(Pi.single ℓ 1 : Vec d)} f) =
      ∂_{(WithLp.toLp 2 (Pi.single ℓ 1) : P d)} (toP f) := by
    exact (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
      (WithLp.toLp 2 (Pi.single ℓ 1) : P d) (eqv d) f).symm
  have h2 := SchwartzMap.fourier_lineDerivOp_eq (toP f) (WithLp.toLp 2 (Pi.single ℓ 1) : P d)
  have h3 : (fun x => lineDeriv ℝ f x (Pi.single ℓ 1)) =
      ((∂_{(Pi.single ℓ 1 : Vec d)} f : 𝓢(Vec d, ℂ)) : Vec d → ℂ) := by
    funext x; rw [SchwartzMap.lineDerivOp_apply]
  rw [h3, ← vecFourier_coe, ← vecFourier_coe, vecFourierCLM_eq', vecFourierCLM_eq', h1, h2]
  have hT : (fun v : P d => inner ℝ v (WithLp.toLp 2 (Pi.single ℓ (1 : ℝ)) : P d)).HasTemperateGrowth :=
    by fun_prop
  change (((2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ
      (fun v : P d => inner ℝ v (WithLp.toLp 2 (Pi.single ℓ (1 : ℝ)) : P d)) (𝓕 (toP f)))
      (WithLp.toLp 2 ξ)) = 2 * Real.pi * Complex.I * (ξ ℓ : ℂ) * (𝓕 (toP f)) (WithLp.toLp 2 ξ)
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply hT]
  simp [PiLp.inner_apply]
  ring

/-- The derivative rule stated with `fderiv`. -/
theorem vecFourier_fderiv (f : 𝓢(Vec d, ℂ)) (ℓ : Fin d) (ξ : Vec d) :
    vecFourier (fun x => fderiv ℝ f x (Pi.single ℓ 1)) ξ =
      (2 * Real.pi * Complex.I * (ξ ℓ : ℂ)) * vecFourier f ξ := by
  rw [← vecFourier_lineDeriv]
  congr 1
  funext x
  exact ((f.differentiableAt (x := x)).lineDeriv_eq_fderiv).symm

/-- Bridge to `euclideanCoordDeriv`, for the complexification of a real Schwartz function. -/
theorem vecFourier_euclideanCoordDeriv (u : 𝓢(Vec d, ℝ)) (ℓ : Fin d) (ξ : Vec d) :
    vecFourier (fun x => (euclideanCoordDeriv ℓ u x : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ ℓ : ℂ)) * vecFourier (fun x => (u x : ℂ)) ξ := by
  let g : 𝓢(Vec d, ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM u
  have hg : ∀ x, g x = (u x : ℂ) := fun x => rfl
  have h := vecFourier_fderiv g ℓ ξ
  have h2 : (fun x => fderiv ℝ g x (Pi.single ℓ 1)) = fun x => (euclideanCoordDeriv ℓ u x : ℂ) := by
    funext x
    have hd : HasFDerivAt (fun y => (u y : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ u x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (u.differentiableAt.hasFDerivAt)
    have : fderiv ℝ g x = Complex.ofRealCLM.comp (fderiv ℝ u x) := by
      have : ⇑g = fun y => (u y : ℂ) := funext hg
      rw [this]; exact hd.fderiv
    rw [this]
    simp [euclideanCoordDeriv, basisVec]
  rw [h2] at h
  have hg' : ⇑g = fun y => (u y : ℂ) := funext hg
  rw [hg'] at h
  exact h

/-! ### Multipliers -/

/-- The Fourier multiplier `F⁻¹ ∘ (m ·) ∘ F`. -/
def vecMultiplier (m : Vec d → ℂ) : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ) :=
  vecFourierInvCLM ∘L SchwartzMap.smulLeftCLM ℂ m ∘L vecFourierCLM

theorem vecMultiplier_apply (m : Vec d → ℂ) (f : 𝓢(Vec d, ℂ)) :
    vecMultiplier m f = vecFourierInvCLM (SchwartzMap.smulLeftCLM ℂ m (vecFourierCLM f)) := rfl

theorem vecFourierCLM_vecMultiplier (m : Vec d → ℂ) (f : 𝓢(Vec d, ℂ)) :
    vecFourierCLM (vecMultiplier m f) = SchwartzMap.smulLeftCLM ℂ m (vecFourierCLM f) := by
  rw [vecMultiplier_apply, vecFourierCLM_vecFourierInvCLM]

theorem vecFourier_vecMultiplier {m : Vec d → ℂ} (hm : m.HasTemperateGrowth) (f : 𝓢(Vec d, ℂ))
    (ξ : Vec d) :
    vecFourier (vecMultiplier m f) ξ = m ξ * vecFourier f ξ := by
  rw [← vecFourier_coe, vecFourierCLM_vecMultiplier, SchwartzMap.smulLeftCLM_apply hm,
    vecFourier_coe]
  rfl

/-- `L²` bound for bounded multipliers. -/
theorem integral_norm_sq_vecMultiplier_le {m : Vec d → ℂ} (hm : m.HasTemperateGrowth) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : 𝓢(Vec d, ℂ)) :
    ∫ x, ‖vecMultiplier m f x‖ ^ 2 ≤ C ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  rw [← integral_norm_sq_vecFourier, ← integral_norm_sq_vecFourier f, ← integral_const_mul]
  have hint : Integrable (fun ξ => ‖vecFourier f ξ‖ ^ 2) := by
    have hg := vecFourierCLM f
    simpa [sq, vecFourier_coe] using
      ((vecFourierCLM f).integrable.norm).bdd_mul
        (vecFourierCLM f).continuous.norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa using SchwartzMap.norm_le_seminorm ℝ (vecFourierCLM f) x)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
    (hint.const_mul _) (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [vecFourier_vecMultiplier hm, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC ξ) 2) (by positivity)

/-! ### Convolution representation -/

theorem hasTemperateGrowth_vecFourier (κ : 𝓢(Vec d, ℂ)) :
    (vecFourier κ).HasTemperateGrowth := by
  rw [← vecFourier_coe]; exact (vecFourierCLM κ).hasTemperateGrowth

/-- If the symbol is the Fourier transform of a Schwartz function `κ`, the multiplier is
convolution with `κ`. -/
theorem vecMultiplier_vecFourier_apply (κ f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier (vecFourier κ) f x = ∫ y, κ (x - y) * f y := by
  let W : 𝓢(Vec d, ℂ) :=
    ofP (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (toP κ) (toP f))
  have hW : ∀ x, W x = ∫ y, κ (x - y) * f y := by
    intro x
    have h := SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) (toP κ) (toP f)
      (WithLp.toLp 2 x)
    change (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (toP κ) (toP f))
      (WithLp.toLp 2 x) = _
    rw [h, convolution_def]
    rw [← integral_toLp]
    have e : ∀ y : Vec d, (ContinuousLinearMap.mul ℂ ℂ) ((toP κ) (WithLp.toLp 2 y))
        ((toP f) (WithLp.toLp 2 x - WithLp.toLp 2 y)) = κ y * f (x - y) := fun y => rfl
    simp_rw [e]
    have := integral_sub_left_eq_self (fun y => κ (x - y) * f y) (volume : Measure (Vec d)) x
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp
  have hF : vecFourierCLM W = SchwartzMap.smulLeftCLM ℂ (vecFourier κ) (vecFourierCLM f) := by
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply (hasTemperateGrowth_vecFourier κ)]
    have h := congrArg (fun g : 𝓢(P d, ℂ) => g (WithLp.toLp 2 ξ))
      (SchwartzMap.fourier_convolution (ContinuousLinearMap.mul ℂ ℂ) (toP κ) (toP f))
    simp only [SchwartzMap.pairing_apply] at h
    change (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (toP κ) (toP f)))
      (WithLp.toLp 2 ξ) = _ at h
    rw [← vecFourier_coe κ]
    change (𝓕 (toP (ofP (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (toP κ)
      (toP f)))) : 𝓢(P d, ℂ)) (WithLp.toLp 2 ξ) = _
    rw [toP_ofP', h]
    rfl
  have : vecMultiplier (vecFourier κ) f = W := by
    rw [vecMultiplier_apply, ← hF, vecFourierInvCLM_vecFourierCLM]
  rw [this, hW]

end

end AFree
