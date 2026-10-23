module

public import AFree.Analysis.ConvCompact
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier transform on `Vec d`

The Fourier transform on `Vec d = Fin d → ℝ` with the Euclidean pairing `vecDot`, transported
from Mathlib's inner-product-space theory along `WithLp.toLp 2`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped FourierTransform SchwartzMap

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The Fourier transform `∫ x, e^{-2πi x·ξ} f x dx` on `Vec d`. -/
def vecFourier (f : Vec d → ℂ) (ξ : Vec d) : ℂ :=
  ∫ x, Real.fourierChar (-(vecDot x ξ)) • f x

/-- The inverse Fourier transform `∫ x, e^{2πi x·ξ} f x dx` on `Vec d`. -/
def vecFourierInv (f : Vec d → ℂ) (ξ : Vec d) : ℂ :=
  ∫ x, Real.fourierChar (vecDot x ξ) • f x

theorem vecFourier_def (f : Vec d → ℂ) (ξ : Vec d) :
    vecFourier f ξ = ∫ x, Real.fourierChar (-(vecDot x ξ)) • f x := rfl

theorem vecFourierInv_def (f : Vec d → ℂ) (ξ : Vec d) :
    vecFourierInv f ξ = ∫ x, Real.fourierChar (vecDot x ξ) • f x := rfl

/-! ### Transport (internal) -/

private abbrev P (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)

private def eqv : P d ≃L[ℝ] Vec d := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

private theorem inner_toLp (x y : Vec d) :
    inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = vecDot x y := by
  simp [PiLp.inner_apply, vecDot, mul_comm]

private theorem integral_toLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : P d → E) : ∫ x : Vec d, h (WithLp.toLp 2 x) = ∫ v, h v :=
  (PiLp.volume_preserving_toLp (Fin d)).integral_comp' (f := MeasurableEquiv.toLp 2 (Fin d → ℝ)) h

private theorem vecFourier_eq (f : Vec d → ℂ) (ξ : Vec d) :
    vecFourier f ξ = 𝓕 (fun v : P d => f (WithLp.ofLp v)) (WithLp.toLp 2 ξ) := by
  rw [Real.fourier_eq, ← integral_toLp]
  simp [vecFourier, inner_toLp]

private theorem vecFourierInv_eq (f : Vec d → ℂ) (ξ : Vec d) :
    vecFourierInv f ξ = 𝓕⁻ (fun v : P d => f (WithLp.ofLp v)) (WithLp.toLp 2 ξ) := by
  rw [Real.fourierInv_eq, ← integral_toLp]
  simp [vecFourierInv, inner_toLp]

/-- Precomposition with `ofLp`: Schwartz functions on `Vec d` to Schwartz functions on `P d`. -/
private def toP : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(P d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eqv (d := d))

/-- Precomposition with `toLp`. -/
private def ofP : 𝓢(P d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eqv (d := d)).symm

private theorem toP_apply (f : 𝓢(Vec d, ℂ)) (v : P d) : toP f v = f (WithLp.ofLp v) := rfl

private theorem ofP_apply (f : 𝓢(P d, ℂ)) (x : Vec d) : ofP f x = f (WithLp.toLp 2 x) := rfl

private theorem ofP_toP (f : 𝓢(Vec d, ℂ)) : ofP (toP f) = f := by
  ext x; simp [ofP_apply, toP_apply]

private theorem toP_ofP (f : 𝓢(P d, ℂ)) : toP (ofP f) = f := by
  ext x; simp [ofP_apply, toP_apply]

/-- The Fourier transform on Schwartz space over `Vec d`, as a continuous linear map. -/
def vecFourierCLM : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm ∘L
    SchwartzMap.fourierTransformCLM ℂ (V := PiLp 2 (fun _ : Fin d => ℝ)) ∘L
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ))

/-- The inverse Fourier transform on Schwartz space over `Vec d`. -/
def vecFourierInvCLM : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm ∘L
    FourierTransform.fourierInvCLM ℂ 𝓢(PiLp 2 (fun _ : Fin d => ℝ), ℂ) ∘L
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ))

private theorem vecFourierCLM_eq :
    (vecFourierCLM : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ)) =
      ofP ∘L SchwartzMap.fourierTransformCLM ℂ ∘L toP := rfl

private theorem vecFourierInvCLM_eq :
    (vecFourierInvCLM : 𝓢(Vec d, ℂ) →L[ℂ] 𝓢(Vec d, ℂ)) =
      ofP ∘L FourierTransform.fourierInvCLM ℂ 𝓢(P d, ℂ) ∘L toP := rfl

theorem vecFourierCLM_apply (f : 𝓢(Vec d, ℂ)) (ξ : Vec d) :
    vecFourierCLM f ξ = vecFourier f ξ := by
  rw [vecFourier_eq, vecFourierCLM_eq]; rfl

theorem vecFourierInvCLM_apply (f : 𝓢(Vec d, ℂ)) (ξ : Vec d) :
    vecFourierInvCLM f ξ = vecFourierInv f ξ := by
  rw [vecFourierInv_eq, vecFourierInvCLM_eq]
  change (𝓕⁻ (toP f) : 𝓢(P d, ℂ)) (WithLp.toLp 2 ξ) = _
  rw [SchwartzMap.fourierInv_coe]; rfl

theorem vecFourier_coe (f : 𝓢(Vec d, ℂ)) : ⇑(vecFourierCLM f) = vecFourier f :=
  funext (vecFourierCLM_apply f)

theorem vecFourierInv_coe (f : 𝓢(Vec d, ℂ)) : ⇑(vecFourierInvCLM f) = vecFourierInv f :=
  funext (vecFourierInvCLM_apply f)

/-- Fourier inversion: `F⁻¹ (F f) = f`. -/
theorem vecFourierInvCLM_vecFourierCLM (f : 𝓢(Vec d, ℂ)) :
    vecFourierInvCLM (vecFourierCLM f) = f := by
  simp only [vecFourierInvCLM_eq, vecFourierCLM_eq, ContinuousLinearMap.comp_apply, toP_ofP]
  change ofP (𝓕⁻ (𝓕 (toP f))) = f
  rw [FourierTransform.fourierInv_fourier_eq]
  exact ofP_toP f

theorem vecFourierCLM_vecFourierInvCLM (f : 𝓢(Vec d, ℂ)) :
    vecFourierCLM (vecFourierInvCLM f) = f := by
  simp only [vecFourierInvCLM_eq, vecFourierCLM_eq, ContinuousLinearMap.comp_apply, toP_ofP]
  change ofP (𝓕 (𝓕⁻ (toP f))) = f
  rw [FourierTransform.fourier_fourierInv_eq]
  exact ofP_toP f

theorem vecFourierInv_vecFourier (f : 𝓢(Vec d, ℂ)) :
    vecFourierInv (vecFourier f) = f := by
  rw [← vecFourier_coe, ← vecFourierInv_coe, vecFourierInvCLM_vecFourierCLM]

theorem vecFourier_vecFourierInv (f : 𝓢(Vec d, ℂ)) :
    vecFourier (vecFourierInv f) = f := by
  rw [← vecFourierInv_coe, ← vecFourier_coe, vecFourierCLM_vecFourierInvCLM]

/-- Plancherel for Schwartz functions. -/
theorem integral_norm_sq_vecFourier (f : 𝓢(Vec d, ℂ)) :
    ∫ ξ, ‖vecFourier f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := SchwartzMap.integral_norm_sq_fourier (toP f)
  have h1 := integral_toLp (fun v : P d => ‖(𝓕 (toP f)) v‖ ^ 2)
  have h2 := integral_toLp (fun v : P d => ‖(toP f) v‖ ^ 2)
  rw [← h1, ← h2] at h
  rw [← vecFourier_coe]
  simpa [vecFourierCLM_eq, ofP_apply, toP_apply] using h

end

end AFree
