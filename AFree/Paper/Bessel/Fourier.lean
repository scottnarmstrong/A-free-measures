module

public import AFree.Defs
public import AFree.Harmonic.Fourier
public import AFree.Harmonic.Symbol
public import AFree.Harmonic.Kernel.Negative

/-!
# Bridge between the Fourier conventions, and the Bessel multiplier

`vecFourier` (defined via `Real.fourierChar`) agrees with `vecFourierTransform`; for a smooth
compactly supported real `u`, `besselPotential` is the Fourier multiplier
`vecMultiplier (besselSymbol s)` applied to the Schwartz function `u`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap

namespace AFree.Bessel

variable {d : ℕ}

/-- The two Fourier transforms coincide. -/
theorem vecFourier_eq_vecFourierTransform (g : Vec d → ℂ) :
    vecFourier g = vecFourierTransform g := by
  funext ξ
  unfold vecFourier vecFourierTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  push_cast
  ring_nf

/-- The Bessel potential of a Schwartz function is the multiplier `vecMultiplier m_s`. -/
theorem vecMultiplier_besselSymbol_eq (s : ℝ) (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier (besselSymbol s) f x =
      ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (vecDot x ξ : ℂ)) *
        ((1 + 4 * Real.pi ^ 2 * vecNormSq ξ) ^ (-s / 2) : ℝ) * vecFourierTransform f ξ := by
  have hm := (isSymbol_besselSymbol (d := d) s).hasTemperateGrowth
  rw [vecMultiplier_apply, vecFourierInvCLM_apply]
  unfold vecFourierInv
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, vecFourierCLM_apply,
    vecFourier_eq_vecFourierTransform]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, besselSymbol, vecEuclideanNorm_sq,
    vecDot_comm ξ x]
  push_cast
  ring_nf

end AFree.Bessel
