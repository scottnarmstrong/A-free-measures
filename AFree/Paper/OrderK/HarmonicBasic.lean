module

public import AFree.Harmonic.Fourier
public import AFree.Harmonic.Symbol
public import AFree.Defs

/-!
# Order-`k` harmonic analysis: basic conventions

`IsCc f` says `f` is smooth with compact support; `schw f` is its complex Schwartz coercion
(the value `0` is a junk value when `IsCc f` fails). `ccMult m f` is the Fourier multiplier
`T_m f` of such a function.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap

namespace AFree

noncomputable section

variable {d : ℕ}

/-- `f ∈ C_c^∞(ℝ^d; ℝ)`. -/
def IsCc (f : Vec d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f

open scoped Classical in
/-- The complex Schwartz function attached to `f ∈ C_c^∞` (junk value `0` otherwise). -/
def schw (f : Vec d → ℝ) : 𝓢(Vec d, ℂ) :=
  if h : IsCc f then toSchwartzC f h.1 h.2 else 0

theorem schw_apply {f : Vec d → ℝ} (hf : IsCc f) (x : Vec d) : schw f x = (f x : ℂ) := by
  simp [schw, hf]

/-- The Fourier multiplier `T_m f = F⁻¹[m f̂]` of a function `f ∈ C_c^∞`. -/
def ccMult (m : Vec d → ℂ) (f : Vec d → ℝ) : Vec d → ℂ :=
  fun x => vecMultiplier m (schw f) x

theorem vecMultiplier_apply_integral {m : Vec d → ℂ} (hm : m.HasTemperateGrowth)
    (f : 𝓢(Vec d, ℂ)) (x : Vec d) :
    vecMultiplier m f x = ∫ ξ, Real.fourierChar (vecDot ξ x) • (m ξ * vecFourier f ξ) := by
  rw [vecMultiplier_apply, vecFourierInvCLM_apply, vecFourierInv_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [SchwartzMap.smulLeftCLM_apply hm, smul_eq_mul, vecFourier_coe]

end

end AFree
