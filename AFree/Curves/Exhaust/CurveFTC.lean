module

public import AFree.Curves.Exhaust.CurveDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# FTC along a normalized `C`-curve: `∫₀¹ ∇φ(γ(s)) ⬝ D(γ,s) ds = φ(γ(1)) - φ(γ(0))`
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `Σ_j v_j ∂_jφ(x) = dφ_x(v)`. -/
lemma sum_mul_euclideanCoordDeriv (φ : Vec d → ℝ) (x v : Vec d) :
    ∑ j, v j * euclideanCoordDeriv j φ x = fderiv ℝ φ x v := by
  have hv : v = ∑ j, v j • basisVec j := by
    funext i
    simp [Finset.sum_apply, basisVec_apply]
  conv_rhs => rw [hv]
  simp [map_sum, euclideanCoordDeriv]

/-- FTC for the Lipschitz function `φ ∘ γ̄`. -/
theorem curveDeriv_integral_eq_sub {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (γ : ccurveSpace e α) :
    ∫ s : I, fderiv ℝ φ ((γ : C(I, Vec d)) s) (curveDeriv e α (γ, s)) =
      φ ((γ : C(I, Vec d)) 1) - φ ((γ : C(I, Vec d)) 0) := by
  have hprops := ccurveSpace_curve_properties hα hα2 γ.2
  have hext := lipschitzWith_ccurveExt γ.2
  obtain ⟨L, hL⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  have hAC : AbsolutelyContinuousOnInterval (φ ∘ ccurveExt (γ : C(I, Vec d))) 0 1 :=
    (hL.comp hext).lipschitzOnWith.absolutelyContinuousOnInterval
  have hftc := hAC.integral_deriv_eq_sub
  have h1 : ccurveExt (γ : C(I, Vec d)) 1 = (γ : C(I, Vec d)) 1 := ccurveExt_coe _ 1
  have h0 : ccurveExt (γ : C(I, Vec d)) 0 = (γ : C(I, Vec d)) 0 := ccurveExt_coe _ 0
  simp only [Function.comp_apply, h1, h0] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hvol : (volume : Measure I) = Measure.comap Subtype.val volume := rfl
  have : ∫ s : I, fderiv ℝ φ ((γ : C(I, Vec d)) s) (curveDeriv e α (γ, s)) =
      ∫ s : I, (fun x : ℝ => fderiv ℝ φ (ccurveExt (γ : C(I, Vec d)) x)
        (deriv (ccurveExt (γ : C(I, Vec d))) x)) (s : ℝ) := by
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [curveDeriv, ccurveExt_coe]
  rw [this, hvol]
  refine (integral_subtype_comap (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1)
    measurableSet_Icc (fun x : ℝ => fderiv ℝ φ (ccurveExt (γ : C(I, Vec d)) x)
        (deriv (ccurveExt (γ : C(I, Vec d))) x))).trans ?_
  refine integral_congr_ae ?_
  filter_upwards [hprops.2.2.1] with s hs
  have hd := hφ.differentiable (by simp) (ccurveExt (γ : C(I, Vec d)) s)
  exact (fderiv_comp_deriv s hd hs.1).symm

end AFree
