module

public import AFree.TopCurrents.Basic

/-!
# `u_#`: well-definedness

For `f ∈ Lip_b` and `π ∈ Lip^d`, `f u det Dπ` is integrable: `det Dπ` is Borel
(`measurable_fderiv`) and bounded by `∏ Kᵢ` (Hadamard, `hadamard_abs_det_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents AFree.MetricCurrents.AKExt

section aux

variable {d m : ℕ}

private lemma piEuclideanNorm_jacMat_row_le {K : ℝ≥0} {F : Fin m → Vec d → ℝ} {i : Fin m}
    (hF : IsEuclLipschitzWith K (F i)) (x : Vec d) : piEuclideanNorm (jacMat F x i) ≤ K := by
  by_cases hx : DifferentiableAt ℝ (F i) x
  · have := Moll.sqrt_sum_partial_sq_le hF hx
    simpa [piEuclideanNorm, jacMat, partialDeriv, sq] using this
  · have h0 : fderiv ℝ (F i) x = 0 := fderiv_zero_of_not_differentiableAt hx
    simp [piEuclideanNorm, jacMat, h0]

/-- `|det Dπ| ≤ ∏ Kᵢ` everywhere (junk value `0` where `π` is not differentiable). -/
lemma abs_jacDet_le {K : Fin d → ℝ≥0} {π : Fin d → Vec d → ℝ}
    (hπ : ∀ i, IsEuclLipschitzWith (K i) (π i)) (x : Vec d) :
    |jacDet π x| ≤ ∏ i, (K i : ℝ) :=
  (hadamard_abs_det_le (jacMat π x)).trans
    (Finset.prod_le_prod₀ (fun _ _ => Real.sqrt_nonneg _)
      fun i _ => piEuclideanNorm_jacMat_row_le (hπ i) x)

lemma measurable_jacMat_apply (π : Fin m → Vec d → ℝ) (i : Fin m) (j : Fin d) :
    Measurable fun x => jacMat π x i j :=
  Moll.measurable_partialDeriv (π i) j

lemma measurable_jacDet (π : Fin d → Vec d → ℝ) : Measurable (jacDet π) := by
  have : jacDet π = fun x => ∑ σ : Equiv.Perm (Fin d),
      Equiv.Perm.sign σ • ∏ i, jacMat π x (σ i) i := by
    funext x; rw [jacDet, Matrix.det_apply]
  rw [this]
  refine Finset.measurable_sum _ fun σ _ => ?_
  exact (Finset.measurable_prod _ fun i _ => measurable_jacMat_apply π (σ i) i).const_smul _

/-- Each term `f u det Dπ` of `u_#` is integrable. -/
lemma integrable_usharp_term {u : Vec d → ℝ} (hu : Integrable u volume) {f : Vec d → ℝ}
    (hf : IsBddLipFun f) {π : Fin d → Vec d → ℝ} (hπ : IsLipTuple π) :
    Integrable (fun x => f x * u x * jacDet π x) volume := by
  choose K hK using hπ
  obtain ⟨hfL, Cf, hCf⟩ := hf
  have hfc : Continuous f := lipFun_continuous hfL
  have hm : Measurable fun x => f x * jacDet π x :=
    hfc.measurable.mul (measurable_jacDet π)
  have := hu.bdd_mul (c := Cf * ∏ i, (K i : ℝ)) hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hCf x) (abs_jacDet_le hK x) (abs_nonneg _)
        ((abs_nonneg _).trans (hCf x)))
  refine this.congr (Eventually.of_forall fun x => ?_)
  ring

end aux

end AFree
