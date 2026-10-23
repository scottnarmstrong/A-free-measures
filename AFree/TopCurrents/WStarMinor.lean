module

public import AFree.TopCurrents.Basic

/-!
# Measurability and bounds for minors of Lipschitz maps

Facts used for weak-* continuity of minors, integration by parts for minors and `u_#`: `minorDet F r c` is Borel, and for Euclidean
`C`-Lipschitz components it is bounded by `C^s` almost everywhere (Hadamard).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace AFree

open PDE

variable {d m s : ℕ}

/-- `minorDet F r c` is Borel measurable. -/
theorem minorDet_measurable (F : Fin m → Vec d → ℝ) (r : Fin s → Fin m) (c : Fin s → Fin d) :
    Measurable (minorDet F r c) := by
  have hm : Measurable fun x : Vec d => (fun a b : Fin s => fderiv ℝ (F (r a)) x (Pi.single (c b) 1)) :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b =>
      measurable_fderiv_apply_const ℝ (F (r a)) _
  have hc : Continuous fun M : Fin s → Fin s → ℝ => (Matrix.of M).det :=
    continuous_id.matrix_det
  exact hc.measurable.comp hm

/-- Hadamard bound for the minor at a point of differentiability. -/
theorem abs_minorDet_le {C : ℝ≥0} {F : Fin m → Vec d → ℝ} (hF : ∀ i, IsEuclLipschitzWith C (F i))
    (r : Fin s → Fin m) (c : Fin s → Fin d) (hc : Function.Injective c) {x : Vec d}
    (hx : ∀ i, DifferentiableAt ℝ (F i) x) : |minorDet F r c x| ≤ (C : ℝ) ^ s := by
  have h := hadamard_abs_minor_le (jacMat F x) (C := fun _ => (C : ℝ)) (fun i => ?_) r c hc
  · simpa [minorDet] using h
  · have := MetricCurrents.Moll.sqrt_sum_partial_sq_le (hF i) (hx i)
    simpa [piEuclideanNorm, jacMat, partialDeriv, sq] using this

/-- Almost everywhere Hadamard bound for the minor of a Euclidean `C`-Lipschitz tuple. -/
theorem ae_abs_minorDet_le {C : ℝ≥0} {F : Fin m → Vec d → ℝ}
    (hF : ∀ i, IsEuclLipschitzWith C (F i)) (r : Fin s → Fin m) (c : Fin s → Fin d)
    (hc : Function.Injective c) : ∀ᵐ x, |minorDet F r c x| ≤ (C : ℝ) ^ s := by
  have : ∀ᵐ x : Vec d, ∀ i, DifferentiableAt ℝ (F i) x :=
    ae_all_iff.2 fun i => MetricCurrents.Moll.ae_differentiableAt_of_eucl (hF i)
  filter_upwards [this] with x hx using abs_minorDet_le hF r c hc hx

/-- `g * minorDet F r c` is integrable for `g ∈ L¹` and a Euclidean Lipschitz tuple `F`. -/
theorem integrable_mul_minorDet {C : ℝ≥0} {F : Fin m → Vec d → ℝ}
    (hF : ∀ i, IsEuclLipschitzWith C (F i)) (r : Fin s → Fin m) (c : Fin s → Fin d)
    (hc : Function.Injective c) {g : Vec d → ℝ} (hg : Integrable g volume) :
    Integrable (fun x => g x * minorDet F r c x) volume := by
  refine Integrable.mono (hg.norm.mul_const ((C : ℝ) ^ s)) ?_ ?_
  · exact hg.aestronglyMeasurable.mul (minorDet_measurable F r c).aestronglyMeasurable
  · filter_upwards [ae_abs_minorDet_le hF r c hc] with x hx
    rw [norm_mul, norm_mul, norm_norm, Real.norm_eq_abs (minorDet F r c x),
      Real.norm_eq_abs ((C : ℝ) ^ s), abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C : ℝ) ^ s)]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

end AFree
