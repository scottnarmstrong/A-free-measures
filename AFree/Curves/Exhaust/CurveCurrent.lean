module

public import AFree.Curves.Exhaust.CurveDeriv
public import AFree.Curves.Exhaust.VecDensity
public import AFree.Measure.Decomp.Density

/-!
# The curve current `N_ρ`: coordinate formula, integrability and mass bound
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

lemma measurable_curveEval (e : Vec d) (α : ℝ) : Measurable (curveEval e α) :=
  (continuous_ccurveSpace_eval e α).measurable

instance (e : Vec d) (α : ℝ) (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (curveXi e α ρ) := by
  unfold curveXi; infer_instance

lemma sum_kvecOne {M : Type*} [AddCommMonoid M] (f : KIdx d 1 → M) :
    ∑ K, f K = ∑ j : Fin d, f ⟨{j}, Finset.card_singleton j⟩ := by
  symm
  refine Fintype.sum_bijective (fun j : Fin d => (⟨{j}, Finset.card_singleton j⟩ : KIdx d 1))
    ⟨fun a b h => by simpa using congrArg Subtype.val h, fun K => ?_⟩ _ _ (fun j => rfl)
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 K.2
  exact ⟨j, Subtype.ext hj.symm⟩

lemma piEuclideanNorm_vecToKVecOne (v : Vec d) :
    piEuclideanNorm (vecToKVecOne v) = vecEuclideanNorm v := by
  unfold piEuclideanNorm vecEuclideanNorm vecNormSq vecDot
  rw [sum_kvecOne (fun K => vecToKVecOne v K * vecToKVecOne v K)]
  simp only [vecToKVecOne_apply]

lemma measurable_vecToKVecOne_comp {X : Type*} [MeasurableSpace X] {g : X → Vec d}
    (hg : Measurable g) : Measurable fun x => vecToKVecOne (g x) :=
  Measurable.of_eval fun _ => Finset.measurable_sum _ fun j _ =>
    (measurable_pi_apply j).comp hg

/-- The density `D̃` is `Ξ`-integrable. -/
theorem integrable_curveDensity {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] :
    Integrable (fun p => vecToKVecOne (curveDeriv e α p)) (curveXi e α ρ) := by
  refine Integrable.of_bound (C := 1)
    (measurable_vecToKVecOne_comp (measurable_curveDeriv e α)).aestronglyMeasurable ?_
  filter_upwards [(curveDeriv_borel hα hα2).2.2 ρ] with p hp
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun K => ?_
  rw [Real.norm_eq_abs]
  exact (abs_apply_le_piEuclideanNorm _ K).trans (by
    rw [piEuclideanNorm_vecToKVecOne]; exact hp.1)

/-- Coordinate formula: `N_ρ(B)_K = ∫_{ev⁻¹B} Σ_{j ∈ K} D_j dΞ`. -/
theorem curveCurrent_apply {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] {B : Set (Vec d)}
    (hB : MeasurableSet B) (K : KIdx d 1) :
    curveCurrent e α ρ B K =
      ∫ p in curveEval e α ⁻¹' B, (∑ j ∈ K.1, curveDeriv e α p j) ∂(curveXi e α ρ) := by
  have hi := integrable_curveDensity hα hα2 ρ
  unfold curveCurrent
  rw [VectorMeasure.map_apply _ (measurable_curveEval e α) hB,
    withDensityᵥ_apply hi ((measurable_curveEval e α) hB)]
  exact (eval_integral (fun j => (integrable_pi_iff.1 hi.restrict) j) K)

/-- `|N_ρ| ≤ ev_# Ξ`. -/
theorem euclideanVariation_curveCurrent_le {e : Vec d} {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] :
    euclideanVariation (curveCurrent e α ρ) ≤ (curveXi e α ρ).map (curveEval e α) := by
  have hi := integrable_curveDensity hα hα2 ρ
  have hc := fun K => integrable_pi_iff.1 hi K
  refine euclideanVariation_le_of_forall _ fun B hB => ?_
  rw [Measure.map_apply (measurable_curveEval e α) hB]
  have hpre := (measurable_curveEval e α) hB
  unfold curveCurrent
  rw [VectorMeasure.map_apply _ (measurable_curveEval e α) hB]
  refine (ofReal_piEuclideanNorm_le_euclideanVariation _ _).trans ?_
  refine (euclideanVariation_withDensityᵥ_le hc _).trans ?_
  rw [withDensity_apply _ hpre]
  calc ∫⁻ x in curveEval e α ⁻¹' B, ENNReal.ofReal
        (piEuclideanNorm (vecToKVecOne (curveDeriv e α x))) ∂curveXi e α ρ
      ≤ ∫⁻ x in curveEval e α ⁻¹' B, 1 ∂curveXi e α ρ := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [(curveDeriv_borel hα hα2).2.2 ρ] with p hp
        rw [piEuclideanNorm_vecToKVecOne]
        exact ENNReal.ofReal_le_one.2 hp.1
    _ = _ := by simp

end AFree
