module

public import AFree.Defs
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# The variation measures are finite

`|μ|` and Mathlib's sup-norm variation `μ.variation` are finite measures. So `polar μ` and the
Lebesgue singular part are the Radon–Nikodym derivative and singular part, and the test-function
integrals `∫ᵛ x, φ x ∂•μ` are integrals of bounded functions against a finite measure.
-/

public section

open MeasureTheory

namespace AFree

open PDE

variable {ι : Type*} [Fintype ι]

theorem piEuclideanNorm_le_sum_abs (v : ι → ℝ) : piEuclideanNorm v ≤ ∑ i, |v i| := by
  unfold piEuclideanNorm
  calc Real.sqrt (∑ i, v i * v i) = Real.sqrt (∑ i, |v i| ^ 2) := by simp [sq]
    _ ≤ Real.sqrt ((∑ i, |v i|) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _)
    _ = ∑ i, |v i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

theorem euclideanVariation_le_of_forall {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) {m : Measure X}
    (h : ∀ E, MeasurableSet E → ENNReal.ofReal (piEuclideanNorm (μ E)) ≤ m E) :
    euclideanVariation μ ≤ m := by
  refine Measure.le_intro fun s hs _ => ?_
  simp only [euclideanVariation, preVariation_apply, VectorMeasure.ennrealToMeasure_apply hs,
    ennrealPreVariation_apply, preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x ∈ i.parts, ENNReal.ofReal (piEuclideanNorm (μ x)) ≤ ∑ x ∈ i.parts, m x :=
        Finset.sum_le_sum fun s _ => h s s.property
    _ = m (i.parts.sup Subtype.val) := by
      rw [Finset.sup_set_eq_biUnion]
      refine (measure_biUnion_finset ?_ fun b _ => b.property).symm
      intro a ha b hb hab
      simpa [disjoint_iff, Subtype.ext_iff] using i.disjoint ha hb hab
    _ ≤ m s := by
      rw [Finset.sup_set_eq_biUnion]
      exact measure_mono <| Set.iUnion₂_subset fun _ hp => Subtype.coe_le_coe.mpr (i.le hp)

/-- `|μ(E)| ≤ |μ|(E)`. -/
theorem ofReal_piEuclideanNorm_le_euclideanVariation {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) (E : Set X) :
    ENNReal.ofReal (piEuclideanNorm (μ E)) ≤ euclideanVariation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [μ.not_measurable hE, piEuclideanNorm]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all [piEuclideanNorm]
  simp only [euclideanVariation, preVariation, VectorMeasure.ennrealToMeasure_apply hE,
    ennrealPreVariation_apply]
  grw [← preVariation.sum_le _ _ (Finpartition.indiscrete hE')]
  simp

theorem euclideanVariation_le_sum_totalVariation {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) :
    euclideanVariation μ ≤ ∑ i, (coordMeasure μ i).totalVariation := by
  refine euclideanVariation_le_of_forall μ fun E _ => ?_
  calc ENNReal.ofReal (piEuclideanNorm (μ E)) ≤ ENNReal.ofReal (∑ i, |μ E i|) :=
        ENNReal.ofReal_le_ofReal (piEuclideanNorm_le_sum_abs _)
    _ = ∑ i, ‖coordMeasure μ i E‖ₑ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← ofReal_norm, Real.norm_eq_abs]
        rfl
    _ ≤ ∑ i, (coordMeasure μ i).totalVariation E :=
        Finset.sum_le_sum fun i _ => SignedMeasure.enorm_le_totalVariation _ _
    _ = (∑ i, (coordMeasure μ i).totalVariation) E := by simp

/-- `|μ|` is a finite measure (so `polar`, `singularPart` and the test integrals are genuine). -/
instance isFiniteMeasure_euclideanVariation {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) : IsFiniteMeasure (euclideanVariation μ) :=
  ⟨lt_of_le_of_lt (euclideanVariation_le_sum_totalVariation μ Set.univ)
    (by simp [Measure.coe_finsetSum])⟩

/-- Mathlib's (sup-norm) variation is finite too, so `∫ᵛ` of a bounded continuous function is a
genuine integral. -/
instance isFiniteMeasure_variation {X : Type*} [MeasurableSpace X]
    (μ : VectorMeasure X (ι → ℝ)) : IsFiniteMeasure μ.variation := by
  refine isFiniteMeasure_of_le (euclideanVariation μ)
    (VectorMeasure.variation_le_of_forall_enorm_le fun E _ => ?_)
  calc ‖μ E‖ₑ = ENNReal.ofReal ‖μ E‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (piEuclideanNorm (μ E)) := by
        refine ENNReal.ofReal_le_ofReal
          ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_)
        rw [Real.norm_eq_abs, ← Real.sqrt_mul_self_eq_abs]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => μ E j * μ E j)
          (fun j _ => mul_self_nonneg _) (Finset.mem_univ i))
    _ ≤ euclideanVariation μ E := ofReal_piEuclideanNorm_le_euclideanVariation μ E

end AFree
