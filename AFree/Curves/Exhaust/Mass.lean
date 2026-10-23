module

public import AFree.Curves.Exhaust.CurveCurrent
public import AFree.Curves.Exhaust.OneSet

/-!
# The mass lower bound `|N_ρ| ≥ w ⬝ N_ρ ≥ c [ρ]`
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `[ρ](B) = Ξ(ev⁻¹ B)`. -/
lemma curveMix_apply_eq_curveXi (e : Vec d) (α : ℝ) (ρ : Measure (ccurveSpace e α))
    {B : Set (Vec d)} (hB : MeasurableSet B) :
    curveMix (ccurveSpace e α) ρ B = curveXi e α ρ (curveEval e α ⁻¹' B) :=
  Measure.map_apply (measurable_curveEval e α) hB

/-- Coordinates of the density `D` are `Ξ`-integrable. -/
lemma integrable_curveDeriv_apply {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] (j : Fin d) :
    Integrable (fun p => curveDeriv e α p j) (curveXi e α ρ) := by
  have := integrable_pi_iff.1 (integrable_curveDensity hα hα2 ρ) ⟨{j}, Finset.card_singleton j⟩
  simpa [vecToKVecOne] using this

/-- `ℓ ⬝ N_ρ(B) = ∫_{ev⁻¹B} ℓ ⬝ D dΞ`. -/
lemma vecDot_curveCurrent {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] {B : Set (Vec d)} (hB : MeasurableSet B)
    (ℓ : Vec d) :
    vecDot (kvecOneToVec (curveCurrent e α ρ B)) ℓ =
      ∫ p in curveEval e α ⁻¹' B, vecDot (curveDeriv e α p) ℓ ∂(curveXi e α ρ) := by
  have hint : ∀ j, Integrable (fun p => curveDeriv e α p j * ℓ j)
      ((curveXi e α ρ).restrict (curveEval e α ⁻¹' B)) := fun j =>
    ((integrable_curveDeriv_apply hα hα2 ρ j).restrict).mul_const _
  simp only [vecDot]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]
  congr 1
  rw [kvecOneToVec, curveCurrent_apply hα hα2 ρ hB]
  simp

/-- For Borel `B`: `|N_ρ|(B) ≥ (w ⬝ N_ρ)(B) ≥ c [ρ](B)`
(`c = cos α`), hence `[ρ] ≪ |N_ρ|`. -/
theorem curveCurrent_mass_lower {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] :
    (∀ B : Set (Vec d), MeasurableSet B →
      ENNReal.ofReal (Real.cos α) * curveMix (ccurveSpace e α) ρ B ≤
          ENNReal.ofReal (vecDot (kvecOneToVec (curveCurrent e α ρ B)) e) ∧
        ENNReal.ofReal (vecDot (kvecOneToVec (curveCurrent e α ρ B)) e) ≤
          euclideanVariation (curveCurrent e α ρ) B) ∧
      curveMix (ccurveSpace e α) ρ ≪ euclideanVariation (curveCurrent e α ρ) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα2⟩
  have key : ∀ B : Set (Vec d), MeasurableSet B →
      ENNReal.ofReal (Real.cos α) * curveMix (ccurveSpace e α) ρ B ≤
          ENNReal.ofReal (vecDot (kvecOneToVec (curveCurrent e α ρ B)) e) ∧
        ENNReal.ofReal (vecDot (kvecOneToVec (curveCurrent e α ρ B)) e) ≤
          euclideanVariation (curveCurrent e α ρ) B := by
    intro B hB
    have hS := (measurable_curveEval e α) hB
    refine ⟨?_, ?_⟩
    · rw [curveMix_apply_eq_curveXi e α ρ hB, vecDot_curveCurrent hα hα2 ρ hB]
      have hfin : curveXi e α ρ (curveEval e α ⁻¹' B) ≠ ⊤ := measure_ne_top _ _
      have hint : Integrable (fun p => vecDot (curveDeriv e α p) e)
          ((curveXi e α ρ).restrict (curveEval e α ⁻¹' B)) := by
        simp only [vecDot]
        exact integrable_finsetSum _ fun j _ =>
          ((integrable_curveDeriv_apply hα hα2 ρ j).restrict).mul_const _
      have hle : ∫ p in curveEval e α ⁻¹' B, Real.cos α ∂(curveXi e α ρ) ≤
          ∫ p in curveEval e α ⁻¹' B, vecDot (curveDeriv e α p) e ∂(curveXi e α ρ) := by
        refine integral_mono_ae (integrable_const _) hint (ae_restrict_of_ae ?_)
        filter_upwards [(curveDeriv_borel hα hα2).2.2 ρ] with p hp using hp.2.2
      rw [setIntegral_const, smul_eq_mul] at hle
      calc ENNReal.ofReal (Real.cos α) * curveXi e α ρ (curveEval e α ⁻¹' B)
          = ENNReal.ofReal (Real.cos α * (curveXi e α ρ).real (curveEval e α ⁻¹' B)) := by
            rw [ENNReal.ofReal_mul hc.le, Measure.real, ENNReal.ofReal_toReal hfin]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hle)
    · refine (ENNReal.ofReal_le_ofReal ?_).trans
        (piEuclideanNorm_apply_le_euclideanVariation (curveCurrent e α ρ) B)
      rw [piEuclideanNorm_kvecOne]
      calc _ ≤ |vecDot (kvecOneToVec (curveCurrent e α ρ B)) e| := le_abs_self _
        _ ≤ _ := by
          have := abs_vecDot_le_vecEuclideanNorm_mul (kvecOneToVec (curveCurrent e α ρ B)) e
          rwa [he, mul_one] at this
  refine ⟨key, ?_⟩
  intro s hs
  have hm := measurableSet_toMeasurable (euclideanVariation (curveCurrent e α ρ)) s
  have h0 : euclideanVariation (curveCurrent e α ρ)
      (toMeasurable (euclideanVariation (curveCurrent e α ρ)) s) = 0 := by
    rw [measure_toMeasurable]; exact hs
  have h1 := (key _ hm).1.trans (key _ hm).2
  rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at h1
  have h2 : curveMix (ccurveSpace e α) ρ (toMeasurable (euclideanVariation (curveCurrent e α ρ)) s) = 0 :=
    h1.resolve_left (by simpa using hc)
  exact measure_mono_null (subset_toMeasurable _ _) h2

end AFree
