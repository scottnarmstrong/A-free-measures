module

public import AFree.Curves.Exhaust.CurveCurrentBdry

/-!
# `N_ρ` is a normal current with `|N_ρ| ≤ ρ(𝒢(C))`
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

private lemma test_bound' {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Measurable φ ∧ ∃ C, ∀ x, ‖φ x‖ ≤ C :=
  ⟨hφ.continuous.measurable, hφ.continuous.bounded_above_of_compact_support hc⟩

private lemma test_bound_deriv' {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (j : Fin d) :
    Measurable (euclideanCoordDeriv j φ) ∧ ∃ C, ∀ x, ‖euclideanCoordDeriv j φ x‖ ≤ C := by
  have hcont : Continuous (euclideanCoordDeriv j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact ⟨hcont.measurable, hcont.bounded_above_of_compact_support (hc.fderiv_apply ℝ _)⟩

private lemma boundary_identity {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∑ j : Fin d, (∫ᵛ x, euclideanCoordDeriv j φ x ∂•(curveCurrent e α ρ))
        ⟨{j}, Finset.card_singleton j⟩ =
      ∫ γ, φ (curveEnd e α 1 γ) ∂ρ - ∫ γ, φ (curveEnd e α 0 γ) ∂ρ := by
  obtain ⟨hm, C, hC⟩ := test_bound' hφ hc
  have hterm : ∀ j : Fin d, (∫ᵛ x, euclideanCoordDeriv j φ x ∂•(curveCurrent e α ρ))
      ⟨{j}, Finset.card_singleton j⟩ =
      ∫ p, euclideanCoordDeriv j φ (curveEval e α p) * curveDeriv e α p j ∂(curveXi e α ρ) := by
    intro j
    obtain ⟨hmj, Cj, hCj⟩ := test_bound_deriv' hφ hc j
    rw [integral_curveCurrent_apply hα hα2 ρ hmj hCj]
    simp
  have hint : ∀ j : Fin d, Integrable
      (fun p => euclideanCoordDeriv j φ (curveEval e α p) * curveDeriv e α p j) (curveXi e α ρ) := by
    intro j
    obtain ⟨hmj, Cj, hCj⟩ := test_bound_deriv' hφ hc j
    have := integrable_pi_iff.1 (integrable_smul_density' hα hα2 ρ hmj hCj)
      ⟨{j}, Finset.card_singleton j⟩
    simpa [vecToKVecOne] using this
  simp_rw [hterm]
  rw [← integral_finsetSum _ fun j _ => hint j]
  have hpt : ∀ p, ∑ j, euclideanCoordDeriv j φ (curveEval e α p) * curveDeriv e α p j =
      fderiv ℝ φ (curveEval e α p) (curveDeriv e α p) := fun p => by
    rw [← sum_mul_euclideanCoordDeriv]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hpt]
  have hF : Integrable (fun p => fderiv ℝ φ (curveEval e α p) (curveDeriv e α p))
      (curveXi e α ρ) := by
    have := integrable_finsetSum Finset.univ fun j _ => hint j
    refine this.congr (ae_of_all _ fun p => ?_)
    simpa using hpt p
  unfold curveXi at hF ⊢
  rw [integral_prod _ hF]
  have hfib : ∀ γ : ccurveSpace e α, ∫ s : I, fderiv ℝ φ (curveEval e α (γ, s))
      (curveDeriv e α (γ, s)) = φ (curveEnd e α 1 γ) - φ (curveEnd e α 0 γ) := fun γ =>
    curveDeriv_integral_eq_sub hα hα2 hφ hc γ
  simp_rw [hfib]
  refine integral_sub ?_ ?_ <;>
  exact Integrable.of_bound (C := C) (hm.comp (measurable_curveEnd e α _)).aestronglyMeasurable
    (ae_of_all _ fun x => hC _)

/-- For a finite measure `ρ` on `𝒢(C)`, `N_ρ` is a normal
`1`-current on `ℝ^d` (`IsNormalCurrentOn Set.univ`) with total variation at most `ρ(𝒢(C))`. -/
theorem isNormalCurrentOn_curveCurrent {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] :
    IsNormalCurrentOn Set.univ (curveCurrent e α ρ) ∧
      euclideanVariation (curveCurrent e α ρ) Set.univ ≤ ρ Set.univ := by
  refine ⟨⟨by simp, curveBoundary e α ρ, by simp, fun φ hφt J => ?_⟩, ?_⟩
  · obtain ⟨hφ, hc, -⟩ := hφt
    obtain ⟨hm, C, hC⟩ := test_bound' hφ hc
    rw [integral_curveBoundary ρ hm hC J, ← boundary_identity hα hα2 ρ hφ hc]
    obtain ⟨J1, hJ1⟩ := J
    have hJ : J1 = ∅ := Finset.card_eq_zero.1 hJ1
    subst hJ
    refine Finset.sum_congr (by ext j; simp) fun j _ => ?_
    have h : (insert j (∅ : Finset (Fin d))).card = 1 := by simp
    simp only [h, ↓reduceDIte]
    have : (⟨insert j ∅, h⟩ : KIdx d 1) = ⟨{j}, Finset.card_singleton j⟩ := Subtype.ext (by simp)
    rw [this]
    simp [insertSign]
  · refine (euclideanVariation_curveCurrent_le hα hα2 ρ Set.univ).trans ?_
    rw [Measure.map_apply (measurable_curveEval e α) MeasurableSet.univ, preimage_univ]
    unfold curveXi
    rw [← univ_prod_univ, Measure.prod_prod]
    simp

end AFree
