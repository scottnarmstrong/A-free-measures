module

public import AFree.Curves.Exhaust.CurveCurrent
public import AFree.Curves.Exhaust.CurveFTC

/-!
# `N_ρ` is a normal current
-/

@[expose] public section

open MeasureTheory Set
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The endpoint evaluation `γ ↦ γ(t)`. -/
def curveEnd (e : Vec d) (α : ℝ) (t : I) (γ : ccurveSpace e α) : Vec d :=
  (γ : C(I, Vec d)) t

lemma measurable_curveEnd (e : Vec d) (α : ℝ) (t : I) : Measurable (curveEnd e α t) :=
  ((continuous_eval_const t).comp continuous_subtype_val).measurable

/-- The boundary `S = (γ(1))_# ρ - (γ(0))_# ρ` of `N_ρ`, as a `KVec d (1-1)`-valued measure. -/
noncomputable def curveBoundary (e : Vec d) (α : ℝ) (ρ : Measure (ccurveSpace e α)) :
    VectorMeasure (Vec d) (KVec d (1 - 1)) :=
  (ρ.withDensityᵥ fun _ => (1 : KVec d (1 - 1))).map (curveEnd e α 1) -
    (ρ.withDensityᵥ fun _ => (1 : KVec d (1 - 1))).map (curveEnd e α 0)

lemma integrable_smul_density' {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] {ψ : Vec d → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Integrable (fun p => ψ (curveEval e α p) • vecToKVecOne (curveDeriv e α p))
      (curveXi e α ρ) :=
  integrable_pi_iff.2 fun K => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (integrable_pi_iff.1 (integrable_curveDensity hα hα2 ρ) K).bdd_mul
        (hψ.comp (measurable_curveEval e α)).aestronglyMeasurable
        (ae_of_all _ fun x => hC _)

/-- `(∫ ψ dN)_K = ∫ ψ(γ(s)) Σ_{j ∈ K} D_j dΞ`. -/
theorem integral_curveCurrent_apply {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (ρ : Measure (ccurveSpace e α)) [IsFiniteMeasure ρ] {ψ : Vec d → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) (K : KIdx d 1) :
    (∫ᵛ x, ψ x ∂•(curveCurrent e α ρ)) K =
      ∫ p, ψ (curveEval e α p) * ∑ j ∈ K.1, curveDeriv e α p j ∂(curveXi e α ρ) := by
  unfold curveCurrent
  rw [integral_map_withDensityᵥ_smul _ (integrable_curveDensity hα hα2 ρ)
    (measurable_curveEval e α) hψ hC]
  rw [eval_integral (fun j => integrable_pi_iff.1 (integrable_smul_density' hα hα2 ρ hψ hC) j) K]
  simp [vecToKVecOne]

lemma integral_curveBoundary {e : Vec d} {α : ℝ} (ρ : Measure (ccurveSpace e α))
    [IsFiniteMeasure ρ] {φ : Vec d → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C)
    (J : KIdx d (1 - 1)) :
    (∫ᵛ x, φ x ∂•(curveBoundary e α ρ)) J =
      ∫ γ, φ (curveEnd e α 1 γ) ∂ρ - ∫ γ, φ (curveEnd e α 0 γ) ∂ρ := by
  have hint : ∀ t : I, ((ρ.withDensityᵥ fun _ => (1 : KVec d (1 - 1))).map
      (curveEnd e α t)).Integrable φ := fun t =>
    Integrable.of_bound (C := C) hφ.aestronglyMeasurable (ae_of_all _ fun x => hC x)
  unfold curveBoundary
  rw [VectorMeasure.integral_sub_vectorMeasure (hint 1) (hint 0)]
  have hi : Integrable (fun _ : ccurveSpace e α => (1 : KVec d (1 - 1))) ρ := integrable_const _
  rw [integral_map_withDensityᵥ_smul ρ hi (measurable_curveEnd e α 1) hφ hC,
    integral_map_withDensityᵥ_smul ρ hi (measurable_curveEnd e α 0) hφ hC]
  have hm : ∀ t : I, Integrable (fun γ => φ (curveEnd e α t γ) • (1 : KVec d (1 - 1))) ρ :=
    fun t => integrable_pi_iff.2 fun K => by
      simpa using (Integrable.of_bound (C := C)
        (hφ.comp (measurable_curveEnd e α t)).aestronglyMeasurable
        (ae_of_all _ fun x => hC _) : Integrable (fun γ => φ (curveEnd e α t γ)) ρ)
  simp only [Pi.sub_apply]
  rw [eval_integral (fun j => integrable_pi_iff.1 (hm 1) j) J,
    eval_integral (fun j => integrable_pi_iff.1 (hm 0) j) J]
  simp

end AFree
