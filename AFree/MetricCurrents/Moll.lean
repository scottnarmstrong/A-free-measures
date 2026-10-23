module

public import AFree.MetricCurrents.MollAux4

/-!
# Mollification of Lipschitz functions
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace AFree

open PDE

/-- The project's standard mollifier is a mollifier kernel in the above sense. -/
theorem isMollifierKernel_stdMollifier (d : ℕ) : IsMollifierKernel (stdMollifier d) :=
  MetricCurrents.Moll.isMollifierKernel_std d

/-- For `F` Euclidean `K`-Lipschitz and `ε > 0`: `F^ε` is
smooth, Euclidean `K`-Lipschitz, and `|F^ε - F| ≤ √d K ε`. -/
theorem mollLip_smooth_lipschitz {d : ℕ} {ρ : Vec d → ℝ} (hρ : IsMollifierKernel ρ) {K : ℝ≥0}
    {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollLip ρ ε F) ∧ IsEuclLipschitzWith K (mollLip ρ ε F) ∧
      ∀ x, |mollLip ρ ε F x - F x| ≤ Real.sqrt d * K * ε :=
  ⟨MetricCurrents.Moll.contDiff_mollLip hρ (MetricCurrents.Moll.continuous_of_eucl hF) hε,
    MetricCurrents.Moll.mollLip_lipschitz hρ hF hε,
    MetricCurrents.Moll.abs_mollLip_sub_le hρ hF hε⟩

/-- `∇F^{1/(n+1)}(x) → ∇F(x)` for a.e. `x`. -/
theorem ae_tendsto_partialDeriv_mollLip {d : ℕ} {ρ : Vec d → ℝ} (hρ : IsMollifierKernel ρ)
    {K : ℝ≥0} {F : Vec d → ℝ} (hF : IsEuclLipschitzWith K F) :
    ∀ᵐ x, ∀ j : Fin d, Tendsto (fun n : ℕ => partialDeriv (mollLip ρ (1 / ((n : ℝ) + 1)) F) x j)
      atTop (𝓝 (partialDeriv F x j)) := by
  have hG : ∀ j : Fin d, LocallyIntegrable (fun x => partialDeriv F x j) volume := by
    intro j
    refine (memLp_top_of_bound (C := (K : ℝ))
      (MetricCurrents.Moll.measurable_partialDeriv F j).aestronglyMeasurable ?_).locallyIntegrable
      le_top
    filter_upwards [MetricCurrents.Moll.ae_differentiableAt_of_eucl hF] with x hx
    rw [Real.norm_eq_abs]
    exact MetricCurrents.Moll.abs_partialDeriv_le hF hx j
  filter_upwards [ae_all_iff.2 fun j =>
    (Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average_norm_sub (hG j)]
    with x hx j
  have h := MetricCurrents.Moll.tendsto_conv_of_lebesgue hρ (hG j) (hx j)
  refine h.congr fun n => ?_
  rw [MetricCurrents.Moll.partialDeriv_mollLip_eq hρ hF (by positivity) x j]
  rw [← integral_sub_left_eq_self
    (fun y => partialDeriv F y j * scaledKernel ρ (1 / ((n : ℝ) + 1)) (x - y)) volume x]
  simp

end AFree
