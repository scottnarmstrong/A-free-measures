module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Absolutely convergent series in `L¹`

If `Σ ∫ ‖F_i‖ < ∞` then `Σ F_i` converges almost everywhere absolutely and is integrable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace AFree

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E]
  [CompleteSpace E]

omit [CompleteSpace E] in
theorem ae_summable_norm_of_summable_integral {F : ℕ → α → E} (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : ∀ᵐ a ∂μ, Summable fun i => ‖F i a‖ := by
  have hlin : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ∞ := by
    have (i : ℕ) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
      simp only [coe_nnnorm]
    rw [funext this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hs.abs
  have h1 : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
    lintegral_tsum fun i => (hF i).1.enorm
  have h2 : ∀ᵐ a ∂μ, ∑' i, ‖F i a‖ₑ < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun i => (hF i).1.enorm)
      (by rw [h1]; exact hlin)
  filter_upwards [h2] with a ha
  have : ∑' i, ((‖F i a‖₊ : NNReal) : ℝ≥0∞) ≠ ∞ := ha.ne
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)

theorem integrable_tsum_of_summable_integral {F : ℕ → α → E} (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by
  have hae := ae_summable_norm_of_summable_integral hF hs
  have hlin : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ∞ := by
    have (i : ℕ) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
      simp only [coe_nnnorm]
    rw [funext this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hs.abs
  have h1 : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
    lintegral_tsum fun i => (hF i).1.enorm
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun L a => ∑ i ∈ Finset.range L, F i a) (fun L => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hF i).1
    · filter_upwards [hae] with a ha
      exact (ha.of_norm.hasSum).tendsto_sum_nat
  · calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ < ∞ := by rw [h1]; exact lt_top_iff_ne_top.2 hlin

end AFree
