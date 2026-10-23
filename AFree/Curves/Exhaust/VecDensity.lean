module

public import AFree.Defs.Finite
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral against a vector density
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace AFree

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

private lemma withDensity_integrable_iff (ν : Measure X) [IsFiniteMeasure ν] {f : X → ι → ℝ}
    (hf : Integrable f ν) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => g x • f x) ν :=
  integrable_pi_iff.2 fun i => by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (integrable_pi_iff.1 hf i).bdd_mul hg.aestronglyMeasurable (Eventually.of_forall hC)

/-- `∫ᵛ φ d(ν.withDensityᵥ f) = ∫ φ f dν` for finite `ν`,
integrable `f` and bounded Borel `φ`. -/
theorem integral_withDensityᵥ_smul (ν : Measure X) [IsFiniteMeasure ν] {f : X → ι → ℝ}
    (hf : Integrable f ν) {φ : X → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    ∫ᵛ x, φ x ∂•(ν.withDensityᵥ f) = ∫ x, φ x • f x ∂ν := by
  have hvar : (ν.withDensityᵥ f).variation = ν.withDensity (fun x => ‖f x‖ₑ) :=
    Measure.variation_withDensityᵥ hf
  have simple : ∀ g : SimpleFunc X ℝ,
      ∫ᵛ x, g x ∂•(ν.withDensityᵥ f) = ∫ x, g x • f x ∂ν := by
    intro g
    induction g using SimpleFunc.induction with
    | @const c s hs =>
      have e : ⇑(SimpleFunc.piecewise _ hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
          Set.indicator s (fun _ => c) := by
        ext x; by_cases hx : x ∈ s <;> simp [hx]
      rw [e, VectorMeasure.integral_indicator_const c hs, withDensityᵥ_apply hf hs]
      have e2 : (fun x => Set.indicator s (fun _ : X => c) x • f x) =
          Set.indicator s (fun x => c • f x) := by
        ext x j; by_cases hx : x ∈ s <;> simp [hx]
      rw [e2, integral_indicator hs, integral_smul]
      simp
    | @add g h hd hg' hh =>
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      obtain ⟨Ch, hCh⟩ := h.exists_forall_norm_le
      have ig : (ν.withDensityᵥ f).Integrable g := SimpleFunc.integrable_of_isFiniteMeasure _
      have ih : (ν.withDensityᵥ f).Integrable h := SimpleFunc.integrable_of_isFiniteMeasure _
      have := VectorMeasure.integral_fun_add (B := ContinuousLinearMap.lsmul ℝ ℝ) ig ih
      simp only [SimpleFunc.coe_add, Pi.add_apply] at *
      rw [this, hg', hh, ← integral_add (withDensity_integrable_iff ν hf g.measurable hCg)
        (withDensity_integrable_iff ν hf h.measurable hCh)]
      simp [add_smul]
  have hsm : StronglyMeasurable φ := hφ.stronglyMeasurable
  have hbd : ∀ n x, ‖hsm.approxBounded C n x‖ ≤ C := fun n x => hsm.norm_approxBounded_le
    ((norm_nonneg _).trans (hC x)) n x
  have hlim : ∀ x, Tendsto (fun n => hsm.approxBounded C n x) atTop (𝓝 (φ x)) :=
    fun x => hsm.tendsto_approxBounded_of_norm_le (hC x)
  have L : Tendsto (fun n => ∫ᵛ x, hsm.approxBounded C n x ∂•(ν.withDensityᵥ f)) atTop
      (𝓝 (∫ᵛ x, φ x ∂•(ν.withDensityᵥ f))) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (SimpleFunc.measurable _).aestronglyMeasurable)
      (integrable_const C) (fun n => Eventually.of_forall (hbd n))
      (Eventually.of_forall hlim)
  have R : Tendsto (fun n => ∫ x, hsm.approxBounded C n x • f x ∂ν)
      atTop (𝓝 (∫ x, φ x • f x ∂ν)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
      (fun n => ((SimpleFunc.measurable (hsm.approxBounded C n)).aemeasurable.smul
        hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
      (hf.norm.const_mul C) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hlim x).smul_const _)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hbd n x) (norm_nonneg _)
  exact tendsto_nhds_unique L (R.congr fun n => (simple _).symm)

/-- Pushforward form of `integral_withDensityᵥ_smul`. -/
theorem integral_map_withDensityᵥ_smul {Y : Type*} [MeasurableSpace Y] (ν : Measure X)
    [IsFiniteMeasure ν] {f : X → ι → ℝ} (hf : Integrable f ν) {ev : X → Y} (hev : Measurable ev)
    {φ : Y → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) :
    ∫ᵛ y, φ y ∂•((ν.withDensityᵥ f).map ev) = ∫ x, φ (ev x) • f x ∂ν := by
  rw [VectorMeasure.integral_map hev hφ.aestronglyMeasurable]
  · exact integral_withDensityᵥ_smul ν hf (hφ.comp hev) (fun x => hC _)
  · exact Integrable.of_bound (C := C) (hφ.comp hev).aestronglyMeasurable
      (Eventually.of_forall fun x => hC _)

end AFree
