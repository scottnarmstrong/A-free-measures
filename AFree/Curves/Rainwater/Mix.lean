module

public import AFree.Curves.Rainwater.Lambda
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The mixture `[τ]_Φ = ∫ Φ(y) dτ(y)`
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace AFree

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- `[τ]_Φ = ∫ Φ(y) dτ(y)`, the measure `E ↦ ∫ Φ(y)(E) dτ(y)`. -/
noncomputable def mixMeasure (Φ : Y → ProbabilityMeasure X) (τ : Measure Y) : Measure X :=
  τ.bind fun y => (Φ y : Measure X)

/-- A continuous `Φ : Y → 𝒫(X)` is a Markov kernel (Borel dependence on `y`). -/
lemma measurable_coe_of_continuous {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) :
    Measurable fun y => (Φ y : Measure X) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {s : Set X | IsClosed s}) ?_ isPiSystem_isClosed ?_
  · exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  · intro F hF
    have hlim : ∀ y, Tendsto (fun n => ∫⁻ x, hF.apprSeq n x ∂(Φ y : Measure X)) atTop
        (𝓝 ((Φ y : Measure X) F)) := fun y => HasOuterApproxClosed.tendsto_lintegral_apprSeq hF _
    refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.2 hlim)
    exact ((ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (hF.apprSeq n)).comp hΦ).measurable

lemma mixMeasure_apply {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) (τ : Measure Y)
    {E : Set X} (hE : MeasurableSet E) :
    mixMeasure Φ τ E = ∫⁻ y, (Φ y : Measure X) E ∂τ :=
  Measure.bind_apply hE (measurable_coe_of_continuous hΦ).aemeasurable

lemma isProbabilityMeasure_mixMeasure {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ)
    (τ : ProbabilityMeasure Y) : IsProbabilityMeasure (mixMeasure Φ τ) := by
  refine ⟨?_⟩
  rw [mixMeasure_apply hΦ _ MeasurableSet.univ]
  simp

/-- `τ ↦ [τ]_Φ` as a map `𝒫(Y) → 𝒫(X)`. -/
noncomputable def mixPM {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ)
    (τ : ProbabilityMeasure Y) : ProbabilityMeasure X :=
  ⟨mixMeasure Φ τ, isProbabilityMeasure_mixMeasure hΦ τ⟩

lemma coe_mixPM {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) (τ : ProbabilityMeasure Y) :
    (mixPM hΦ τ : Measure X) = mixMeasure Φ τ := rfl

/-- `[a τ + b τ']_Φ = a [τ]_Φ + b [τ']_Φ`: `τ ↦ [τ]_Φ` is affine. -/
lemma mixMeasure_add_smul {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) (τ τ' : Measure Y)
    (a b : ℝ≥0) :
    mixMeasure Φ (a • τ + b • τ') = a • mixMeasure Φ τ + b • mixMeasure Φ τ' := by
  refine Measure.ext fun E hE => ?_
  rw [mixMeasure_apply hΦ _ hE, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    mixMeasure_apply hΦ _ hE, mixMeasure_apply hΦ _ hE, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure]

variable [CompactSpace X] [CompactSpace Y]

/-- (b) `τ ↦ [τ]_Φ` is continuous `𝒫(Y) → 𝒫(X)` for continuous
`Φ : Y → 𝒫(X)` (`X`, `Y` compact metric); it is affine by `mixMeasure_add_smul`. -/
theorem continuous_mixPM {Φ : Y → ProbabilityMeasure X} (hΦ : Continuous Φ) :
    Continuous (mixPM hΦ) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_lintegral]
  intro f
  obtain ⟨C, hC⟩ := (isCompact_range f.continuous).bddAbove
  have hbd : ∀ y, ∫⁻ x, (f x : ℝ≥0∞) ∂(Φ y : Measure X) ≠ ⊤ := fun y => by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (C : ℝ≥0∞) ∂(Φ y : Measure X)) ?_ ?_
    · simp
    · exact lintegral_mono fun x => ENNReal.coe_le_coe.2 (hC ⟨x, rfl⟩)
  have hf : Continuous fun y => ∫⁻ x, (f x : ℝ≥0∞) ∂(Φ y : Measure X) :=
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact f)).comp hΦ
  let g : C(Y, ℝ≥0) := ⟨fun y => (∫⁻ x, (f x : ℝ≥0∞) ∂(Φ y : Measure X)).toNNReal,
    ENNReal.continuousOn_toNNReal.comp_continuous hf hbd⟩
  have key : ∀ τ : ProbabilityMeasure Y, ∫⁻ x, (f x : ℝ≥0∞) ∂(mixPM hΦ τ : Measure X) =
      ∫⁻ y, (BoundedContinuousFunction.mkOfCompact g y : ℝ≥0∞) ∂(τ : Measure Y) := fun τ => by
    rw [coe_mixPM, mixMeasure, Measure.lintegral_bind (measurable_coe_of_continuous hΦ).aemeasurable
      f.continuous.measurable.coe_nnreal_ennreal.aemeasurable]
    refine lintegral_congr fun y => ?_
    exact (ENNReal.coe_toNNReal (hbd y)).symm
  simp_rw [key]
  exact ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction _

end AFree
