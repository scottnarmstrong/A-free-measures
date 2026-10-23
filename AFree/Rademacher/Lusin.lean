module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import PDEFoundation.Ambient.Basic

/-!
# Lusin's theorem for finite measures on `Vec d`

Lusin's theorem is
proved from continuous `L¹` approximants, almost everywhere convergence,
Egorov, inner regularity.
-/

@[expose] public section

open MeasureTheory Filter Topology PDE
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- Inner regularity by compact sets, in the form used throughout: a measurable set of positive
finite measure contains a compact set of positive measure. -/
theorem exists_isCompact_pos (μ : Measure (Vec d)) [IsFiniteMeasure μ] {A : Set (Vec d)}
    (hA : MeasurableSet A) (hμA : 0 < μ A) : ∃ K ⊆ A, IsCompact K ∧ 0 < μ K := by
  have hne : μ A ≠ ∞ := measure_ne_top μ A
  have hε : μ A / 2 ≠ 0 := (ENNReal.div_pos hμA.ne' (by simp)).ne'
  obtain ⟨K, hKA, hK, hlt⟩ := hA.exists_isCompact_lt_add hne hε
  refine ⟨K, hKA, hK, ?_⟩
  by_contra h
  have h0 : μ K = 0 := by simpa using h
  rw [h0, zero_add] at hlt
  exact absurd hlt (not_lt.2 (ENNReal.half_le_self))

/-- Lusin's theorem for a bounded measurable map into a second countable normed space. -/
theorem lusin_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {A : Set (Vec d)} (hA : MeasurableSet A) (hμA : 0 < μ A) {Φ : Vec d → E}
    (hΦ : Measurable Φ) (hb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) :
    ∃ K ⊆ A, IsCompact K ∧ 0 < μ K ∧ ContinuousOn Φ K := by
  obtain ⟨C, hC⟩ := hb
  have hmem : MemLp Φ 1 μ := MemLp.of_bound hΦ.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
  have hreg : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have hex : ∀ n : ℕ, ∃ g : Vec d → E, HasCompactSupport g ∧
      eLpNorm (Φ - g) 1 μ ≤ (1 / 2 : ℝ≥0∞) ^ n ∧ Continuous g ∧ MemLp g 1 μ := fun n =>
    hmem.exists_hasCompactSupport_eLpNorm_sub_le (by simp) (by simp)
  choose g _ hg1 hgc hgm using hex
  have hlim : Tendsto (fun n => eLpNorm (g n - Φ) 1 μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
      (fun n => zero_le) (fun n => ?_)
    rw [← eLpNorm_neg, neg_sub]
    exact hg1 n
  have hconv : TendstoInMeasure μ g atTop Φ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by simp) hlim
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  have hεpos : 0 < μ A / 2 := ENNReal.div_pos hμA.ne' (by simp)
  obtain ⟨t, htA, htm, htμ, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto
    (f := fun n => g (ns n)) (g := Φ) (s := A) (μ := μ)
    (fun n => (hgc (ns n)).stronglyMeasurable) hΦ.stronglyMeasurable hA (measure_ne_top μ A)
    (hae.mono fun x hx _ => hx) hεpos
  have hcont : ContinuousOn Φ (A \ t) :=
    hunif.continuousOn (Filter.Eventually.of_forall fun n => (hgc (ns n)).continuousOn).frequently
  have hpos : 0 < μ (A \ t) := by
    by_contra h
    have h0 : μ (A \ t) = 0 := by simpa using h
    have h1 : μ A ≤ μ (A \ t) + μ t := by
      calc μ A ≤ μ ((A \ t) ∪ t) := measure_mono (by intro x hx; by_cases h : x ∈ t <;> simp [h, hx])
        _ ≤ _ := measure_union_le _ _
    have h2 : μ t ≤ μ A / 2 := htμ
    rw [h0, zero_add] at h1
    have h3 : μ A ≤ μ A / 2 := h1.trans h2
    have h4 : μ A / 2 < μ A := ENNReal.half_lt_self hμA.ne' (measure_ne_top μ A)
    exact absurd h3 (not_le.2 h4)
  obtain ⟨K, hKs, hK, hKpos⟩ := exists_isCompact_pos μ (hA.diff htm) hpos
  exact ⟨K, hKs.trans Set.sdiff_subset, hK, hKpos, hcont.mono hKs⟩

/-- A compact set of positive measure has a point all of whose neighbourhoods meet it in positive
measure. -/
theorem exists_density_point (μ : Measure (Vec d)) {K : Set (Vec d)} (hK : IsCompact K)
    (hμ : 0 < μ K) : ∃ y ∈ K, ∀ ρ : ℝ, 0 < ρ → 0 < μ (K ∩ Metric.closedBall y ρ) := by
  by_contra hcon
  have hcon' : ∀ y ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ μ (K ∩ Metric.closedBall y ρ) = 0 := by
    intro y hy
    by_contra h
    exact hcon ⟨y, hy, fun ρ hρ => by
      by_contra h'
      exact h ⟨ρ, hρ, le_antisymm (not_lt.1 h') zero_le⟩⟩
  choose! ρ hρ hρ0 using hcon'
  obtain ⟨t, htK, hsub⟩ := hK.elim_nhds_subcover (fun y => Metric.ball y (ρ y))
    (fun y hy => Metric.ball_mem_nhds y (hρ y hy))
  have hnull : μ K = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      ((measure_biUnion_null_iff (s := fun y => K ∩ Metric.closedBall y (ρ y))
        t.countable_toSet).2 fun y hy => hρ0 y (htK y hy))
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hsub hx)
    exact Set.mem_iUnion₂.2 ⟨y, hy, hx, Metric.ball_subset_closedBall hxy⟩
  exact hμ.ne' hnull

end AFree.Rademacher
