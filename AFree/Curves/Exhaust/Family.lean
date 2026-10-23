module

public import AFree.Curves.Rainwater

/-!
# Exhaustion, part 1: the family `𝔄` and the maximal set `A₀`

The family of Borel sets on which `μ` is absolutely continuous with respect to a curve mixture is closed under countable unions, so it has a maximal element.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- `curveMix` is monotone for absolute continuity in the measure on `𝒢(C)`. -/
lemma curveMix_absolutelyContinuous (S : Set C(I, Vec d)) {ρ' ρ : Measure S} (h : ρ' ≪ ρ) :
    curveMix S ρ' ≪ curveMix S ρ := by
  intro E hE
  set T := toMeasurable (curveMix S ρ) E with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : curveMix S ρ T = 0 := by rw [hT, measure_toMeasurable]; exact hE
  rw [curveMix_apply S ρ hTm] at hT0
  have hmeas : Measurable fun γ : S => curveLaw (γ : C(I, Vec d)) T :=
    measurable_curveLaw_apply S hTm
  have h1 : ∀ᵐ γ : S ∂ρ, curveLaw (γ : C(I, Vec d)) T = 0 := (lintegral_eq_zero_iff hmeas).1 hT0
  have h2 := h.ae_le h1
  refine measure_mono_null (subset_toMeasurable (curveMix S ρ) E) ?_
  rw [← hT, curveMix_apply S ρ' hTm]
  exact (lintegral_eq_zero_iff hmeas).2 h2

/-- The family `𝔄`: Borel `A` with `μ⌞A ≪ [ρ]` for some finite measure `ρ` on `𝒢(C)`. -/
def IsExhaustible (e : Vec d) (α : ℝ) (μ : Measure (Vec d)) (A : Set (Vec d)) : Prop :=
  MeasurableSet A ∧ ∃ ρ : Measure (ccurveSpace e α), IsFiniteMeasure ρ ∧
    μ.restrict A ≪ curveMix (ccurveSpace e α) ρ

lemma isExhaustible_empty (e : Vec d) (α : ℝ) (μ : Measure (Vec d)) :
    IsExhaustible e α μ ∅ :=
  ⟨MeasurableSet.empty, 0, inferInstance, by simp⟩

/-- `𝔄` is closed under countable unions (weights `2⁻ⁿ / (1 + ρₙ(𝒢))`, `Measure.sum`). -/
lemma isExhaustible_iUnion {e : Vec d} {α : ℝ} {μ : Measure (Vec d)} {A : ℕ → Set (Vec d)}
    (h : ∀ n, IsExhaustible e α μ (A n)) : IsExhaustible e α μ (⋃ n, A n) := by
  refine ⟨MeasurableSet.iUnion fun n => (h n).1, ?_⟩
  choose ρ hρ hac using fun n => (h n).2
  let c : ℕ → ℝ≥0∞ := fun n => (2⁻¹) ^ n * (1 + ρ n univ)⁻¹
  have hc0 : ∀ n, c n ≠ 0 := fun n => by
    have : (1 + ρ n univ) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, measure_ne_top _ _⟩
    simp [c, this]
  have hcle : ∀ n, c n * ρ n univ ≤ (2⁻¹) ^ n := fun n => by
    have h1 : (1 + ρ n univ) ≠ 0 := by simp
    have h2 : (1 + ρ n univ) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, measure_ne_top _ _⟩
    calc c n * ρ n univ = (2⁻¹) ^ n * ((1 + ρ n univ)⁻¹ * ρ n univ) := by simp only [c]; ring
      _ ≤ (2⁻¹) ^ n * ((1 + ρ n univ)⁻¹ * (1 + ρ n univ)) := by gcongr; exact le_add_self
      _ = (2⁻¹) ^ n := by rw [ENNReal.inv_mul_cancel h1 h2, mul_one]
  let ρ0 : Measure (ccurveSpace e α) := Measure.sum fun n => c n • ρ n
  have hfin : IsFiniteMeasure ρ0 := by
    refine ⟨?_⟩
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, smul_eq_mul]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hcle) ?_
    rw [ENNReal.tsum_geometric]
    have : (1 - (2 : ℝ≥0∞)⁻¹) ≠ 0 := by
      rw [ne_eq, tsub_eq_zero_iff_le, not_le]
      exact ENNReal.inv_lt_one.2 (by norm_num)
    exact ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 this)
  refine ⟨ρ0, hfin, ?_⟩
  intro E hE
  have hn : ∀ n, μ (E ∩ A n) = 0 := by
    intro n
    have hρn : ρ n ≪ ρ0 :=
      (Measure.absolutelyContinuous_smul (hc0 n)).trans
        (Measure.absolutelyContinuous_of_le (Measure.le_sum (fun n => c n • ρ n) n))
    have := (hac n).trans (curveMix_absolutelyContinuous _ hρn) hE
    rwa [Measure.restrict_apply' (h n).1] at this
  have : μ (E ∩ ⋃ n, A n) = 0 := by
    rw [inter_iUnion]; exact measure_iUnion_null hn
  rwa [Measure.restrict_apply' (MeasurableSet.iUnion fun n => (h n).1)]

/-- There is `A₀ ∈ 𝔄` with `μ(A₀) = sup {μ(A) : A ∈ 𝔄}`. -/
theorem exhaust_maximal (e : Vec d) (α : ℝ) (μ : Measure (Vec d)) :
    ∃ A₀, IsExhaustible e α μ A₀ ∧ ∀ A, IsExhaustible e α μ A → μ A ≤ μ A₀ := by
  let S : Set ℝ≥0∞ := {x | ∃ A, IsExhaustible e α μ A ∧ μ A = x}
  have hne : S.Nonempty := ⟨_, ∅, isExhaustible_empty e α μ, rfl⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hne (OrderTop.bddAbove S)
  choose A hA hAu using huS
  refine ⟨⋃ n, A n, isExhaustible_iUnion hA, fun B hB => ?_⟩
  have h1 : μ B ≤ sSup S := le_sSup ⟨B, hB, rfl⟩
  refine h1.trans (le_of_tendsto' hu fun n => ?_)
  rw [← hAu n]
  exact measure_mono (subset_iUnion A n)

end AFree
