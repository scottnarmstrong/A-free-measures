module

public import AFree.Curves.Rainwater.LemmaHB
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Rainwater's lemma, Borel--Cantelli step and the main statement

Rainwater's lemma: if `μ` is singular to every member of a convex weakly compact set `F` of
probability measures, one Borel set carries `μ` and is null for all of `F`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BoundedContinuousFunction

namespace AFree

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- Markov, then Borel--Cantelli: if `∫ g n dν < 4⁻ⁿ`, the set where `g n ≥ 1/2` infinitely often is
`ν`-null. -/
private lemma limsup_half_null (ν : Measure X) [IsFiniteMeasure ν] (g : ℕ → X →ᵇ ℝ)
    (hg0 : ∀ n x, 0 ≤ g n x) (hg : ∀ n, ∫ x, g n x ∂ν < (1 / 4 : ℝ) ^ n) :
    ν (limsup (fun n => {x | 1 / 2 ≤ g n x}) atTop) = 0 := by
  have hb : ∀ n, ν {x | 1 / 2 ≤ g n x} ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ n) := by
    intro n
    have h := mul_meas_ge_le_integral_of_nonneg (μ := ν)
      (Eventually.of_forall fun x => hg0 n x) ((g n).integrable ν) (1 / 2)
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [hg n]
  have hsum : Summable fun n : ℕ => 2 * (1 / 4 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  apply measure_limsup_atTop_eq_zero
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

omit [CompactSpace X] in
/-- If `⟨μ, f_n⟩ < 4⁻ⁿ` and `⟨λ, 1 - f_n⟩ < 4⁻ⁿ` for all `λ ∈ F`,
then `E = ⋃_m ⋂_{n ≥ m} {f_n < 1/2}` is Borel, `μ(Eᶜ) = 0` and `λ(E) = 0` for `λ ∈ F`. -/
theorem rainwater_borel_cantelli (μ : Measure X) [IsFiniteMeasure μ]
    (F : Set (ProbabilityMeasure X)) (f : ℕ → X →ᵇ ℝ) (hf : ∀ n, IsUnitFn (f n))
    (hμ : ∀ n, ∫ x, f n x ∂μ < (1 / 4 : ℝ) ^ n)
    (hl : ∀ l ∈ F, ∀ n, ∫ x, (1 - f n x) ∂(l : Measure X) < (1 / 4 : ℝ) ^ n) :
    ∃ E : Set X, MeasurableSet E ∧ μ Eᶜ = 0 ∧ ∀ l ∈ F, (l : Measure X) E = 0 := by
  let s : ℕ → Set X := fun n => {x | 1 / 2 ≤ f n x}
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_le measurable_const (f n).continuous.measurable
  refine ⟨(limsup s atTop)ᶜ, (MeasurableSet.measurableSet_limsup hsm).compl, ?_, ?_⟩
  · rw [compl_compl]
    exact limsup_half_null μ f (fun n x => (hf n x).1) hμ
  · intro l hl'
    have h0 := limsup_half_null (l : Measure X) (fun n => 1 - f n)
      (fun n x => by simpa using (hf n x).2) (fun n => by simpa using hl l hl' n)
    refine measure_mono_null ?_ h0
    intro x hx
    rw [mem_compl_iff, mem_limsup_iff_frequently_mem] at hx
    rw [mem_limsup_iff_frequently_mem]
    have : ∀ᶠ n in atTop, x ∉ s n := by simpa [Filter.Frequently] using hx
    refine this.frequently.mono fun n hn => ?_
    simp only [s, mem_ofPred_eq, not_le] at hn
    simp only [mem_ofPred_eq, BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_one,
      Pi.sub_apply, Pi.one_apply]
    linarith

/-- Rainwater's lemma. `X` compact metric, `F ⊆ 𝒫(X)` convex and weakly compact,
`μ` a finite Borel measure with `μ ⟂ λ` for every `λ ∈ F`. Then there is a Borel `E` with
`μ(X ∖ E) = 0` and `λ(E) = 0` for all `λ ∈ F`. Convexity is for the measure combinations
`a • λ₁ + b • λ₂` with `a + b = 1` in `ℝ≥0`. -/
theorem rainwater_lemma (F : Set (ProbabilityMeasure X)) (hF : IsCompact F)
    (hconv : Convex ℝ≥0 ((fun l : ProbabilityMeasure X => (l : Measure X)) '' F))
    (μ : Measure X) [IsFiniteMeasure μ] (hsing : ∀ l ∈ F, μ ⟂ₘ (l : Measure X)) :
    ∃ E : Set X, MeasurableSet E ∧ μ Eᶜ = 0 ∧ ∀ l ∈ F, (l : Measure X) E = 0 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · exact ⟨univ, MeasurableSet.univ, by simp, by simp⟩
  have hex : ∀ n : ℕ, ∃ g : X →ᵇ ℝ, IsUnitFn g ∧ ∀ l ∈ F, rainCost μ g l < (1 / 4 : ℝ) ^ n := by
    intro n
    have hδ : (0 : ℝ) < (1 / 4) ^ n := by positivity
    obtain ⟨t, ht, htc⟩ := rainwater_finite_subcover μ F hF hsing hδ
    exact rainwater_convex_combination μ F hF hconv hδ t ht htc
  choose g hg hgc using hex
  refine rainwater_borel_cantelli μ F g hg (fun n => ?_) (fun l hl n => ?_)
  · have h := hgc n l₀ hl₀
    have h2 : 0 ≤ ∫ x, (1 - g n x) ∂(l₀ : Measure X) :=
      integral_nonneg fun x => sub_nonneg.2 (hg n x).2
    unfold rainCost at h
    linarith
  · have h := hgc n l hl
    have h2 : 0 ≤ ∫ x, g n x ∂μ := integral_nonneg fun x => (hg n x).1
    unfold rainCost at h
    linarith

end AFree
