module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Rainwater's lemma, steps 1 and 2

One singular measure is separated from `μ` by a function `f`; compactness then gives a finite subcover.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace AFree

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- `f` takes values in `[0, 1]`. -/
def IsUnitFn (f : X →ᵇ ℝ) : Prop := ∀ x, 0 ≤ f x ∧ f x ≤ 1

/-- The quantity `⟨μ, f⟩ + ⟨λ, 1 - f⟩` of Rainwater's proof. -/
noncomputable def rainCost (μ : Measure X) (f : X →ᵇ ℝ) (l : ProbabilityMeasure X) : ℝ :=
  ∫ x, f x ∂μ + ∫ x, (1 - f x) ∂(l : Measure X)

lemma continuous_rainCost [CompactSpace X] [BorelSpace X] (μ : Measure X) (f : X →ᵇ ℝ) :
    Continuous (rainCost μ f) := by
  unfold rainCost
  have h : Continuous fun l : ProbabilityMeasure X => ∫ x, (1 - f x) ∂(l : Measure X) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (1 - f)
  exact continuous_const.add h

lemma rainCost_nonneg (μ : Measure X) {f : X →ᵇ ℝ} (hf : IsUnitFn f) (l : ProbabilityMeasure X) :
    0 ≤ rainCost μ f l :=
  add_nonneg (integral_nonneg fun x => (hf x).1) (integral_nonneg fun x => sub_nonneg.2 (hf x).2)

/-- For a single probability measure `λ` singular to `μ` and `δ > 0`
there is `f` with values in `[0, 1]` and `⟨μ, f⟩ + ⟨λ, 1 - f⟩ < δ`. -/
theorem rainwater_one_measure [CompactSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (l : ProbabilityMeasure X)
    (hs : μ ⟂ₘ (l : Measure X)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : X →ᵇ ℝ, IsUnitFn f ∧ rainCost μ f l < δ := by
  obtain ⟨N, hN, hμN, hlN⟩ := hs
  have hNc : MeasurableSet Nᶜ := hN.compl
  have hε : (ENNReal.ofReal (δ / 2)) ≠ 0 := by simp [hδ]
  obtain ⟨K, hKN, hKc, hK⟩ := hNc.exists_isCompact_lt_add (measure_ne_top μ _) hε
  have hlK : (l : Measure X) K = 0 := measure_mono_null hKN hlN
  obtain ⟨U, hKU, hU, hlU⟩ := Set.exists_isOpen_lt_add K (measure_ne_top (l : Measure X) K) hε
  rw [hlK, zero_add] at hlU
  obtain ⟨g, hg0, hg1, hg01⟩ := exists_continuous_zero_one_of_isClosed hKc.isClosed hU.isClosed_compl
    (disjoint_compl_right_iff_subset.2 hKU)
  let f : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact g
  have hf : IsUnitFn f := fun x => ⟨(hg01 x).1, (hg01 x).2⟩
  refine ⟨f, hf, ?_⟩
  have hμK : μ Kᶜ < ENNReal.ofReal (δ / 2) := by
    have h1 : μ Kᶜ ≤ μ (Nᶜ \ K) + μ N := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hxN : x ∈ N
      · exact Or.inr hxN
      · exact Or.inl ⟨hxN, hx⟩
    rw [hμN, add_zero, measure_sdiff hKN hKc.nullMeasurableSet (measure_ne_top μ K)] at h1
    exact h1.trans_lt (ENNReal.sub_lt_of_lt_add (measure_mono hKN) (by rwa [add_comm] at hK))
  have hI1 : ∫ x, f x ∂μ ≤ μ.real Kᶜ := by
    rw [← integral_indicator_one hKc.measurableSet.compl]
    refine integral_mono (f.integrable μ) ((integrable_const (1 : ℝ)).indicator
      hKc.measurableSet.compl) fun x => ?_
    by_cases hx : x ∈ K
    · simp [indicator_of_notMem, hx, f, hg0 hx]
    · simp [hx, (hg01 x).2, f]
  have hI2 : ∫ x, (1 - f x) ∂(l : Measure X) ≤ (l : Measure X).real U := by
    rw [← integral_indicator_one hU.measurableSet]
    refine integral_mono ((1 - f).integrable _) ((integrable_const (1 : ℝ)).indicator
      hU.measurableSet) fun x => ?_
    by_cases hx : x ∈ U
    · simp [hx, (hg01 x).1, f]
    · have := hg1 (show x ∈ Uᶜ from hx)
      simp [hx, f, this]
  have h1 : μ.real Kᶜ < δ / 2 := ENNReal.toReal_lt_of_lt_ofReal hμK
  have h2 : (l : Measure X).real U < δ / 2 := ENNReal.toReal_lt_of_lt_ofReal hlU
  unfold rainCost
  linarith

/-- Fix `δ > 0`. The open sets
`O_f = {λ : ⟨μ, f⟩ + ⟨λ, 1 - f⟩ < δ}` cover the compact set `F`, so finitely many `f_i` suffice. -/
theorem rainwater_finite_subcover [CompactSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (F : Set (ProbabilityMeasure X)) (hF : IsCompact F)
    (hsing : ∀ l ∈ F, μ ⟂ₘ (l : Measure X)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset (X →ᵇ ℝ), (∀ f ∈ s, IsUnitFn f) ∧ ∀ l ∈ F, ∃ f ∈ s, rainCost μ f l < δ := by
  classical
  let O : {f : X →ᵇ ℝ // IsUnitFn f} → Set (ProbabilityMeasure X) :=
    fun i => {l | rainCost μ i.1 l < δ}
  have hO : ∀ i, IsOpen (O i) := fun i => isOpen_lt (continuous_rainCost μ i.1) continuous_const
  have hcov : F ⊆ ⋃ i, O i := by
    intro l hl
    obtain ⟨f, hf, hfl⟩ := rainwater_one_measure μ l (hsing l hl) hδ
    exact mem_iUnion.2 ⟨⟨f, hf⟩, hfl⟩
  obtain ⟨t, ht⟩ := hF.elim_finite_subcover O hO hcov
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hf
    exact i.2
  · intro l hl
    obtain ⟨i, hi⟩ := mem_iUnion₂.1 (ht hl)
    exact ⟨i.1, Finset.mem_image_of_mem _ hi.1, hi.2⟩

end AFree
