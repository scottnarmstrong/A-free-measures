module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Rat

/-!
# Uniform differentiability on a large compact set

For a Lipschitz `f : ℝ → E` and
`ε > 0` there is a compact `S ⊆ [a, b]` of almost full measure on which `f` is differentiable
and the Whitney condition holds uniformly. The argument is Egorov's theorem, applied to the Borel sets
`T_{n,k} = {s : the quotient error at rational q within 1/(n+1) of s is ≤ |q - s| / (k+1)}`:
they increase in `n` and exhaust the differentiability points, so continuity from above gives `n_k`
with `T_{n_k,k}` of almost full measure for each `k`, and `S` is a compact subset of their
intersection.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace AFree

namespace Lusin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quotient error of `f` at `s` against the slope `deriv f s` at the point `x`. -/
noncomputable def quotErr (f : ℝ → E) (s x : ℝ) : ℝ := ‖f x - f s - (x - s) • deriv f s‖

/-- `T_{n,k}`: the quotient error at every rational `q` with `|q - s| < 1/(n+1)` is at most
`|q - s| / (k+1)`. -/
def tSet (f : ℝ → E) (n k : ℕ) : Set ℝ :=
  {s | ∀ q : ℚ, |(q : ℝ) - s| < 1 / ((n : ℝ) + 1) →
    quotErr f s q ≤ 1 / ((k : ℝ) + 1) * |(q : ℝ) - s|}

lemma continuous_quotErr {f : ℝ → E} (hf : Continuous f) (s : ℝ) : Continuous (quotErr f s) := by
  unfold quotErr
  fun_prop

section Meas

variable [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_quotErr_snd {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    Measurable fun s => quotErr f s x := by
  unfold quotErr
  exact ((measurable_const.sub hf.measurable).sub
    ((measurable_const.sub measurable_id).smul (measurable_deriv f))).norm

lemma measurableSet_tSet {f : ℝ → E} (hf : Continuous f) (n k : ℕ) : MeasurableSet (tSet f n k) := by
  have : tSet f n k = ⋂ q : ℚ, {s | |(q : ℝ) - s| < 1 / ((n : ℝ) + 1)}ᶜ ∪
      {s | quotErr f s q ≤ 1 / ((k : ℝ) + 1) * |(q : ℝ) - s|} := by
    ext s
    simp only [tSet, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [this]
  refine MeasurableSet.iInter fun q => ?_
  refine MeasurableSet.union (measurableSet_lt (by fun_prop) measurable_const).compl ?_
  exact measurableSet_le (measurable_quotErr_snd hf q) (by fun_prop)

end Meas

lemma tSet_mono (f : ℝ → E) (k : ℕ) : Monotone fun n => tSet f n k := by
  intro n n' h s hs q hq
  refine hs q (hq.trans_le ?_)
  gcongr

/-- A differentiability point lies in `T_{n,k}` for `n` large. -/
lemma exists_mem_tSet {f : ℝ → E} {s : ℝ} (hs : DifferentiableAt ℝ f s) (k : ℕ) :
    ∃ n, s ∈ tSet f n k := by
  have h := hs.hasDerivAt.isLittleO.def (c := 1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 h
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, fun q hq => ?_⟩
  have := hδ' (y := (q : ℝ)) (by rw [Real.dist_eq]; exact hq.trans hn)
  simpa [quotErr, Real.norm_eq_abs] using this

/-- Real points instead of rational ones, by density. -/
lemma tSet_real {f : ℝ → E} (hf : Continuous f) {n k : ℕ} {s : ℝ} (hs : s ∈ tSet f n k) {x : ℝ}
    (hx : |x - s| < 1 / ((n : ℝ) + 1)) :
    quotErr f s x ≤ 1 / ((k : ℝ) + 1) * |x - s| := by
  set U : Set ℝ := {x | |x - s| < 1 / ((n : ℝ) + 1)} with hU
  have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hcl : IsClosed {x : ℝ | quotErr f s x ≤ 1 / ((k : ℝ) + 1) * |x - s|} :=
    isClosed_le (continuous_quotErr hf s) (by fun_prop)
  have hsub : U ∩ range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | quotErr f s x ≤ 1 / ((k : ℝ) + 1) * |x - s|} := by
    rintro _ ⟨hq, q, rfl⟩
    exact hs q hq
  have := (Rat.denseRange_cast.open_subset_closure_inter hUo).trans (closure_minimal hsub hcl)
  exact this hx

section Main

variable [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E]
  [BorelSpace E]

/-- For each `k` some `T_{n,k}` has almost full measure in `[a, b]` (continuity from above). -/
lemma exists_tSet_small {f : ℝ → E} {L : ℝ≥0} (hf : LipschitzWith L f) (a b : ℝ) (k : ℕ)
    {c : ℝ≥0∞} (hc : 0 < c) : ∃ n, volume (Icc a b \ tSet f n k) < c := by
  have hcont := hf.continuous
  have hae : ∀ᵐ s, DifferentiableAt ℝ f s := hf.ae_differentiableAt_real
  set A : ℕ → Set ℝ := fun n => Icc a b \ tSet f n k with hA
  have hmono : Antitone A := fun n n' h x hx => ⟨hx.1, fun hh => hx.2 (tSet_mono f k h hh)⟩
  have hnm : ∀ n, NullMeasurableSet (A n) volume := fun n =>
    (measurableSet_Icc.diff (measurableSet_tSet hcont n k)).nullMeasurableSet
  have hfin : ∃ n, volume (A n) ≠ ∞ := ⟨0, ne_top_of_le_ne_top (by simp) (measure_mono sdiff_subset)⟩
  have ht := tendsto_measure_iInter_atTop hnm hmono hfin
  have h0 : volume (⋂ n, A n) = 0 := by
    refine measure_mono_null (t := {s | ¬ DifferentiableAt ℝ f s}) (fun x hx => ?_) (ae_iff.1 hae)
    intro hd
    obtain ⟨n, hn⟩ := exists_mem_tSet hd k
    exact (mem_iInter.1 hx n).2 hn
  rw [h0] at ht
  exact (ht.eventually (eventually_lt_nhds hc)).exists

/-- A Lipschitz `f : ℝ → E` is, on a compact `S ⊆ [a, b]` with
`𝓛¹([a,b] \ S) < ε`, differentiable and uniformly differentiable in the sense of Whitney:
`‖f s' - f s - (s' - s) f'(s)‖ ≤ η |s' - s|` for `s, s' ∈ S`, `|s' - s| < δ(η)`. -/
theorem egorov_whitney {f : ℝ → E} {L : ℝ≥0} (hf : LipschitzWith L f) (a b : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : Set ℝ, IsCompact S ∧ S ⊆ Icc a b ∧ volume (Icc a b \ S) < ENNReal.ofReal ε ∧
      (∀ s ∈ S, DifferentiableAt ℝ f s) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S, |s' - s| < δ →
        ‖f s' - f s - (s' - s) • deriv f s‖ ≤ η * |s' - s| := by
  have hcont := hf.continuous
  have hεpos : ENNReal.ofReal ε / 2 ≠ 0 := by simp [hε]
  obtain ⟨ε', hε'pos, hsum⟩ := ENNReal.exists_pos_sum_of_countable hεpos ℕ
  have key : ∀ k : ℕ, ∃ n, volume (Icc a b \ tSet f n k) < ε' k := fun k =>
    exists_tSet_small hf a b k (by exact_mod_cast hε'pos k)
  choose n hn using key
  set T : Set ℝ := Icc a b ∩ ⋂ k, tSet f (n k) k with hT
  have hTm : MeasurableSet T :=
    measurableSet_Icc.inter (MeasurableSet.iInter fun k => measurableSet_tSet hcont _ k)
  have hTfin : volume T ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (inter_subset_left : T ⊆ Icc a b))
  have hsmall : volume (Icc a b \ T) < ENNReal.ofReal ε / 2 := by
    have hsub : Icc a b \ T ⊆ ⋃ k, Icc a b \ tSet f (n k) k := by
      intro x hx
      have : ¬ ∀ k, x ∈ tSet f (n k) k := fun h => hx.2 ⟨hx.1, mem_iInter.2 h⟩
      push Not at this
      obtain ⟨k, hk⟩ := this
      exact mem_iUnion.2 ⟨k, hx.1, hk⟩
    calc volume (Icc a b \ T) ≤ volume (⋃ k, Icc a b \ tSet f (n k) k) := measure_mono hsub
      _ ≤ ∑' k, volume (Icc a b \ tSet f (n k) k) := measure_iUnion_le _
      _ ≤ ∑' k, (ε' k : ℝ≥0∞) := ENNReal.tsum_le_tsum fun k => (hn k).le
      _ < _ := hsum
  obtain ⟨S, hST, hSc, hSlt⟩ := hTm.exists_isCompact_sdiff_lt hTfin hεpos
  have hSbound : ∀ s ∈ S, ∀ k : ℕ, ∀ x : ℝ, |x - s| < 1 / ((n k : ℝ) + 1) →
      ‖f x - f s - (x - s) • deriv f s‖ ≤ 1 / ((k : ℝ) + 1) * |x - s| := fun s hs k x hx =>
    tSet_real hcont (mem_iInter.1 (hST hs).2 k) hx
  refine ⟨S, hSc, fun s hs => (hST hs).1, ?_, fun s hs => ?_, fun η hη => ?_⟩
  · calc volume (Icc a b \ S) ≤ volume (Icc a b \ T) + volume (T \ S) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro x hx
          by_cases hxT : x ∈ T
          · exact Or.inr ⟨hxT, hx.2⟩
          · exact Or.inl ⟨hx.1, hxT⟩
      _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 := ENNReal.add_lt_add hsmall hSlt
      _ = ENNReal.ofReal ε := ENNReal.add_halves _
  · refine (hasDerivAt_iff_isLittleO (f' := deriv f s)).2 ?_ |>.differentiableAt
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hc
    have hδ : (0 : ℝ) < 1 / ((n k : ℝ) + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds s hδ] with x hx
    have := hSbound s hs k x (by simpa [Real.dist_eq] using hx)
    simp only [Real.norm_eq_abs] at this ⊢
    calc _ ≤ _ := this
      _ ≤ c * |x - s| := by gcongr
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
    refine ⟨1 / ((n k : ℝ) + 1), by positivity, fun s hs s' hs' h => ?_⟩
    have := hSbound s hs k s' h
    calc _ ≤ _ := this
      _ ≤ η * |s' - s| := by gcongr

end Main

end Lusin

end AFree
