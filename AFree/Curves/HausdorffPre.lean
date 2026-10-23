module

public import AFree.Curves.Vec
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# `𝓗¹` as a limit of `r`-premeasures

Comparison of sup and Euclidean diameters, and `𝓗¹` as the supremum of the `r`-premeasures.
`euclideanHausdorffOne d = Measure.mkMetric' euclideanDiam`, where the smallness constraint of
`OuterMeasure.mkMetric'.pre` is the sup-metric diameter `Metric.ediam`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- Sup versus Euclidean diameter: `ediam s ≤ euclideanDiam s ≤ √d · ediam s`. -/
theorem ediam_le_euclideanDiam_le (s : Set (Vec d)) :
    Metric.ediam s ≤ euclideanDiam s ∧
      euclideanDiam s ≤ ENNReal.ofReal (Real.sqrt d) * Metric.ediam s := by
  constructor
  · refine Metric.ediam_le fun x hx y hy => ?_
    rw [edist_dist, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (norm_le_vecEuclideanNorm (x - y))) ?_
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
  · unfold euclideanDiam
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    calc ENNReal.ofReal (vecEuclideanNorm (x - y))
        ≤ ENNReal.ofReal (Real.sqrt d * ‖x - y‖) :=
          ENNReal.ofReal_le_ofReal (vecEuclideanNorm_le_sqrt_natCast_mul_norm _)
      _ = ENNReal.ofReal (Real.sqrt d) * edist x y := by
          rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), edist_dist, dist_eq_norm]
      _ ≤ _ := mul_le_mul_right (Metric.edist_le_ediam_of_mem hx hy) _

lemma euclideanDiam_le_iff {s : Set (Vec d)} {r : ℝ≥0∞} :
    euclideanDiam s ≤ r ↔ ∀ x ∈ s, ∀ y ∈ s, ENNReal.ofReal (vecEuclideanNorm (x - y)) ≤ r := by
  unfold euclideanDiam
  simp only [iSup_le_iff]

lemma euclideanDiam_closure (s : Set (Vec d)) : euclideanDiam (closure s) = euclideanDiam s := by
  refine le_antisymm ?_ (by unfold euclideanDiam; exact iSup₂_mono' fun x hx =>
    ⟨x, subset_closure hx, iSup₂_mono' fun y hy => ⟨y, subset_closure hy, le_rfl⟩⟩)
  rw [euclideanDiam_le_iff]
  intro x hx y hy
  have hcl : IsClosed {p : Vec d × Vec d |
      ENNReal.ofReal (vecEuclideanNorm (p.1 - p.2)) ≤ euclideanDiam s} :=
    isClosed_le (ENNReal.continuous_ofReal.comp
      (continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_snd))) continuous_const
  have hsub : s ×ˢ s ⊆ {p : Vec d × Vec d |
      ENNReal.ofReal (vecEuclideanNorm (p.1 - p.2)) ≤ euclideanDiam s} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact (euclideanDiam_le_iff (r := euclideanDiam s)).mp le_rfl a ha b hb
  have := closure_minimal hsub hcl (by rw [closure_prod_eq]; exact ⟨hx, hy⟩ :
    (x, y) ∈ closure (s ×ˢ s))
  exact this

/-- Upper bounds: covers by sets of sup-diameter `≤ r` bound the
`r`-premeasure. -/
lemma pre_euclideanDiam_le_tsum {S : Set (Vec d)} {r : ℝ≥0∞} {U : ℕ → Set (Vec d)}
    (hS : S ⊆ ⋃ k, U k) (hU : ∀ k, Metric.ediam (U k) ≤ r) :
    OuterMeasure.mkMetric'.pre euclideanDiam r S ≤ ∑' k, euclideanDiam (U k) :=
  calc _ ≤ OuterMeasure.mkMetric'.pre euclideanDiam r (⋃ k, U k) := measure_mono hS
    _ ≤ ∑' k, OuterMeasure.mkMetric'.pre euclideanDiam r (U k) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum fun k => OuterMeasure.mkMetric'.pre_le (hU k)

/-- Lower bounds: a near-optimal cover with small sup-diameters. -/
lemma exists_cover_of_pre_lt {S : Set (Vec d)} {r : ℝ≥0∞} {c : ℝ≥0∞}
    (h : OuterMeasure.mkMetric'.pre euclideanDiam r S < c) :
    ∃ U : ℕ → Set (Vec d), S ⊆ ⋃ k, U k ∧ (∀ k, Metric.ediam (U k) ≤ r) ∧
      ∑' k, euclideanDiam (U k) < c := by
  unfold OuterMeasure.mkMetric'.pre at h
  rw [OuterMeasure.boundedBy_apply, iInf_lt_iff] at h
  obtain ⟨t, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨hSt, h⟩ := h
  have hterm : ∀ n, (⨆ (_ : (t n).Nonempty),
      extend (fun s (_ : Metric.ediam s ≤ r) => euclideanDiam s) (t n)) < ⊤ := fun n =>
    lt_of_le_of_lt (ENNReal.le_tsum (f := fun n => ⨆ (_ : (t n).Nonempty),
      extend (fun s (_ : Metric.ediam s ≤ r) => euclideanDiam s) (t n)) n)
      (lt_of_lt_of_le h le_top)
  have hdiam : ∀ n, Metric.ediam (t n) ≤ r := by
    intro n
    by_contra hn
    have hne : (t n).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty.mp hne] at hn
      simp at hn
    have := hterm n
    simp only [iSup_pos hne, extend, iInf_neg hn] at this
    simp at this
  refine ⟨t, hSt, hdiam, lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => ?_) h⟩
  by_cases hne : (t n).Nonempty
  · simp [hne, extend, hdiam n]
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp [euclideanDiam]

/-- For every set `S` (measurable or not), `𝓗¹(S) = sup_n pre (1/n) S`, where
`pre r = OuterMeasure.mkMetric'.pre euclideanDiam r`. Consequently (1) covers by sets of
sup-diameter `≤ r` bound `pre r S` by `∑ euclideanDiam (U k)`, and (2) if `𝓗¹(S) < ⊤`, then for
`r, ε > 0` there is a cover with sup-diameters `≤ r` and `∑ euclideanDiam (U k) ≤ 𝓗¹(S) + ε`. -/
theorem euclideanHausdorffOne_eq_iSup_pre (S : Set (Vec d)) :
    euclideanHausdorffOne d S = ⨆ n : ℕ, OuterMeasure.mkMetric'.pre euclideanDiam (n : ℝ≥0∞)⁻¹ S ∧
    (∀ (r : ℝ≥0∞) (U : ℕ → Set (Vec d)), S ⊆ ⋃ k, U k → (∀ k, Metric.ediam (U k) ≤ r) →
      OuterMeasure.mkMetric'.pre euclideanDiam r S ≤ ∑' k, euclideanDiam (U k)) ∧
    (euclideanHausdorffOne d S < ⊤ → ∀ r : ℝ≥0∞, 0 < r → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : ℕ → Set (Vec d), S ⊆ ⋃ k, U k ∧ (∀ k, Metric.ediam (U k) ≤ r) ∧
        ∑' k, euclideanDiam (U k) ≤ euclideanHausdorffOne d S + ε) := by
  have hEq : euclideanHausdorffOne d S = ⨆ n : ℕ,
      OuterMeasure.mkMetric'.pre euclideanDiam (n : ℝ≥0∞)⁻¹ S := by
    have h1 : (euclideanHausdorffOne d) S = (OuterMeasure.mkMetric' (euclideanDiam (d := d))).trim S := by
      show (Measure.mkMetric' (euclideanDiam (d := d))).toOuterMeasure S = _
      rw [Measure.mkMetric'_toOuterMeasure]
    rw [h1, OuterMeasure.mkMetric'.eq_iSup_nat, OuterMeasure.trim_iSup]
    simp only [OuterMeasure.iSup_apply]
    refine iSup_congr fun n => ?_
    rw [OuterMeasure.mkMetric'.trim_pre _ euclideanDiam_closure]
  refine ⟨hEq, fun r U hS hU => pre_euclideanDiam_le_tsum hS hU, fun hfin r hr ε hε => ?_⟩
  have hpre : OuterMeasure.mkMetric'.pre euclideanDiam r S ≤ euclideanHausdorffOne d S := by
    have : OuterMeasure.mkMetric'.pre (euclideanDiam (d := d)) r ≤
        OuterMeasure.mkMetric' (euclideanDiam (d := d)) :=
      le_iSup₂_of_le r hr le_rfl
    refine (this S).trans ?_
    show _ ≤ (Measure.mkMetric' (euclideanDiam (d := d))).toOuterMeasure S
    rw [Measure.mkMetric'_toOuterMeasure]
    exact OuterMeasure.le_trim _ _
  obtain ⟨U, hS, hU, hsum⟩ := exists_cover_of_pre_lt
    (lt_of_le_of_lt hpre (ENNReal.lt_add_right hfin.ne hε.ne'))
  exact ⟨U, hS, hU, hsum.le⟩

end AFree
