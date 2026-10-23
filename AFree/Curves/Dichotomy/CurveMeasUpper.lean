module

public import AFree.Curves.Dichotomy.CurveMeasConcat
public import AFree.Curves.Dichotomy.CurveMeasLower

/-!
# `𝓗¹(U ∩ γ[0,1]) ≤ Λ_γ(U)` and the length formula
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The sum of the variations of the grid cells mapped into `U` is dominated by `Λ_γ(U)`. -/
lemma grid_variation_le (γ : C(I, Vec d)) (U : Set (Vec d)) (M : ℕ) (hM : 0 < M) (m : ℕ) :
    ∑ j ∈ Finset.range m, (open scoped Classical in
      if ccurveExt γ '' Icc ((j : ℝ) / M) (((j : ℝ) + 1) / M) ⊆ U then
        euclideanCurveVariation (ccurveExt γ) (Icc ((j : ℝ) / M) (((j : ℝ) + 1) / M)) else 0) ≤
      curveLambda γ U (Icc 0 ((m : ℝ) / M)) := by
  classical
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hmono : curveLambda γ U (Icc 0 ((m : ℝ) / M)) ≤
        curveLambda γ U (Icc 0 (((m + 1 : ℕ) : ℝ) / M)) :=
      curveLambda_mono_set γ U (Icc_subset_Icc le_rfl (by
        push_cast; gcongr; linarith))
    split_ifs with h
    · refine le_trans ?_ (curveLambda_add_variation_le γ U (by positivity) ?_ h |>.trans
        (by push_cast; exact le_rfl))
      · exact add_le_add ih le_rfl
      · gcongr; linarith
    · rw [add_zero]; exact ih.trans hmono

lemma exists_cell {M : ℕ} (hM : 0 < M) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ j < M, x ∈ Icc ((j : ℝ) / M) (((j : ℝ) + 1) / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases h : ⌊x * M⌋₊ < M
  · refine ⟨⌊x * M⌋₊, h, ?_⟩
    have h1 := Nat.floor_le (mul_nonneg hx.1 hM'.le)
    have h2 := Nat.lt_floor_add_one (x * M)
    constructor
    · rw [div_le_iff₀ hM']; exact h1
    · rw [le_div_iff₀ hM']; exact h2.le
  · refine ⟨M - 1, by omega, ?_⟩
    have h1 : (M : ℝ) ≤ x * M := by
      have := (Nat.le_floor_iff (mul_nonneg hx.1 hM'.le)).1 (not_lt.1 h)
      exact this
    have hx1 : x = 1 := le_antisymm hx.2 (by nlinarith)
    subst hx1
    have : ((M - 1 : ℕ) : ℝ) + 1 = M := by
      rw [Nat.cast_sub hM]; simp
    rw [this, div_self hM'.ne']
    refine ⟨?_, le_rfl⟩
    rw [div_le_one hM']
    rw [Nat.cast_sub hM]; simp

/-- The image of a compact subset of `γ⁻¹(U)` has `𝓗¹` at most `Λ_γ(U)`. -/
lemma hausdorffOne_image_compact_le {e : Vec d} {α : ℝ} {γ : C(I, Vec d)}
    (hγ : γ ∈ ccurveSpace e α) {U : Set (Vec d)} (hU : IsOpen U) {F : Set I}
    (hF : IsCompact F) (hFU : γ '' F ⊆ U) :
    euclideanHausdorffOne d (γ '' F) ≤ curveLambda γ U (Icc 0 1) := by
  classical
  have hlip := lipschitzWith_ccurveExt hγ
  have hcont : Continuous (ccurveExt γ) := hlip.continuous
  obtain ⟨r, hr, hrU⟩ := (hF.image γ.continuous).exists_cthickening_subset_open hU hFU
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
  set M := N + 1 with hMdef
  have hM : 0 < M := Nat.succ_pos N
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hMr : 1 / (M : ℝ) ≤ r := by simpa [hMdef] using hN.le
  set cell : ℕ → Set ℝ := fun j => Icc ((j : ℝ) / M) (((j : ℝ) + 1) / M) with hcell
  set P : ℕ → Prop := fun j => ccurveExt γ '' cell j ⊆ U with hP
  have hPj : ∀ j, (∃ s ∈ F, (s : ℝ) ∈ cell j) → P j := by
    rintro j ⟨s, hs, hsj⟩ _ ⟨t, ht, rfl⟩
    apply hrU
    refine Metric.mem_cthickening_of_dist_le (ccurveExt γ t) (γ s) r (γ '' F) ⟨s, hs, rfl⟩ ?_
    have h1 : dist (ccurveExt γ t) (ccurveExt γ s) ≤ |t - s| := by
      have := hlip.dist_le_mul t s
      simpa [Real.dist_eq] using this
    rw [ccurveExt_coe] at h1
    refine h1.trans (le_trans ?_ hMr)
    rw [abs_le]
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨hs1, hs2⟩ := hsj
    have : ((j : ℝ) + 1) / M - j / M = 1 / M := by field_simp; ring
    constructor <;> linarith
  have hcover : γ '' F ⊆ ⋃ j ∈ (Finset.range M).filter P, ccurveExt γ '' cell j := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨j, hj, hsj⟩ := exists_cell hM s.2
    simp only [mem_iUnion]
    refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hPj j ⟨s, hs, hsj⟩⟩, s, hsj, ?_⟩
    exact ccurveExt_coe γ s
  calc euclideanHausdorffOne d (γ '' F)
      ≤ euclideanHausdorffOne d (⋃ j ∈ (Finset.range M).filter P, ccurveExt γ '' cell j) :=
        measure_mono hcover
    _ ≤ ∑ j ∈ (Finset.range M).filter P, euclideanHausdorffOne d (ccurveExt γ '' cell j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ (Finset.range M).filter P, euclideanCurveVariation (ccurveExt γ) (cell j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine hausdorffOne_le_euclideanCurveVariation ?_ hcont.continuousOn
        have : ((j : ℝ) + 1) / M - j / M = 1 / M := by field_simp; ring
        have : (0 : ℝ) < 1 / M := by positivity
        linarith
    _ = ∑ j ∈ Finset.range M, (if P j then
          euclideanCurveVariation (ccurveExt γ) (cell j) else 0) := (Finset.sum_filter _ _)
    _ ≤ curveLambda γ U (Icc 0 ((M : ℝ) / M)) := grid_variation_le γ U M hM M
    _ = curveLambda γ U (Icc 0 1) := by rw [div_self hM'.ne']

/-- (`≤` half) For `γ ∈ 𝒢(C)` and `U` open,
`𝓗¹(U ∩ γ([0,1])) ≤ Λ_γ(U)`. -/
theorem hausdorffOne_inter_range_le {e : Vec d} {α : ℝ}
    {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α) {U : Set (Vec d)} (hU : IsOpen U) :
    euclideanHausdorffOne d (U ∩ range γ) ≤ curveLambda γ U (Icc 0 1) := by
  obtain ⟨F, hFc, hFU, hFeq, hFm⟩ := (hU.preimage γ.continuous).exists_iUnion_isClosed
  have : U ∩ range γ = ⋃ n, γ '' F n := by
    rw [← image_iUnion, hFeq]
    exact (image_preimage_eq_inter_range).symm
  have hmono : Monotone fun n => γ '' F n := fun a b h => image_mono (hFm h)
  rw [this, hmono.measure_iUnion]
  exact iSup_le fun n => hausdorffOne_image_compact_le hγ hU (hFc n).isCompact
    (image_subset_iff.2 (hFU n))

end AFree
