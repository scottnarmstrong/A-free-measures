module

public import AFree.Curves.HausdorffPre
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# `𝓗¹` and the Euclidean variation of a curve

Mathlib's `eVariationOn` on `Vec d` uses the
sup metric, so the variation is taken with the Euclidean norm; the comparison with Mathlib's
`eVariationOn` is made privately through `PiLp 2`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- The variation `Var(γ; s) = sup ∑ᵢ |γ(sᵢ) - γ(sᵢ₋₁)|` over monotone finite sequences in `s`,
with the *Euclidean* norm (same shape as Mathlib's `eVariationOn`). -/
noncomputable def euclideanCurveVariation (γ : ℝ → Vec d) (s : Set ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, ENNReal.ofReal (vecEuclideanNorm (γ (p.2.1 (i + 1)) - γ (p.2.1 i)))

private lemma edist_toLp_eq (x y : Vec d) :
    edist (WithLp.toLp 2 x : PiLp 2 (fun _ : Fin d => ℝ)) (WithLp.toLp 2 y) =
      ENNReal.ofReal (vecEuclideanNorm (x - y)) := by
  rw [edist_dist, PiLp.dist_eq_of_L2]
  congr 1
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.dist_eq, sq]

private lemma euclideanCurveVariation_eq (γ : ℝ → Vec d) (s : Set ℝ) :
    euclideanCurveVariation γ s =
      eVariationOn (fun t => (WithLp.toLp 2 (γ t) : PiLp 2 (fun _ : Fin d => ℝ))) s := by
  unfold euclideanCurveVariation eVariationOn
  refine iSup_congr fun p => Finset.sum_congr rfl fun i _ => ?_
  rw [edist_toLp_eq]

private lemma euclideanDiam_Icc_le (γ : ℝ → Vec d) {p q : ℝ} :
    euclideanDiam (γ '' Icc p q) ≤ eVariationOn (fun t => (WithLp.toLp 2 (γ t) :
      PiLp 2 (fun _ : Fin d => ℝ))) (univ ∩ Icc p q) := by
  rw [euclideanDiam_le_iff]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← edist_toLp_eq]
  exact eVariationOn.edist_le (fun t => (WithLp.toLp 2 (γ t) : PiLp 2 (fun _ : Fin d => ℝ)))
    (s := univ ∩ Icc p q) ⟨mem_univ _, hx⟩ ⟨mem_univ _, hy⟩

private lemma sum_variation_grid (F : ℝ → PiLp 2 (fun _ : Fin d => ℝ)) {a h : ℝ} (hh : 0 ≤ h)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, eVariationOn F (univ ∩ Icc (a + k * h) (a + (k + 1) * h)) =
      eVariationOn F (univ ∩ Icc a (a + N * h)) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
    exact (eVariationOn.subsingleton F (by simp)).symm
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : a ≤ a + N * h := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have h2 : a + N * h ≤ a + ((N : ℝ) + 1) * h := by nlinarith
    rw [eVariationOn.Icc_add_Icc F (s := univ) h1 h2 (mem_univ _)]
    push_cast; rfl

private lemma grid_cover {a h t : ℝ} {N : ℕ} (hN : 0 < N)
    (ht : t ∈ Icc a (a + N * h)) : ∃ k < N, t ∈ Icc (a + k * h) (a + (k + 1) * h) := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨0, by omega, by simpa using ht⟩
  | succ N hN ih =>
    by_cases hle : t ≤ a + N * h
    · obtain ⟨k, hk, hk'⟩ := ih ⟨ht.1, hle⟩
      exact ⟨k, by omega, hk'⟩
    · refine ⟨N, by omega, (not_le.mp hle).le, ?_⟩
      have := ht.2; push_cast at this; linarith

/-- For `γ` continuous on `[a, b]`,
`𝓗¹(γ([a, b])) ≤ Var(γ; [a, b])` with the Euclidean variation. -/
theorem hausdorffOne_le_euclideanCurveVariation {γ : ℝ → Vec d} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) :
    euclideanHausdorffOne d (γ '' Icc a b) ≤ euclideanCurveVariation γ (Icc a b) := by
  set F : ℝ → PiLp 2 (fun _ : Fin d => ℝ) := fun t => WithLp.toLp 2 (γ t) with hF
  rw [euclideanCurveVariation_eq, (euclideanHausdorffOne_eq_iSup_pre _).1]
  refine iSup_le fun n => ?_
  have hunif := isCompact_Icc.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ, hδ'⟩ := hunif (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by have := sub_nonneg.mpr hab; positivity) hN
    exact_mod_cast this
  set h : ℝ := (b - a) / N with hh
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N)
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ (by exact_mod_cast hN0)]
    rwa [div_lt_iff₀ hδ, mul_comm] at hN
  have hNh : a + N * h = b := by rw [hh]; field_simp; ring
  have hsub : ∀ k, k < N → Icc (a + k * h) (a + (k + 1) * h) ⊆ Icc a b := by
    intro k hk x hx
    have : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  let U : ℕ → Set (Vec d) := fun k => if k < N then γ '' Icc (a + k * h) (a + (k + 1) * h) else ∅
  have hcov : γ '' Icc a b ⊆ ⋃ k, U k := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨k, hk, hk'⟩ := grid_cover hN0 (by rwa [hNh] : t ∈ Icc a (a + N * h))
    exact mem_iUnion.mpr ⟨k, by simp only [U, hk, ↓reduceIte]; exact ⟨t, hk', rfl⟩⟩
  have hdiam : ∀ k, Metric.ediam (U k) ≤ (n : ℝ≥0∞)⁻¹ := by
    intro k
    by_cases hk : k < N
    · simp only [U, hk, ↓reduceIte]
      refine Metric.ediam_le ?_
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hxy : dist x y < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
      have := hδ' x (hsub k hk hx) y (hsub k hk hy) hxy
      have hη : ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ (n : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
        apply ENNReal.inv_le_inv.2
        rw [show ENNReal.ofReal ((n : ℝ) + 1) = (n : ℝ≥0∞) + 1 by simp [ENNReal.ofReal_add]]
        exact le_self_add
      rw [edist_dist]
      exact (ENNReal.ofReal_le_ofReal this.le).trans hη
    · simp [U, hk]
  refine ((euclideanHausdorffOne_eq_iSup_pre _).2.1 _ U hcov hdiam).trans ?_
  have hzero : ∀ k ∉ Finset.range N, euclideanDiam (U k) = 0 := by
    intro k hk
    have : ¬ k < N := by simpa using hk
    simp [U, this, euclideanDiam]
  rw [tsum_eq_sum hzero]
  calc ∑ k ∈ Finset.range N, euclideanDiam (U k)
      ≤ ∑ k ∈ Finset.range N, eVariationOn F (univ ∩ Icc (a + k * h) (a + (k + 1) * h)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k < N := Finset.mem_range.mp hk
        simp only [U, hk', ↓reduceIte]
        exact euclideanDiam_Icc_le γ
    _ = eVariationOn F (univ ∩ Icc a (a + N * h)) := sum_variation_grid F hh0 N
    _ = eVariationOn F (Icc a b) := by rw [hNh, univ_inter]

end AFree
