module

public import AFree.TopCurrents.CurrentNullCompact

/-!
# `|ν|` vanishes on Borel `C(e, α)`-null sets
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu AFree.MetricCurrents.LipApprox

/-- `ν(K) = 0` for compact `C(e, α)`-null `K`. -/
theorem currentnull_compact {d : ℕ} {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)} (hν : IsNuMeasure T ν) {e : Vec d}
    (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {K : Set (Vec d)} (hK : IsCompact K) (hnull : IsCNull (cone e α) K) : ν K = 0 := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp [vecEuclideanNorm, vecNormSq, vecDot] at he
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨R, hR, hRe⟩ := exists_orthRows he
  choose g hgsm hg01 hgD hgU hgW using fun k : ℕ =>
    perturb_of_cnull he hα hα2 hK hnull (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  have hgL : ∀ k, IsEuclLipschitzWith (Real.toNNReal (1 / Real.sin α)) (g k) := fun k =>
    perturb_isEuclLipschitz he hα hα2 (hgsm k) (hgD k) (hgW k)
  have hg0 : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 0) := by
    intro x
    refine squeeze_zero (fun k => (hg01 k x).1) (fun k => (hg01 k x).2) ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hdet : |R.det| = 1 := by
    rcases det_sq_of_orth R hR with h | h <;> simp [h]
  have hKm := hK.isClosed
  obtain ⟨hlip1, hz, -, -, -, hout, -, -⟩ := distCutoff_spec (C := K) hKm hne
    (t := 1) one_pos
  -- the bound for every cut-off
  have key : ∀ m : ℕ, |ν K| ≤ (ν.variation ({x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K)).toReal := by
    intro m
    have ht : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨-, -, hfL, hf01, hfK, hfout, -, -⟩ := distCutoff_spec (C := K) hKm hne ht
    have hVm : MeasurableSet {x | euclDist K x < 1 / ((m : ℝ) + 1)} :=
      measurableSet_lt (continuous_of_eucl hlip1).measurable measurable_const
    have hle : ∀ k, |ν K| ≤ (ν.variation ({x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K)).toReal +
        |T (distCutoff K (1 / ((m : ℝ) + 1))) (rowTuple R (g k))| := by
      intro k
      have h1 := currentnull_estimate ν hK (hgsm k) (hgD k) (hgU k) hfL (hf01) hfK hVm
        (fun x hx => by
          by_contra hc
          exact hx (hfout x (not_lt.1 hc)))
      rw [currentnull_perturbation_map hT hν hR hRe (hgsm k) (hgL k) hfL, abs_mul, hdet,
        one_mul]
      exact h1
    have hlim := currentnull_limit_map_vanishes hT hR hgL hg0 hfL
    have : Tendsto (fun k => (ν.variation ({x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K)).toReal +
        |T (distCutoff K (1 / ((m : ℝ) + 1))) (rowTuple R (g k))|) atTop
        (𝓝 ((ν.variation ({x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K)).toReal + |0|)) :=
      tendsto_const_nhds.add hlim.abs
    simpa using ge_of_tendsto' this hle
  -- the right-hand side tends to zero
  have hfin := finite_variation ν
  have hmeas : ∀ m : ℕ, MeasurableSet ({x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K) := fun m =>
    (measurableSet_lt (continuous_of_eucl hlip1).measurable measurable_const).diff hKm.measurableSet
  have hanti : Antitone fun m : ℕ => {x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K := by
    intro a b hab x hx
    have h1 : euclDist K x < 1 / ((b : ℝ) + 1) := hx.1
    refine ⟨lt_of_lt_of_le h1 ?_, hx.2⟩
    have : (a : ℝ) ≤ b := Nat.cast_le.2 hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hinter : (⋂ m : ℕ, {x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_forall]
    by_cases hx : x ∈ K
    · exact ⟨0, fun h => h.2 hx⟩
    · have h0 : euclDist K x ≠ 0 := fun h => hx ((hz x).1 h)
      have hpos : 0 < euclDist K x := lt_of_le_of_ne (euclDist_nonneg x) (Ne.symm h0)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact ⟨m, fun h => absurd h.1 (not_lt.2 hm.le)⟩
  have hT0 := tendsto_measure_iInter_atTop (μ := ν.variation)
    (fun m => (hmeas m).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hT0
  have hT1 : Tendsto (fun m : ℕ => (ν.variation ({x | euclDist K x < 1 / ((m : ℝ) + 1)} \ K)).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT0
    exact this.congr fun m => rfl
  have : |ν K| ≤ 0 := ge_of_tendsto' hT1 key
  exact abs_nonpos_iff.1 this

/-- Let `T ∈ M_d(ℝ^d)` and `ν` its density measure (`IsNuMeasure T ν`),
`e` a unit vector, `α ∈ (0, π/2)`. If `B` is a Borel `C(e, α)`-null set, then `|ν|(B) = 0`. -/
theorem currentnull {d : ℕ} {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)} (hν : IsNuMeasure T ν) {e : Vec d}
    (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {B : Set (Vec d)} (hB : MeasurableSet B) (hnull : IsCNull (cone e α) B) :
    ν.totalVariation B = 0 := by
  have hcomp : ∀ K, IsCompact K → K ⊆ B → ν K = 0 := fun K hK hKB =>
    currentnull_compact hT hν he hα hα2 hK (hnull.mono hKB)
  obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := ν.toJordanDecomposition_spec
  have hreal : ∀ E, MeasurableSet E →
      ν.totalVariation.real E = ν (i ∩ E) - ν (iᶜ ∩ E) := by
    intro E hE
    have h1 := SignedMeasure.toMeasureOfZeroLE_real_apply ν hi₂ hi₁ hE
    have h2 := SignedMeasure.toMeasureOfLEZero_real_apply ν hi₃ hi₁.compl hE
    rw [← hpos] at h1
    rw [← hneg] at h2
    rw [SignedMeasure.totalVariation, Measure.real, Measure.add_apply,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    simp only [Measure.real] at h1 h2
    rw [h1, h2]
    ring
  have hfin := finite_variation ν
  -- inner regularity reduction
  have hinner : ∀ A : Set (Vec d), MeasurableSet A → (∀ K, IsCompact K → K ⊆ A →
      ν.totalVariation K = 0) → ν.totalVariation A = 0 := by
    intro A hA hK0
    by_contra hne
    obtain ⟨K, hKA, hKc, hlt⟩ := hA.exists_isCompact_lt_add (μ := ν.totalVariation)
      (measure_ne_top _ _) hne
    rw [hK0 K hKc hKA, zero_add] at hlt
    exact lt_irrefl _ hlt
  have hz : ∀ K, ν.totalVariation.real K = 0 → ν.totalVariation K = 0 := by
    intro K h
    rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hpos0 : ν.totalVariation (B ∩ i) = 0 := by
    refine hinner _ (hB.inter hi₁) fun K hK hKA => hz K ?_
    have hKi : K ⊆ i := hKA.trans Set.inter_subset_right
    have hKB : K ⊆ B := hKA.trans Set.inter_subset_left
    have h1 : iᶜ ∩ K = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hx hxK => hx (hKi hxK)
    rw [hreal K hK.isClosed.measurableSet, Set.inter_eq_right.2 hKi, h1, hcomp K hK hKB]
    simp
  have hneg0 : ν.totalVariation (B ∩ iᶜ) = 0 := by
    refine hinner _ (hB.inter hi₁.compl) fun K hK hKA => hz K ?_
    have hKi : K ⊆ iᶜ := hKA.trans Set.inter_subset_right
    have hKB : K ⊆ B := hKA.trans Set.inter_subset_left
    have h1 : i ∩ K = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hx hxK => hKi hxK hx
    rw [hreal K hK.isClosed.measurableSet, Set.inter_eq_right.2 hKi, h1, hcomp K hK hKB]
    simp
  have := measure_inter_add_sdiff (μ := ν.totalVariation) B hi₁
  rw [hpos0, Set.sdiff_eq (s := B) (t := i), hneg0, zero_add] at this
  exact this.symm

end AFree
