module

public import AFree.TopCurrents.CurrentNull
public import AFree.Curves.Exhaust

/-!
# [DPR, Theorem 1.15]: mass measures of metric `d`-currents are `≪ 𝓛^d`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu

private lemma vecDot_single_single {d : ℕ} (i j : Fin d) :
    vecDot (Pi.single i (1 : ℝ) : Vec d) (Pi.single j (1 : ℝ)) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [vecDot, Pi.single_apply]
  · simp [vecDot, Pi.single_apply, h, Ne.symm h]

private lemma volume_null_dim_zero (μ : Measure (Vec 0)) :
    μ ≪ volume := by
  intro s hs
  have : s = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hu : s = Set.univ := Set.eq_univ_of_forall fun y => by
      rwa [Subsingleton.elim y x]
    rw [hu] at hs
    have h1 : (volume : Measure (Vec 0)) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_univ]; simp
    rw [h1] at hs
    exact one_ne_zero hs
  simp [this]

/-- [DPR, Theorem 1.15] If `T ∈ M_d(ℝ^d)` and `μ` is its mass measure, `μ ≪ 𝓛^d`. -/
theorem curr_ac {d : ℕ} {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent d T) {μ : Measure (Vec d)} (hμ : IsAKMass T μ) : μ ≪ volume := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact volume_null_dim_zero μ
  obtain ⟨ν, hν, -, -, -, -, hmass⟩ := nu_main hT
  have hμν : μ = ν.totalVariation := hmass μ hμ
  obtain ⟨αd, hαd, hcn⟩ := conenull_ac hd
  have hfin : IsFiniteMeasure μ := by rw [hμν]; infer_instance
  refine hcn μ (fun i => Pi.single i 1) vecDot_single_single (min αd (Real.pi / 4))
    (lt_min hαd (by positivity)) (min_le_left _ _) fun i K hK hnull => ?_
  have he : vecEuclideanNorm (Pi.single i (1 : ℝ) : Vec d) = 1 := by
    have := vecDot_single_single i i
    simp only [ite_true] at this
    simp [vecEuclideanNorm, vecNormSq, this]
  have hα2 : min αd (Real.pi / 4) < Real.pi / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  rw [hμν]
  exact currentnull hT hν he (lt_min hαd (by positivity)) hα2 hK.measurableSet hnull

end AFree
