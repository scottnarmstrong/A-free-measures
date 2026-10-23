module

public import AFree.MetricCurrents.AKTaylorSum

/-!
# Taylor lemma, Step 4: summation
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}
  {R : ℝ} {δ : ℝ≥0} {r : ℝ} {F : Finset (Fin k → ℤ)}

lemma sum_gridChi_eq (sd : ScaleData ψ R δ r F) {f : Vec d → ℝ} {x : Vec d}
    (hg : cutoffWeight π R f x ≠ 0) : ∑ J ∈ F, gridChi r J (evalTuple π x) = 1 := by
  have hθ : theta R (evalTuple π x) ≠ 0 := right_ne_zero_of_mul hg
  exact (grid_partition_of_unity (m := k) sd.r_pos).2.2.2.2.1 _ F fun J hJ =>
    (sd.mem J).2 ⟨_, (ne_zero_imp_norm_lt hθ).le, hJ⟩

lemma cutoffWeight_eq_sum (sd : ScaleData ψ R δ r F) (f : Vec d → ℝ)
    (x : Vec d) : cutoffWeight π R f x = ∑ J ∈ F, wJ π R f r J x := by
  by_cases hg : cutoffWeight π R f x = 0
  · simp [wJ, hg]
  · simp only [wJ, ← Finset.mul_sum, sum_gridChi_eq sd hg, mul_one]

lemma sum_abs_wJ_le (sd : ScaleData ψ R δ r F) (f : Vec d → ℝ)
    (x : Vec d) : ∑ J ∈ F, |wJ π R f r J x| ≤ |f x| := by
  have hG := (grid_partition_of_unity (m := k) sd.r_pos).2.1
  have habs : |cutoffWeight π R f x| ≤ |f x| := by
    unfold cutoffWeight
    rw [abs_mul, abs_of_nonneg (theta_nonneg _ _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (theta_le_one _ _)
  by_cases hg : cutoffWeight π R f x = 0
  · simp [wJ, hg]
  · have : ∀ J ∈ F, |wJ π R f r J x| = |cutoffWeight π R f x| * gridChi r J (evalTuple π x) := by
      intro J _
      simp only [wJ, abs_mul, abs_of_nonneg (hG J _).1]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_gridChi_eq sd hg, mul_one]
    exact habs

/-- Step 4. Summing the per-cube estimates (using linearity of `IsMetricCurrent` in `f` and
`∑_{J ∈ F} f_J = f_R`): `|T(f_R, ψ ∘ π) - T(f_R · ξ ∘ π, π)| ≤ C₃ δ ∫ |f| dμ_T`. -/
theorem summation (cx : Ctx T π ψ Λ M μ) (sd : ScaleData ψ R δ r F) (hδ1 : δ ≤ 1)
    (D : Set (Matrix (Fin k) (Fin k) ℝ)) (hD : ∀ y, jacMat ψ y ∈ D)
    (hlin : ∀ f, IsBddLipFun f → ∀ A ∈ D, T f (matAct A π) = A.det * T f π)
    {f : Vec d → ℝ} (hf : IsBddLipFun f) :
    |T (cutoffWeight π R f) (psiPi ψ π) -
        T (fun x => cutoffWeight π R f x * xiFun ψ r F (evalTuple π x)) π| ≤
      cubeConst k Λ M * δ * ∫ x, |f x| ∂μ := by
  have := cx.hμ.1.1
  have hw : ∀ J ∈ F, IsBddLipFun (wJ π R f r J) := fun J _ => lipb_wJ cx sd.r_pos R hf J
  have e1 : cutoffWeight π R f = fun x => ∑ J ∈ F, (1 : ℝ) * wJ π R f r J x := by
    funext x; simp [cutoffWeight_eq_sum sd f x]
  have e2 : (fun x => cutoffWeight π R f x * xiFun ψ r F (evalTuple π x)) =
      fun x => ∑ J ∈ F, (jacMat ψ (yJ r J)).det * wJ π R f r J x := by
    funext x
    simp only [xiFun, wJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun J _ => by ring
  rw [e2]
  nth_rewrite 1 [e1]
  rw [T_sum_lin cx.hT F hw _ (isLipTuple_psi cx), T_sum_lin cx.hT F hw _ cx.isLipTuple,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hJ : ∀ J ∈ F, |(1 : ℝ) * T (wJ π R f r J) (psiPi ψ π) -
      (jacMat ψ (yJ r J)).det * T (wJ π R f r J) π| ≤
        cubeConst k Λ M * δ * ∫ x, |wJ π R f r J x| ∂μ := fun J hJ => by
    rw [one_mul]; exact per_cube cx sd hδ1 D hD hlin hf hJ
  refine (Finset.sum_le_sum hJ).trans ?_
  rw [← Finset.mul_sum]
  have hC : 0 ≤ cubeConst k Λ M * δ := by unfold cubeConst; positivity
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← integral_finsetSum _ fun J _ => (integrable_of_borelBdd (borelBdd_of_lipb (hw J ‹_›))).abs]
  refine integral_mono (integrable_finsetSum _ fun J hJ' =>
    (integrable_of_borelBdd (borelBdd_of_lipb (hw J hJ'))).abs)
    (integrable_of_borelBdd (borelBdd_of_lipb hf)).abs fun x => ?_
  exact sum_abs_wJ_le sd f x

end AFree.MetricCurrents.AKTaylor
