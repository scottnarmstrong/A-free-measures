module

public import AFree.MetricCurrents.AKAlt
public import AFree.MetricCurrents.Hadamard

/-!
# The chain rule [AK, (3.2)]
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AKChainAux

/-- A `C¹` map with bounded derivative composed with a tuple of Lipschitz functions is Lipschitz. -/
private lemma isLipFun_comp_tuple {d k : ℕ} {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    {u : Vec k → ℝ} (hu : ContDiff ℝ 1 u) {M : ℝ} (hM : ∀ y, ‖fderiv ℝ u y‖ ≤ M) :
    IsLipFun (fun x => u (evalTuple π x)) := by
  choose K hK using hπ
  have hL : LipschitzWith (Real.toNNReal M) u := by
    refine lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable one_ne_zero) fun y => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ ((norm_nonneg _).trans (hM y))]
    exact hM y
  refine ⟨Real.toNNReal M * ∑ l, K l, fun x y => ?_⟩
  have h1 : ‖evalTuple π x - evalTuple π y‖ ≤ (∑ l, (K l : ℝ)) * vecEuclideanNorm (x - y) := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => (K _).2)
      (vecEuclideanNorm_nonneg _))).2 fun l => ?_
    have := hK l x y
    simp only [evalTuple, Pi.sub_apply, Real.norm_eq_abs]
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (vecEuclideanNorm_nonneg _))
    exact Finset.single_le_sum (f := fun l => (K l : ℝ)) (fun _ _ => (K _).2) (Finset.mem_univ l)
  have h2 := hL.dist_le_mul (evalTuple π x) (evalTuple π y)
  rw [Real.dist_eq, dist_eq_norm] at h2
  push_cast
  calc |u (evalTuple π x) - u (evalTuple π y)| ≤ _ := h2
    _ ≤ (Real.toNNReal M : ℝ) * ((∑ l, (K l : ℝ)) * vecEuclideanNorm (x - y)) :=
        mul_le_mul_of_nonneg_left h1 (NNReal.coe_nonneg _)
    _ = _ := by ring

private lemma continuous_jacDet {k : ℕ} {ψ : Fin k → Vec k → ℝ} (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) :
    Continuous (jacDet ψ) := by
  unfold jacDet
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  exact ((hψ i).continuous_fderiv one_ne_zero).clm_apply continuous_const

private lemma abs_jacDet_le {k : ℕ} {ψ : Fin k → Vec k → ℝ} {M : ℝ}
    (hM : ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M) (y : Vec k) :
    |jacDet ψ y| ≤ (Real.sqrt (k * (max M 0) ^ 2)) ^ k := by
  refine hadamard_abs_det_le_pow _ fun i => ?_
  unfold piEuclideanNorm
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, jacMat ψ y i j * jacMat ψ y i j ≤ ∑ _j : Fin k, (max M 0) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : |jacMat ψ y i j| ≤ M := by
          have e : jacMat ψ y i j = fderiv ℝ (ψ i) y (Pi.single j 1) := rfl
          rw [e]
          have h2 : ‖(Pi.single j (1 : ℝ) : Vec k)‖ ≤ 1 := by
            refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
            by_cases hl : l = j
            · subst hl; simp
            · simp [hl]
          calc |fderiv ℝ (ψ i) y (Pi.single j 1)| = ‖fderiv ℝ (ψ i) y (Pi.single j 1)‖ :=
                (Real.norm_eq_abs _).symm
            _ ≤ ‖fderiv ℝ (ψ i) y‖ * ‖(Pi.single j (1 : ℝ) : Vec k)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ M * 1 := mul_le_mul (hM i y) h2 (norm_nonneg _) ((norm_nonneg _).trans (hM i y))
            _ = M := mul_one M
        have h3 := abs_le.mp (h1.trans (le_max_left M 0))
        nlinarith [h3.1, h3.2, le_max_right M 0]
    _ = k * (max M 0) ^ 2 := by simp

/-- The weight `h · det Dψ(π)` in the chain rule is again a bounded Borel function. -/
theorem isBorelBdd_mul_jacDet {d k : ℕ} {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    {ψ : Fin k → Vec k → ℝ} (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hM : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    IsBorelBdd (fun x => h x * jacDet ψ (evalTuple π x)) := by
  obtain ⟨M, hM⟩ := hM
  choose K hK using hπ
  have hev : Continuous (evalTuple π : Vec d → Vec k) :=
    continuous_pi fun l => continuous_of_lip (hK l)
  exact isBorelBdd_mul hh ((continuous_jacDet hψ).comp hev).measurable
    fun x => abs_jacDet_le hM _

/-- [AK, (3.2)] Let `T ∈ M_k(ℝ^d)`, `h ∈ B^∞`, `π ∈ Lip^k` and `ψ_i ∈ C¹(ℝ^k)` with
bounded gradients (`∃ M, ∀ i y, ‖Dψ_i(y)‖ ≤ M`). Then `ψ ∘ π ∈ Lip^k` and
`T(h, ψ_1 ∘ π, …, ψ_k ∘ π) = T(h · det Dψ(π), π_1, …, π_k)`; here `T` on `B^∞ × Lip^k` is the
extension `akExt T`. (Also true, trivially, for `k = 0`.) -/
theorem akchain {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    {ψ : Fin k → Vec k → ℝ} (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hM : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    IsLipTuple (fun i x => ψ i (evalTuple π x)) ∧
      akExt T h (fun i x => ψ i (evalTuple π x)) =
        akExt T (fun x => h x * jacDet ψ (evalTuple π x)) π := by
  obtain ⟨M, hM'⟩ := hM
  refine ⟨fun i => isLipFun_comp_tuple hπ (hψ i) (hM' i), ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e1 : (fun i x => ψ i (evalTuple π x)) = π := Subsingleton.elim _ _
    have e2 : (fun x => h x * jacDet ψ (evalTuple π x)) = h := by
      funext x; simp [jacDet]
    rw [e1, e2]
  · refine aktaylor hk hT hπ hψ ⟨M, hM'⟩ Set.univ (fun _ => trivial) ?_ hh
    intro f hf A _
    have hf' := isBorelBdd_of_isBddLipFun hf
    have := akalt_matrix hT hπ A hf'
    rwa [(akext hT).1.1 f hf _ (isLipTuple_matAct hπ A), (akext hT).1.1 f hf _ hπ] at this

end AFree
