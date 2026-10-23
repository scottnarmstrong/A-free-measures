module

public import AFree.MetricCurrents.AKExt
public import AFree.MetricCurrents.Grid
public import AFree.MetricCurrents.Hadamard
public import AFree.MetricCurrents.AKTaylorJac

/-!
# The Taylor lemma: [AK, (3.2)] modulo the linear case

The chain rule for metric currents, assuming the multiplicativity `T(f, Aπ) = det A · T(f, π)`, is
assembled from the steps in `AKTaylorReduction`, `AKTaylorScale`, `AKTaylorFreeze`, `AKTaylorMulti`,
`AKTaylorSummation` and `AKTaylorJac`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.AKTaylor

/-- Chain rule modulo the linear case. Let `k ≥ 1`, `π ∈ Lip^k`,
`ψ_i ∈ C¹(ℝ^k)` with bounded gradients, `𝒟 ⊆ ℝ^{k×k}` containing `Dψ(y)` for every `y`, and assume
`T(f, Aπ) = det A · T(f, π)` for `f ∈ Lip_b`, `A ∈ 𝒟`. Then for every `h ∈ B^∞`:
`T(h, ψ ∘ π) = T(h det Dψ(π), π)`. -/
theorem aktaylor {d k : ℕ} (hk : 1 ≤ k) {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    {ψ : Fin k → Vec k → ℝ} (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hM : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M)
    (D : Set (Matrix (Fin k) (Fin k) ℝ)) (hD : ∀ y, jacMat ψ y ∈ D)
    (hlin : ∀ f, IsBddLipFun f → ∀ A ∈ D, T f (matAct A π) = A.det * T f π)
    {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    akExt T h (fun i x => ψ i (evalTuple π x)) =
      akExt T (fun x => h x * jacDet ψ (evalTuple π x)) π := by
  have _hk := hk
  classical
  obtain ⟨M₀, hM₀⟩ := hM
  choose K hK using hπ
  set Λ : ℝ≥0 := ∑ l, K l with hΛ
  have hKΛ : ∀ l, K l ≤ Λ := fun l =>
    Finset.single_le_sum (f := K) (fun _ _ => zero_le) (Finset.mem_univ l)
  have hπΛ : ∀ l, IsEuclLipschitzWith Λ (π l) := fun l x y =>
    (hK l x y).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hKΛ l) (vecEuclideanNorm_nonneg _))
  have hμ := akMassMeasure_isAKMass hT
  have cx : Ctx T π ψ Λ M₀.toNNReal (akMassMeasure T) :=
    ⟨hT, hμ, hπΛ, hψ, fun i y => (hM₀ i y).trans (Real.le_coe_toNNReal _)⟩
  have := hμ.1.1
  set C : ℝ := cubeConst k Λ M₀.toNNReal + (Λ : ℝ) ^ k * jacConst k M₀.toNNReal with hC
  have hC0 : 0 ≤ C := by rw [hC]; unfold cubeConst jacConst; positivity
  have hfR : ∀ f, IsBddLipFun f → ∀ R : ℝ, 0 < R → Dfun T π ψ (cutoffWeight π R f) = 0 := by
    intro f hf R hR
    have hg := lipb_cutoffWeight cx R hf
    refine eq_zero_of_bound (u := fun n : ℕ => C * (1 / ((n : ℝ) + 1)) *
      ∫ x, |f x| ∂(akMassMeasure T)) (fun n => ?_) ?_
    · set δ : ℝ≥0 := (1 / ((n : ℝ) + 1)).toNNReal with hδ
      have hδpos : 0 < δ := by rw [hδ]; exact Real.toNNReal_pos.2 (by positivity)
      have hδ1 : δ ≤ 1 := by
        rw [hδ]
        refine Real.toNNReal_le_one.2 ?_
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hδr : (δ : ℝ) = 1 / ((n : ℝ) + 1) := Real.coe_toNNReal _ (by positivity)
      obtain ⟨r, F, sd⟩ := exists_scaleData hψ R hδpos
      have s1 := summation cx sd hδ1 D hD hlin hf
      have s2 := frozen_vs_exact cx sd hf
      have hE1 := (akext hT).1.1 _ hg (psiPi ψ π) (isLipTuple_psi cx)
      unfold Dfun
      rw [hE1]
      have hsplit : T (cutoffWeight π R f) (psiPi ψ π) - akExt T (jacW ψ π (cutoffWeight π R f)) π =
          (T (cutoffWeight π R f) (psiPi ψ π) -
            T (fun x => cutoffWeight π R f x * xiFun ψ r F (evalTuple π x)) π) -
          (akExt T (jacW ψ π (cutoffWeight π R f)) π -
            T (fun x => cutoffWeight π R f x * xiFun ψ r F (evalTuple π x)) π) := by ring
      rw [hsplit]
      refine (abs_sub _ _).trans ?_
      rw [hδr] at s1 s2
      calc _ ≤ cubeConst k Λ M₀.toNNReal * (1 / ((n : ℝ) + 1)) * ∫ x, |f x| ∂(akMassMeasure T) +
            (Λ : ℝ) ^ k * (jacConst k M₀.toNNReal * (1 / ((n : ℝ) + 1))) *
              ∫ x, |f x| ∂(akMassMeasure T) := add_le_add s1 s2
        _ = _ := by rw [hC]; ring
    · rw [show (0 : ℝ) = C * 0 * ∫ x, |f x| ∂(akMassMeasure T) by ring]
      exact (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C).mul_const _
  have := reduction cx hfR h hh
  exact sub_eq_zero.1 this

end AFree
