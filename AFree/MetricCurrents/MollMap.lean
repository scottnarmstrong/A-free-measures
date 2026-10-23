module

public import AFree.MetricCurrents.Moll
public import AFree.MetricCurrents.Hadamard

/-!
# Mollifying a tuple
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace AFree

open PDE

/-- Let `F_i` be Euclidean `K_i`-Lipschitz and `F_i^{(n)} = F_i * ρ_{1/(n+1)}`. Then
`F^{(n)} → F` uniformly, each `F_i^{(n)}` is smooth and Euclidean `K_i`-Lipschitz, for every continuous
`Φ` on `ℝ^{m×d}` we have `Φ(DF^{(n)}(x)) → Φ(DF(x))` a.e., in particular every minor converges a.e.,
and every `s × s` minor of every `DF^{(n)}(x)` is bounded by the product of the `K_i` over its rows. -/
theorem mollmap {d m : ℕ} {ρ : Vec d → ℝ} (hρ : IsMollifierKernel ρ) {K : Fin m → ℝ≥0}
    {F : Fin m → Vec d → ℝ} (hF : ∀ i, IsEuclLipschitzWith (K i) (F i)) :
    (∀ i, TendstoUniformly (fun n : ℕ => mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) (F i) atTop) ∧
    (∀ (i : Fin m) (n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) ∧
      IsEuclLipschitzWith (K i) (mollLip ρ (1 / ((n : ℝ) + 1)) (F i))) ∧
    (∀ Φ : Matrix (Fin m) (Fin d) ℝ → ℝ, Continuous Φ →
      ∀ᵐ x, Tendsto (fun n : ℕ =>
        Φ (jacMat (fun i => mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) x)) atTop (𝓝 (Φ (jacMat F x)))) ∧
    (∀ (s : ℕ) (r : Fin s → Fin m) (c : Fin s → Fin d), Function.Injective c →
      ∀ᵐ x, Tendsto (fun n : ℕ =>
        ((jacMat (fun i => mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) x).submatrix r c).det) atTop
          (𝓝 ((jacMat F x).submatrix r c).det)) ∧
    (∀ (s : ℕ) (r : Fin s → Fin m) (c : Fin s → Fin d), Function.Injective c → ∀ (n : ℕ) (x : Vec d),
      |((jacMat (fun i => mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) x).submatrix r c).det| ≤
        ∏ i, (K (r i) : ℝ)) := by
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hsm := fun i n => mollLip_smooth_lipschitz hρ (hF i) (hε n)
  refine ⟨?_, fun i n => ⟨(hsm i n).1, (hsm i n).2.1⟩, ?_, ?_, ?_⟩
  · intro i
    rw [Metric.tendstoUniformly_iff]
    intro e he
    have hlim : Tendsto (fun n : ℕ => Real.sqrt d * K i * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.sqrt d * K i)
    filter_upwards [hlim.eventually (gt_mem_nhds he)] with n hn x
    rw [dist_comm, Real.dist_eq]
    exact ((hsm i n).2.2 x).trans_lt hn
  · have hae : ∀ᵐ x : Vec d, ∀ i j, Tendsto (fun n : ℕ =>
        partialDeriv (mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) x j) atTop
          (𝓝 (partialDeriv (F i) x j)) := by
      rw [ae_all_iff]
      intro i
      exact ae_tendsto_partialDeriv_mollLip hρ (hF i) |>.mono fun x hx j => hx j
    intro Φ hΦ
    filter_upwards [hae] with x hx
    refine (hΦ.tendsto _).comp ?_
    exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hx i j
  · have hae : ∀ᵐ x : Vec d, ∀ i j, Tendsto (fun n : ℕ =>
        partialDeriv (mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) x j) atTop
          (𝓝 (partialDeriv (F i) x j)) := by
      rw [ae_all_iff]
      intro i
      exact ae_tendsto_partialDeriv_mollLip hρ (hF i) |>.mono fun x hx j => hx j
    intro s r c _
    filter_upwards [hae] with x hx
    have hcont : Continuous fun A : Matrix (Fin m) (Fin d) ℝ => (A.submatrix r c).det :=
      (continuous_id.matrix_submatrix r c).matrix_det
    refine (hcont.tendsto _).comp ?_
    exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hx i j
  · intro s r c hc n x
    refine hadamard_abs_minor_le _ (C := fun i => (K i : ℝ)) (fun i => ?_) r c hc
    have hdiff : DifferentiableAt ℝ (mollLip ρ (1 / ((n : ℝ) + 1)) (F i)) x :=
      ((hsm i n).1.differentiable (by simp)) x
    have := MetricCurrents.Moll.sqrt_sum_partial_sq_le (hsm i n).2.1 hdiff
    simpa [piEuclideanNorm, jacMat, partialDeriv, sq] using this

end AFree
