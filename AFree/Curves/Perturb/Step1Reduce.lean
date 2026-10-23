module

public import AFree.Curves.Perturb.Nbhd
public import AFree.Curves.Perturb.GDef
public import AFree.Curves.Clamp

/-!
# Reduction to a fixed interval
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

/-- Let `‖k‖ ≤ R` on `K`, `0 ≤ R`, `δ ≤ 1` and `η`
`tan α`-Lipschitz into `e^⊥` on `[a, b]`. Then `ζ = η ∘ clamp_{[a,b]} ∘ clamp_{J'}`, with
`J' = [-R-1, R+1]`, is `tan α`-Lipschitz into `e^⊥` on `J'`; every `u ∈ [a, b]` with
`γ_η(u) ∈ N_δ(K)` lies in `J'` where `ζ(u) = η(u)` and `|η(u)| ≤ 2R + 2`; in particular the
parameter set of `ζ` on `J'` is at least that of `η` on `[a, b]`. -/
theorem perturb_step1_reduction (he : vecEuclideanNorm e = 1) (hα : 0 ≤ Real.tan α)
    {K : Set (Vec d)} {R δ : ℝ} (hR0 : 0 ≤ R) (hR : ∀ k ∈ K, vecEuclideanNorm k ≤ R) (hδ : δ ≤ 1)
    {a b : ℝ} {η : ℝ → Vec d} (hab : a ≤ b) (hη : IsConeGraphFn e α a b η) :
    ∃ ζ : ℝ → Vec d, IsConeGraphFn e α (-R - 1) (R + 1) ζ ∧
      (∀ u ∈ Icc a b, graphCurve e η u ∈ perturbClosedNbhd K δ →
        u ∈ Icc (-R - 1) (R + 1) ∧ ζ u = η u ∧ vecEuclideanNorm (η u) ≤ 2 * R + 2) ∧
      perturbMeas e (perturbClosedNbhd K δ) a b η ≤
        perturbMeas e (perturbClosedNbhd K δ) (-R - 1) (R + 1) ζ := by
  have hJ : -R - 1 ≤ R + 1 := by linarith
  set c : ℝ → ℝ := fun u => clampIcc a b (clampIcc (-R - 1) (R + 1) u) with hc
  have hcmem : ∀ u, c u ∈ Icc a b := fun u => clampIcc_mem hab _
  have hclip : ∀ u u', |c u - c u'| ≤ |u - u'| := fun u u' =>
    (abs_clampIcc_sub_le hab _ _).trans (abs_clampIcc_sub_le hJ _ _)
  have key : ∀ u ∈ Icc a b, graphCurve e η u ∈ perturbClosedNbhd K δ →
      u ∈ Icc (-R - 1) (R + 1) ∧ vecEuclideanNorm (η u) ≤ 2 * R + 2 := by
    intro u hu ⟨k, hk, hk1⟩
    have hdot : vecDot (graphCurve e η u) e = u := by
      rw [graphCurve, add_comm, perturb_dot_add_smul he, (hη.1 u hu), zero_add]
    have h1 : |u - vecDot k e| ≤ 1 := by
      have := abs_vecDot_le_vecEuclideanNorm_mul (graphCurve e η u - k) e
      rw [he, mul_one, vecDot_sub_left, hdot] at this
      linarith
    have h2 : |vecDot k e| ≤ R := by
      have := abs_vecDot_le_vecEuclideanNorm_mul k e
      rw [he, mul_one] at this
      exact this.trans (hR k hk)
    have hu1 : |u| ≤ R + 1 := by
      have := abs_sub_abs_le_abs_sub u (vecDot k e)
      linarith
    refine ⟨⟨by linarith [(abs_le.mp hu1).1], (abs_le.mp hu1).2⟩, ?_⟩
    have hsplit : η u = (graphCurve e η u - k) + k - u • e := by
      rw [graphCurve]; abel
    have hn1 := vecEuclideanNorm_sub_le ((graphCurve e η u - k) + k) (u • e)
    have hn2 := vecEuclideanNorm_add_le (graphCurve e η u - k) k
    have hn3 : vecEuclideanNorm (u • e) = |u| := by rw [vecEuclideanNorm_smul, he, mul_one]
    rw [hsplit]
    linarith [hR k hk]
  refine ⟨fun u => η (c u), ⟨fun u _ => hη.1 _ (hcmem u), fun u _ u' _ => ?_⟩, ?_, ?_⟩
  · refine (hη.2 _ (hcmem u) _ (hcmem u')).trans ?_
    exact mul_le_mul_of_nonneg_left (hclip u u') hα
  · intro u hu hN
    obtain ⟨hJu, hnorm⟩ := key u hu hN
    refine ⟨hJu, ?_, hnorm⟩
    simp only [hc, clampIcc_of_mem hJu, clampIcc_of_mem hu]
  · refine measure_mono fun u ⟨hu, hP⟩ => ?_
    obtain ⟨hJu, hz, -⟩ := (by
      have hN : graphCurve e η u ∈ perturbClosedNbhd K δ := hP
      have := key u hu hN
      exact ⟨this.1, by simp only [hc, clampIcc_of_mem this.1, clampIcc_of_mem hu], this.2⟩ :
        u ∈ Icc (-R - 1) (R + 1) ∧ η (c u) = η u ∧ vecEuclideanNorm (η u) ≤ 2 * R + 2)
    refine ⟨hJu, ?_⟩
    show graphCurve e (fun u => η (c u)) u ∈ perturbClosedNbhd K δ
    have : graphCurve e (fun u => η (c u)) u = graphCurve e η u := by simp [graphCurve, hz]
    rw [this]; exact hP

end AFree
