module

public import AFree.Rademacher.Chain.PertLocal

/-!
# Claim B of the single-stage perturbation

The gradient bound for the perturbed function, in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- The change of `D_k f` between `x` and the base point `x̄` is at most `θ + √d ω`. -/
theorem LocalData.abs_D_sub_le {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} {xb : Vec d}
    {r s ω θ ρ : ℝ} (ld : LocalData e f xb r s ω θ ρ) {x : Vec d} (hx : ‖x - xb‖ ≤ 5 * r)
    (k : Fin d) :
    |fderiv ℝ f x (e x k) - fderiv ℝ f xb (e xb k)| ≤ θ + Real.sqrt d * ω := by
  rw [← vecDot_euclGrad, ← vecDot_euclGrad]
  have h : vecDot (euclGrad f x) (e x k) - vecDot (euclGrad f xb) (e xb k) =
      vecDot (euclGrad f x - euclGrad f xb) (e x k) +
        vecDot (euclGrad f xb) (e x k - e xb k) := by
    rw [vecDot_sub_left, vecDot_sub_right]; ring
  rw [h]
  have h1 := abs_vecDot_le_vecEuclideanNorm_mul (euclGrad f x - euclGrad f xb) (e x k)
  have h2 := abs_vecDot_le_vecEuclideanNorm_mul (euclGrad f xb) (e x k - e xb k)
  rw [ld.frame.norm_eq_one, mul_one] at h1
  have h3 := ld.grad_close x hx
  have h4 := ld.e_close x hx k
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ θ + Real.sqrt d * ω := by
      have := mul_le_mul ld.grad_xb h4 (vecEuclideanNorm_nonneg _) (Real.sqrt_nonneg _)
      linarith

/-- Claim B: `|D_j (f' + ḡ)(x)| ≤ 1` for all `x` and `j`, where
`ḡ = (ς/2) g`, `ς = ±1` is chosen by the sign of `D_k f'(x̄)`. -/
theorem pert_claimB {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} {xb : Vec d}
    {r s ω θ ρ : ℝ} (ld : LocalData e f xb r s ω θ ρ) {k : Fin d} {r' ε' : ℝ} {g : Vec d → ℝ}
    {K : Set (Vec d)} (cd : CutData e k xb r' ε' (6 * ρ) g K) (hr' : r' ≤ 2 * r)
    (hε' : ε' ≤ s) {ς : ℝ}
    (hς : (ς = 1 ∧ fderiv ℝ f xb (e xb k) ≤ 0) ∨ (ς = -1 ∧ 0 < fderiv ℝ f xb (e xb k)))
    (x : Vec d) (j : Fin d) :
    |fderiv ℝ (fun y => f y + ς / 2 * g y) x (e x j)| ≤ 1 := by
  have hdg := cd.differentiable
  rw [fderiv_add_const_mul ld.diff hdg]
  have hs := ld.s_le
  have hs0 := ld.s_pos
  have hb := ld.bound x j
  by_cases hxs : x ∈ tsupport g
  swap
  · rw [fderiv_of_notMem_tsupport ℝ hxs]
    simp only [zero_apply, mul_zero, add_zero]
    exact hb.trans (by linarith)
  have hxr : ‖x - xb‖ ≤ 2 * r := by
    have := Metric.mem_closedBall.1 (cd.supp hxs)
    rw [dist_eq_norm] at this
    linarith
  have hx5 : ‖x - xb‖ ≤ 5 * r := by linarith [ld.r_pos]
  have hgrad : ∀ u, |fderiv ℝ g x u| ≤ 3 * vecEuclideanNorm u := by
    intro u
    have := cd.abs_fderiv_le ld.frame (by linarith [ld.ρ_pos]) x u
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (vecEuclideanNorm_nonneg _))
    linarith [ld.ρ_le]
  have hς2 : |ς / 2| ≤ 1 / 2 := by
    rcases hς with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, abs_div]
  have hωj : ∀ j, vecEuclideanNorm (e x j - e xb j) ≤ ω := ld.e_close x hx5
  by_cases hjk : j = k
  · subst hjk
    have hD := ld.abs_D_sub_le hx5 j
    have hsplit : fderiv ℝ g x (e x j) =
        fderiv ℝ g x (e xb j) + fderiv ℝ g x (e x j - e xb j) := by
      rw [← map_add]; congr 1; abel
    have he1 : |fderiv ℝ g x (e x j - e xb j)| ≤ 3 * ω :=
      (hgrad _).trans (mul_le_mul_of_nonneg_left (hωj j) (by norm_num))
    set t := fderiv ℝ g x (e xb j) with ht
    have htb := cd.dn x
    set D0 := fderiv ℝ f xb (e xb j) with hD0
    set D := fderiv ℝ f x (e x j) with hDdef
    set e1 := fderiv ℝ g x (e x j - e xb j) with he1def
    have hmain : |D0 + ς / 2 * t| ≤ 1 - s / 2 := by
      rw [abs_le]
      have hD0b := abs_le.1 (ld.bound xb j)
      rcases hς with ⟨h, hneg⟩ | ⟨h, hpos⟩
      · rw [h]; constructor <;> nlinarith [htb.1, htb.2, hD0b.1]
      · rw [h]; constructor <;> nlinarith [htb.1, htb.2, hD0b.2]
    have herr : |ς / 2 * e1| ≤ 2 * ω := by
      rw [abs_mul]
      have := ld.ω_nonneg
      calc |ς / 2| * |e1| ≤ (1 / 2) * (3 * ω) :=
            mul_le_mul hς2 he1 (abs_nonneg _) (by norm_num)
        _ ≤ 2 * ω := by linarith
    have hfin : D + ς / 2 * fderiv ℝ g x (e x j) =
        (D0 + ς / 2 * t) + ((D - D0) + ς / 2 * e1) := by
      rw [hsplit]; ring
    rw [hfin]
    have hnum := ld.num1
    have hsq := Real.sqrt_nonneg (d : ℝ)
    calc _ ≤ |D0 + ς / 2 * t| + |(D - D0) + ς / 2 * e1| := abs_add_le _ _
      _ ≤ (1 - s / 2) + ((θ + Real.sqrt d * ω) + 2 * ω) :=
        add_le_add hmain ((abs_add_le _ _).trans (add_le_add hD herr))
      _ ≤ 1 := by nlinarith
  · have hperp : vecDot (e xb j) (e xb k) = 0 := ld.frame.dot_eq_zero xb hjk
    have hsplit : fderiv ℝ g x (e x j) =
        fderiv ℝ g x (e xb j) + fderiv ℝ g x (e x j - e xb j) := by
      rw [← map_add]; congr 1; abel
    have h1 : |fderiv ℝ g x (e xb j)| ≤ 6 * ρ := by
      have := cd.dW x _ hperp
      rwa [ld.frame.norm_eq_one, mul_one] at this
    have h2 : |fderiv ℝ g x (e x j - e xb j)| ≤ 3 * ω :=
      (hgrad _).trans (mul_le_mul_of_nonneg_left (hωj j) (by norm_num))
    have hgj : |fderiv ℝ g x (e x j)| ≤ 6 * ρ + 3 * ω := by
      rw [hsplit]; exact (abs_add_le _ _).trans (add_le_add h1 h2)
    have hnum := ld.num2
    have := ld.ω_nonneg
    calc _ ≤ |fderiv ℝ f x (e x j)| + |ς / 2 * fderiv ℝ g x (e x j)| := abs_add_le _ _
      _ ≤ (1 - s) + (1 / 2) * (6 * ρ + 3 * ω) := by
        refine add_le_add hb ?_
        rw [abs_mul]
        exact mul_le_mul hς2 hgj (abs_nonneg _) (by norm_num)
      _ ≤ 1 := by linarith

end AFree.Rademacher
