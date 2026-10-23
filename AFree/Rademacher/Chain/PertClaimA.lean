module

public import AFree.Rademacher.Chain.PertClaimB

/-!
# Claim A of the single-stage perturbation

The lower bound on the difference quotient of the perturbed function, in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

/-- Claim A. With `h = 4r`, `ḡ = (ς/2) g`, `q = δ/√m` and the
threshold inequality `ω/2 + 4ρ + 2θ ≤ q/6`: for `x ∈ K` (where `D_n g = 1`, `‖x - x̄‖ ≤ r`,
`|v · e_k(x)| ≥ q`) and every `a` with `|a| ≤ ε' ≤ r²`,
`|D_v (f + ḡ)(x) - (f(x + h v) + a - (f + ḡ)(x)) / h| ≥ q / 3`. -/
theorem pert_claimA {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} {xb : Vec d}
    {r s ω θ ρ : ℝ} (ld : LocalData e f xb r s ω θ ρ) {k : Fin d} {r' ε' : ℝ} {g : Vec d → ℝ}
    {K : Set (Vec d)} (cd : CutData e k xb r' ε' (6 * ρ) g K) {ς : ℝ}
    (hς : ς = 1 ∨ ς = -1) {v : Vec d} (hv : vecEuclideanNorm v = 1) (hvn : ‖v‖ ≤ 1) {q : ℝ}
    (hnum : ω / 2 + 4 * ρ + 2 * θ ≤ q / 6) (hrρ : 3 * r ≤ 8 * ρ) (hεr : ε' ≤ r ^ 2)
    {x : Vec d} (hxK : x ∈ K) (hxr : ‖x - xb‖ ≤ r) (hxq : q ≤ |vecDot v (e x k)|)
    {a : ℝ} (ha : |a| ≤ ε') :
    q / 3 ≤ |fderiv ℝ (fun y => f y + ς / 2 * g y) x v -
      ((f (x + (4 * r) • v) + a - (f x + ς / 2 * g x)) / (4 * r))| := by
  have hr := ld.r_pos
  have hdg := cd.differentiable
  have hςa : |ς / 2| = 1 / 2 := by rcases hς with h | h <;> simp [h, abs_div]
  set h := 4 * r with hh
  have hhpos : 0 < h := by positivity
  set n := e xb k with hn
  have hn1 : vecEuclideanNorm n = 1 := ld.frame.norm_eq_one xb k
  have hρ0 := ld.ρ_pos
  have hω0 := ld.ω_nonneg
  have hθ0 := ld.θ_nonneg
  -- Term 1
  have hT1 : (q - ω - 6 * ρ) / 2 ≤ |ς / 2 * fderiv ℝ g x v| := by
    rw [abs_mul, hςa]
    have hu : v = vecDot v n • n + (v - vecDot v n • n) := by abel
    have hDv : fderiv ℝ g x v = vecDot v n + fderiv ℝ g x (v - vecDot v n • n) := by
      conv_lhs => rw [hu]
      rw [map_add, map_smul, smul_eq_mul, cd.dn_K x hxK, mul_one]
    have hw : |fderiv ℝ g x (v - vecDot v n • n)| ≤ 6 * ρ := by
      have h1 := cd.dW x _ (vecDot_proj_orth hn1 v)
      have h2 := vecEuclideanNorm_proj_orth_le hn1 v
      rw [hv] at h2
      calc _ ≤ 6 * ρ * vecEuclideanNorm (v - vecDot v n • n) := h1
        _ ≤ 6 * ρ * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have hvn' : |vecDot v n| ≥ q - ω := by
      have hek := ld.e_close x (by linarith) k
      have hsub : vecDot v n = vecDot v (e x k) - vecDot v (e x k - n) := by
        rw [vecDot_sub_right]; ring
      have hc := abs_vecDot_le_vecEuclideanNorm_mul v (e x k - n)
      rw [hv, one_mul] at hc
      have : |vecDot v (e x k)| ≤ |vecDot v n| + |vecDot v (e x k - n)| := by
        have h0 : vecDot v (e x k) = vecDot v n + vecDot v (e x k - n) := by
          rw [vecDot_sub_right]; ring
        rw [h0]; exact abs_add_le _ _
      linarith
    have : q - ω - 6 * ρ ≤ |fderiv ℝ g x v| := by
      rw [hDv]
      have := abs_sub_abs_le_abs_sub (vecDot v n) (-(fderiv ℝ g x (v - vecDot v n • n)))
      rw [abs_neg, sub_neg_eq_add] at this
      linarith
    rw [one_div]; nlinarith [abs_nonneg (fderiv ℝ g x v)]
  -- Term 2
  have hT2 : |fderiv ℝ f x v - dirQuot f v x h| ≤ 2 * θ := by
    obtain ⟨c, hc, hceq⟩ := exists_dirQuot_eq ld.diff v x hhpos
    rw [hceq, ← vecDot_euclGrad, ← vecDot_euclGrad]
    have hx5 : ‖x - xb‖ ≤ 5 * r := by linarith
    have hy5 : ‖x + c • v - xb‖ ≤ 5 * r := by
      have : x + c • v - xb = (x - xb) + c • v := by abel
      rw [this]
      calc _ ≤ ‖x - xb‖ + ‖c • v‖ := norm_add_le _ _
        _ ≤ r + c * 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
          exact add_le_add hxr (mul_le_mul_of_nonneg_left hvn hc.1.le)
        _ ≤ 5 * r := by linarith [hc.2]
    rw [← vecDot_sub_left]
    have := abs_vecDot_le_vecEuclideanNorm_mul (euclGrad f x - euclGrad f (x + c • v)) v
    rw [hv, mul_one] at this
    refine this.trans ?_
    have h1 := ld.grad_close x hx5
    have h2 := ld.grad_close _ hy5
    have h3 := vecEuclideanNorm_add_le (euclGrad f x - euclGrad f xb)
      (euclGrad f xb - euclGrad f (x + c • v))
    have h4 : euclGrad f x - euclGrad f xb + (euclGrad f xb - euclGrad f (x + c • v)) =
        euclGrad f x - euclGrad f (x + c • v) := by abel
    rw [h4, vecEuclideanNorm_sub_comm (euclGrad f xb)] at h3
    linarith
  -- Term 3
  have hT3 : |(ς / 2 * g x - a) / h| ≤ ρ := by
    rw [abs_div, abs_of_pos hhpos, div_le_iff₀ hhpos]
    have h1 : |ς / 2 * g x| ≤ ε' / 2 := by
      rw [abs_mul, hςa]
      have := cd.bound x
      linarith
    have h2 := abs_sub (ς / 2 * g x) a
    have : ε' * 8 ≤ 8 * r ^ 2 := by linarith
    nlinarith [abs_nonneg (ς / 2 * g x - a)]
  -- Combine
  have hexpr : fderiv ℝ (fun y => f y + ς / 2 * g y) x v -
      ((f (x + h • v) + a - (f x + ς / 2 * g x)) / h) =
      ς / 2 * fderiv ℝ g x v + (fderiv ℝ f x v - dirQuot f v x h) +
        (ς / 2 * g x - a) / h := by
    rw [fderiv_add_const_mul ld.diff hdg]
    unfold dirQuot
    field_simp
    ring
  rw [hexpr]
  have hsum := abs_sub (ς / 2 * fderiv ℝ g x v + (fderiv ℝ f x v - dirQuot f v x h) +
    (ς / 2 * g x - a) / h) (fderiv ℝ f x v - dirQuot f v x h + (ς / 2 * g x - a) / h)
  have heq : ς / 2 * fderiv ℝ g x v + (fderiv ℝ f x v - dirQuot f v x h) +
      (ς / 2 * g x - a) / h - ((fderiv ℝ f x v - dirQuot f v x h) +
        (ς / 2 * g x - a) / h) = ς / 2 * fderiv ℝ g x v := by ring
  rw [heq] at hsum
  have h5 := abs_add_le (fderiv ℝ f x v - dirQuot f v x h) ((ς / 2 * g x - a) / h)
  have h6 := abs_nonneg (ς / 2 * fderiv ℝ g x v + (fderiv ℝ f x v - dirQuot f v x h) +
    (ς / 2 * g x - a) / h)
  linarith

end AFree.Rademacher
