module

public import AFree.Curves.Perturb.Main

/-!
# The Euclidean Lipschitz constant `1 / sin α` of the function of [AM, Proposition 7.4]
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

private lemma perturb_hasDerivAt_line {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y v : Vec d)
    (s : ℝ) : HasDerivAt (fun r : ℝ => f (y + r • v)) (fderiv ℝ f (y + s • v) v) s := by
  have hdf : DifferentiableAt ℝ f (y + s • v) := (hf.differentiable (by simp)).differentiableAt
  have hι : HasDerivAt (fun r : ℝ => y + r • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add y
  have := hdf.hasFDerivAt.comp_hasDerivAt_of_eq s hι rfl
  exact this

/-- Pointwise gradient bound: `|g'(z) w| ≤ (1 / sin α) |w|` from `0 ≤ D_e g ≤ 1` and
`|d_W g| ≤ 1 / tan α`. -/
theorem perturb_fderiv_bound {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {g : Vec d → ℝ} (z : Vec d)
    (h1 : 0 ≤ fderiv ℝ g z e ∧ fderiv ℝ g z e ≤ 1)
    (hW : ∀ w, vecDot w e = 0 → |fderiv ℝ g z w| ≤ (1 / Real.tan α) * vecEuclideanNorm w)
    (w : Vec d) : |fderiv ℝ g z w| ≤ (1 / Real.sin α) * vecEuclideanNorm w := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα2⟩
  set a := vecDot w e with ha
  set wW := w - a • e with hwW
  have hperp : vecDot wW e = 0 := vecDot_sub_dot_smul he w
  have hsplit : fderiv ℝ g z w = a * fderiv ℝ g z e + fderiv ℝ g z wW := by
    have : w = a • e + wW := by rw [hwW]; abel
    conv_lhs => rw [this]
    rw [map_add, map_smul, smul_eq_mul]
  have hb := hW wW hperp
  have hpyth : vecEuclideanNorm w ^ 2 = a ^ 2 + vecEuclideanNorm wW ^ 2 := by
    rw [vecEuclideanNorm_sq, vecEuclideanNorm_sq, hwW, vecNormSq_sub_dot_smul he w]; ring
  have hone : |a * fderiv ℝ g z e| ≤ |a| := by
    rw [abs_mul, abs_of_nonneg h1.1]
    exact mul_le_of_le_one_right (abs_nonneg _) h1.2
  have htan : 1 / Real.tan α = Real.cos α / Real.sin α := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  have key : Real.sin α * |a| + Real.cos α * vecEuclideanNorm wW ≤ vecEuclideanNorm w := by
    refine le_of_sq_le_sq ?_ (vecEuclideanNorm_nonneg w)
    rw [hpyth]
    have hsc := Real.sin_sq_add_cos_sq α
    nlinarith [sq_nonneg (Real.cos α * |a| - Real.sin α * vecEuclideanNorm wW), sq_abs a]
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [htan] at hb
  have : Real.cos α / Real.sin α * vecEuclideanNorm wW =
      (Real.cos α * vecEuclideanNorm wW) / Real.sin α := by ring
  rw [this] at hb
  have h3 : |a| + (Real.cos α * vecEuclideanNorm wW) / Real.sin α ≤
      (1 / Real.sin α) * vecEuclideanNorm w := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
    have : (|a| + (Real.cos α * vecEuclideanNorm wW) / Real.sin α) * Real.sin α =
        Real.sin α * |a| + Real.cos α * vecEuclideanNorm wW := by field_simp
    rw [this]; exact key
  linarith

/-- The Euclidean Lipschitz constant of the function of [AM, Proposition 7.4]: a smooth `g` with
`0 ≤ D_e g ≤ 1` and `|d_W g| ≤ 1 / tan α` everywhere is `1 / sin α`-Lipschitz for the Euclidean
distance. -/
theorem perturb_isEuclLipschitz {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (h1 : ∀ x, 0 ≤ fderiv ℝ g x e ∧ fderiv ℝ g x e ≤ 1)
    (hW : ∀ x w, vecDot w e = 0 → |fderiv ℝ g x w| ≤ (1 / Real.tan α) * vecEuclideanNorm w) :
    IsEuclLipschitzWith (Real.toNNReal (1 / Real.sin α)) g := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  intro x y
  rw [Real.coe_toNNReal _ (by positivity)]
  set v := x - y with hv
  have hφ : ∀ r : ℝ, HasDerivAt (fun r : ℝ => g (y + r • v))
      (fderiv ℝ g (y + r • v) v) r := perturb_hasDerivAt_line hg y v
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun r : ℝ => g (y + r • v))
    (C := (1 / Real.sin α) * vecEuclideanNorm v) (s := univ) (x := 0) (y := 1)
    (fun r _ => (hφ r).differentiableAt)
    (fun r _ => by
      rw [(hφ r).deriv, Real.norm_eq_abs]
      exact perturb_fderiv_bound he hα hα2 _ (h1 _) (hW _) v)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [hv] using this

end AFree
