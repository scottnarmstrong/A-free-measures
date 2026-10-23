module

public import AFree.Rademacher.Chain.PertBasic

/-!
# Local data of the single-stage perturbation and Claim B

Local data at a base point in the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE Filter Topology Set

namespace AFree.Rademacher

variable {d : ℕ}

theorem IsFrame.norm_eq_one {e : Vec d → Fin d → Vec d} (he : IsFrame e) (x : Vec d) (j : Fin d) :
    vecEuclideanNorm (e x j) = 1 := by
  have h := he.2 x j j
  rw [vecDot_self] at h
  simp only [ite_true] at h
  exact (pow_eq_one_iff_of_nonneg (vecEuclideanNorm_nonneg _) two_ne_zero).1 h

theorem IsFrame.dot_eq_zero {e : Vec d → Fin d → Vec d} (he : IsFrame e) (x : Vec d) {j k : Fin d}
    (h : j ≠ k) : vecDot (e x j) (e x k) = 0 := by
  have := he.2 x j k
  simpa [h] using this

/-- The local data (Step 3 of the proof of [AM, Lemma 4.8]) at a base point `x̄`: the frame `e`
and the gradient of `f' = f` are `ω`- and `θ`-close to their values at `x̄` on the ball
`B̄(x̄, 5r)`, `|D_j f'| ≤ 1 - s` everywhere, and the numerical thresholds `num1`, `num2`. -/
structure LocalData (e : Vec d → Fin d → Vec d) (f : Vec d → ℝ) (xb : Vec d)
    (r s ω θ ρ : ℝ) : Prop where
  frame : IsFrame e
  r_pos : 0 < r
  s_pos : 0 < s
  s_le : s ≤ 1 / 2
  diff : Differentiable ℝ f
  bound : ∀ x j, |fderiv ℝ f x (e x j)| ≤ 1 - s
  grad_xb : vecEuclideanNorm (euclGrad f xb) ≤ Real.sqrt d
  e_close : ∀ y, ‖y - xb‖ ≤ 5 * r → ∀ j, vecEuclideanNorm (e y j - e xb j) ≤ ω
  grad_close : ∀ y, ‖y - xb‖ ≤ 5 * r → vecEuclideanNorm (euclGrad f y - euclGrad f xb) ≤ θ
  ω_nonneg : 0 ≤ ω
  θ_nonneg : 0 ≤ θ
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ 1 / 8
  num1 : (2 + Real.sqrt d) * ω + θ ≤ s / 2
  num2 : 3 * ρ + 2 * ω ≤ s

/-- The data of a cut-off perturbation `g` at the base point `x̄` with the base vector `e x̄ k`:
the conclusions of [AM, Lemma 4.11] with `ε = ε'` and `|d_W g| ≤ W`. -/
structure CutData (e : Vec d → Fin d → Vec d) (k : Fin d) (xb : Vec d) (r' ε' W : ℝ)
    (g : Vec d → ℝ) (K : Set (Vec d)) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) g
  bound : ∀ x, |g x| ≤ ε'
  supp : tsupport g ⊆ Metric.closedBall xb r'
  dn : ∀ x, -ε' ≤ fderiv ℝ g x (e xb k) ∧ fderiv ℝ g x (e xb k) ≤ 1 + ε'
  dn_K : ∀ x ∈ K, fderiv ℝ g x (e xb k) = 1
  dW : ∀ x w, vecDot w (e xb k) = 0 → |fderiv ℝ g x w| ≤ W * vecEuclideanNorm w

theorem CutData.differentiable {e : Vec d → Fin d → Vec d} {k : Fin d} {xb : Vec d}
    {r' ε' W : ℝ} {g : Vec d → ℝ} {K : Set (Vec d)} (h : CutData e k xb r' ε' W g K) :
    Differentiable ℝ g := h.smooth.differentiable (by simp)

/-- The gradient of the cut-off perturbation is bounded by `1 + ε' + W`. -/
theorem CutData.abs_fderiv_le {e : Vec d → Fin d → Vec d} {k : Fin d} {xb : Vec d}
    {r' ε' W : ℝ} {g : Vec d → ℝ} {K : Set (Vec d)} (h : CutData e k xb r' ε' W g K)
    (hfr : IsFrame e) (hW : 0 ≤ W) (x u : Vec d) :
    |fderiv ℝ g x u| ≤ (1 + ε' + W) * vecEuclideanNorm u := by
  refine abs_fderiv_le_of_normal (hfr.norm_eq_one xb k) ?_ hW (h.dW x) u
  rw [abs_le]
  exact ⟨by linarith [(h.dn x).1, h.bound x, abs_nonneg (g x), (abs_le.1 (h.bound x)).1,
    (abs_le.1 (h.bound x)).2], (h.dn x).2⟩

end AFree.Rademacher
