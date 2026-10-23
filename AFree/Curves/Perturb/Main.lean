module

public import AFree.Curves.Perturb.Choice

/-!
# [AM, Proposition 7.4]
-/

@[expose] public section

open MeasureTheory Set

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- Let `e` be a unit vector, `α ∈ (0, π/2)`, `K ⊆ ℝ^d` a compact
`C(e, α)`-null set and `ε > 0`. There is a smooth `g : ℝ^d → ℝ` with `0 ≤ g ≤ ε`,
`0 ≤ D_e g ≤ 1` everywhere (`D_e g(x) = g'(x) e`), `D_e g = 1` on an open set `U ⊇ K`, and
`|d_W g| ≤ 1 / tan α` everywhere for `W = e^⊥`, in the form
`|g'(x) w| ≤ (1 / tan α) |w|` for all `w ⊥ e`. -/
theorem perturb_of_cnull {e : Vec d} (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α)
    (hα2 : α < Real.pi / 2) {K : Set (Vec d)} (hK : IsCompact K)
    (hnull : IsCNull (cone e α) K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ ε) ∧
      (∀ x, 0 ≤ fderiv ℝ g x e ∧ fderiv ℝ g x e ≤ 1) ∧
      (∃ U : Set (Vec d), IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, fderiv ℝ g x e = 1) ∧
      ∀ x w, vecDot w e = 0 → |fderiv ℝ g x w| ≤ (1 / Real.tan α) * vecEuclideanNorm w := by
  have htpos : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2
  obtain ⟨δ, g, ρ, hδ0, -, hg, hg0, hmono, hseg, hW, hρ, hρc, hρ0, hρ1, hρs⟩ :=
    perturb_choice_of_data he hα hα2 hK hnull hε
  obtain ⟨hsm, hb⟩ := perturb_smooth_bounds hg hg0 hρ hρc hρ0 hρ1
  obtain ⟨he1, he2⟩ := perturb_e_derivative he hδ0 hg hg0 hmono hseg hρ hρc hρ0 hρ1 hρs
  exact ⟨perturbMollify ρ g, hsm, hb, he1,
    ⟨perturbOpenNbhd K (δ / 3), isOpen_perturbOpenNbhd K _,
      subset_perturbOpenNbhd K (by linarith), he2⟩,
    perturb_W_derivative htpos hg hg0 hW hρ hρc hρ0 hρ1⟩

end AFree
