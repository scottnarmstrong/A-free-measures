module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Module

/-!
# The cubic Hermite interpolant

On a gap `(p, q)` the extension is the
cubic with prescribed values `A, B` and derivatives `U, V` at `p, q`.
-/

@[expose] public section

namespace AFree

namespace Lusin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cubic Hermite interpolant on `[p, q]` with values `A, B` and derivatives `U, V`. -/
noncomputable def herm (p q : ℝ) (A B U V : E) (t : ℝ) : E :=
  A + ((t - p) / (q - p)) • ((q - p) • U) +
    ((t - p) / (q - p)) ^ 2 • ((3 : ℝ) • (B - A) - (q - p) • ((2 : ℝ) • U + V)) +
    ((t - p) / (q - p)) ^ 3 • ((2 : ℝ) • (A - B) + (q - p) • (U + V))

/-- The weights of the derivative of the Hermite cubic at the parameter `θ` (weights summing to
one): `6θ(1-θ) κ + (3θ²-4θ+1) U + (3θ²-2θ) V`. -/
def hermW (θ : ℝ) (κ U V : E) : E :=
  (6 * θ * (1 - θ)) • κ + (3 * θ ^ 2 - 4 * θ + 1) • U + (3 * θ ^ 2 - 2 * θ) • V

/-- The derivative of `herm`, as a weighted combination. -/
noncomputable def hermD (p q : ℝ) (A B U V : E) (t : ℝ) : E :=
  hermW ((t - p) / (q - p)) ((q - p)⁻¹ • (B - A)) U V

lemma herm_left (p q : ℝ) (A B U V : E) : herm p q A B U V p = A := by
  simp [herm]

lemma herm_right {p q : ℝ} (hpq : p < q) (A B U V : E) : herm p q A B U V q = B := by
  have h : q - p ≠ 0 := (sub_pos.2 hpq).ne'
  simp only [herm, div_self h, one_smul, one_pow]
  module

/-- The cubic Hermite interpolant on `[p, q]` is differentiable with
derivative `hermD` (weights `6θ(1-θ)`, `3θ²-4θ+1`, `3θ²-2θ`, summing to one), interpolates the
values `A, B` and the derivatives `U, V` at `p, q`. -/
theorem herm_hasDerivAt {p q : ℝ} (hpq : p < q) (A B U V : E) (t : ℝ) :
    HasDerivAt (herm p q A B U V) (hermD p q A B U V t) t := by
  have h : q - p ≠ 0 := (sub_pos.2 hpq).ne'
  have hθ : HasDerivAt (fun t : ℝ => (t - p) / (q - p)) (q - p)⁻¹ t := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id t).sub_const p).mul_const (q - p)⁻¹
  have h1 := hθ.smul_const ((q - p) • U)
  have h2 := (hθ.pow 2).smul_const ((3 : ℝ) • (B - A) - (q - p) • ((2 : ℝ) • U + V))
  have h3 := (hθ.pow 3).smul_const ((2 : ℝ) • (A - B) + (q - p) • (U + V))
  have h4 := (((h1.const_add A).add h2).add h3)
  refine h4.congr_deriv ?_
  simp only [hermD, hermW, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    pow_one]
  match_scalars <;> field_simp <;> ring

lemma hermW_sub_left_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (κ U V : E) {D : ℝ}
    (h1 : ‖κ - U‖ ≤ D) (h2 : ‖V - U‖ ≤ D) : ‖hermW θ κ U V - U‖ ≤ 8 * θ * D := by
  have hD : 0 ≤ D := (norm_nonneg _).trans h2
  have e : hermW θ κ U V - U = (6 * θ * (1 - θ)) • (κ - U) + (3 * θ ^ 2 - 2 * θ) • (V - U) := by
    simp only [hermW]; module
  have a1 : 0 ≤ 6 * θ * (1 - θ) := by nlinarith
  have a2 : |3 * θ ^ 2 - 2 * θ| ≤ 2 * θ := by rw [abs_le]; constructor <;> nlinarith
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg a1]
  have b1 : 6 * θ * (1 - θ) * ‖κ - U‖ ≤ 6 * θ * D := by
    calc _ ≤ 6 * θ * (1 - θ) * D := by gcongr
      _ ≤ 6 * θ * D := by nlinarith
  have b2 : |3 * θ ^ 2 - 2 * θ| * ‖V - U‖ ≤ 2 * θ * D := by gcongr
  linarith

lemma hermW_sub_right_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (κ U V : E) {D : ℝ}
    (h1 : ‖κ - V‖ ≤ D) (h2 : ‖U - V‖ ≤ D) : ‖hermW θ κ U V - V‖ ≤ 8 * (1 - θ) * D := by
  have hD : 0 ≤ D := (norm_nonneg _).trans h2
  have e : hermW θ κ U V - V = (6 * θ * (1 - θ)) • (κ - V) + (3 * θ ^ 2 - 4 * θ + 1) • (U - V) := by
    simp only [hermW]; module
  have a1 : 0 ≤ 6 * θ * (1 - θ) := by nlinarith
  have a2 : |3 * θ ^ 2 - 4 * θ + 1| ≤ 2 * (1 - θ) := by rw [abs_le]; constructor <;> nlinarith
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg a1]
  have b1 : 6 * θ * (1 - θ) * ‖κ - V‖ ≤ 6 * (1 - θ) * D := by
    calc _ ≤ 6 * θ * (1 - θ) * D := by gcongr
      _ ≤ 6 * (1 - θ) * D := by
        nlinarith [mul_nonneg (mul_nonneg hD (sub_nonneg.2 hθ1)) (sub_nonneg.2 hθ1)]
  have b2 : |3 * θ ^ 2 - 4 * θ + 1| * ‖U - V‖ ≤ 2 * (1 - θ) * D := by gcongr
  linarith

/-- The `θ`-weighted estimate at the left endpoint. -/
lemma hermD_sub_left_le {p q t : ℝ} (hpq : p < q) (ht : t ∈ Set.Icc p q) (A B U V : E) {D : ℝ}
    (h1 : ‖(q - p)⁻¹ • (B - A) - U‖ ≤ D) (h2 : ‖V - U‖ ≤ D) :
    ‖hermD p q A B U V t - U‖ ≤ 8 * ((t - p) / (q - p)) * D := by
  have hl : 0 < q - p := sub_pos.2 hpq
  exact hermW_sub_left_le (div_nonneg (sub_nonneg.2 ht.1) hl.le)
    ((div_le_one hl).2 (by linarith [ht.2])) _ _ _ h1 h2

/-- The `θ`-weighted estimate at the right endpoint, symmetric form. -/
lemma hermD_sub_right_le {p q t : ℝ} (hpq : p < q) (ht : t ∈ Set.Icc p q) (A B U V : E) {D : ℝ}
    (h1 : ‖(q - p)⁻¹ • (B - A) - V‖ ≤ D) (h2 : ‖U - V‖ ≤ D) :
    ‖hermD p q A B U V t - V‖ ≤ 8 * (1 - (t - p) / (q - p)) * D := by
  have hl : 0 < q - p := sub_pos.2 hpq
  exact hermW_sub_right_le (div_nonneg (sub_nonneg.2 ht.1) hl.le)
    ((div_le_one hl).2 (by linarith [ht.2])) _ _ _ h1 h2

end Lusin

end AFree
