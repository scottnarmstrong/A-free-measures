module

public import AFree.Curves.Dichotomy.LusinExt

/-!
# Estimates on one gap of the Whitney extension

`Pars S φ ψ L η δW` packages the Whitney data on a set `S` in the form used at a fixed accuracy `η`:
Lipschitz bound `L`, `‖ψ‖ ≤ L` on `S`, and the Whitney condition for `|s' - s| < δW`.
-/

@[expose] public section

open Set

namespace AFree

namespace Lusin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Whitney data at a fixed accuracy. -/
structure Pars (S : Set ℝ) (φ ψ : ℝ → E) (L η δW : ℝ) : Prop where
  lip : ∀ s ∈ S, ∀ s' ∈ S, ‖φ s' - φ s‖ ≤ L * |s' - s|
  bdd : ∀ s ∈ S, ‖ψ s‖ ≤ L
  whit : ∀ s ∈ S, ∀ s' ∈ S, |s' - s| < δW → ‖φ s' - φ s - (s' - s) • ψ s‖ ≤ η * |s' - s|
  hη : 0 < η
  hδW : 0 < δW

variable {S : Set ℝ} {φ ψ : ℝ → E} {L η δW : ℝ}

/-- The derivative `ψ` is uniformly continuous on `S`. -/
lemma Pars.psi_close (h : Pars S φ ψ L η δW) {s s' : ℝ} (hs : s ∈ S) (hs' : s' ∈ S)
    (hd : |s' - s| < δW) : ‖ψ s' - ψ s‖ ≤ 2 * η := by
  rcases eq_or_ne s s' with rfl | hne
  · simp [h.hη.le]
  have h1 := h.whit s hs s' hs' hd
  have h2 := h.whit s' hs' s hs (by rwa [abs_sub_comm])
  have hpos : 0 < |s' - s| := abs_pos.2 (sub_ne_zero.2 hne.symm)
  have e : (s' - s) • (ψ s' - ψ s) =
      (φ s' - φ s - (s' - s) • ψ s) + (φ s - φ s' - (s - s') • ψ s') := by module
  have h3 : |s' - s| * ‖ψ s' - ψ s‖ ≤ 2 * η * |s' - s| := by
    calc |s' - s| * ‖ψ s' - ψ s‖ = ‖(s' - s) • (ψ s' - ψ s)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖φ s' - φ s - (s' - s) • ψ s‖ + ‖φ s - φ s' - (s - s') • ψ s'‖ := by
          rw [e]; exact norm_add_le _ _
      _ ≤ η * |s' - s| + η * |s - s'| := add_le_add h1 h2
      _ = 2 * η * |s' - s| := by rw [abs_sub_comm s s']; ring
  nlinarith

lemma Pars.kappa_left (h : Pars S φ ψ L η δW) {p q : ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p < q)
    (hd : q - p < δW) : ‖(q - p)⁻¹ • (φ q - φ p) - ψ p‖ ≤ η := by
  have hl : 0 < q - p := sub_pos.2 hpq
  have e : (q - p)⁻¹ • (φ q - φ p) - ψ p = (q - p)⁻¹ • (φ q - φ p - (q - p) • ψ p) := by
    have := hl.ne'
    match_scalars <;> field_simp
  have h1 := h.whit p hp q hq (by rwa [abs_of_pos hl])
  rw [abs_of_pos hl] at h1
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]
  calc (q - p)⁻¹ * _ ≤ (q - p)⁻¹ * (η * (q - p)) := by gcongr
    _ = η := by field_simp

lemma Pars.kappa_right (h : Pars S φ ψ L η δW) {p q : ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p < q)
    (hd : q - p < δW) : ‖(q - p)⁻¹ • (φ q - φ p) - ψ q‖ ≤ η := by
  have hl : 0 < q - p := sub_pos.2 hpq
  have e : (q - p)⁻¹ • (φ q - φ p) - ψ q = -((q - p)⁻¹ • (φ p - φ q - (p - q) • ψ q)) := by
    have := hl.ne'
    rw [show p - q = -(q - p) by ring]
    match_scalars <;> field_simp
  have h1 := h.whit q hq p hp (by rw [abs_sub_comm, abs_of_pos hl]; exact hd)
  rw [abs_sub_comm, abs_of_pos hl] at h1
  rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]
  calc (q - p)⁻¹ * _ ≤ (q - p)⁻¹ * (η * (q - p)) := by gcongr
    _ = η := by field_simp

lemma Pars.kappa_bound (h : Pars S φ ψ L η δW) {p q : ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p < q) :
    ‖(q - p)⁻¹ • (φ q - φ p)‖ ≤ L := by
  have hl : 0 < q - p := sub_pos.2 hpq
  have h1 := h.lip p hp q hq
  rw [abs_of_pos hl] at h1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]
  calc (q - p)⁻¹ * _ ≤ (q - p)⁻¹ * (L * (q - p)) := by gcongr
    _ = L := by field_simp

/-- The derivative of the Hermite cubic on a gap `(p, q)` stays within `18 η` of `c` near the left
endpoint `p` when `‖ψ p - c‖ ≤ 2 η` (the two cases `q - p < δW` and `q - p ≥ δW`). -/
lemma Pars.gap_left (h : Pars S φ ψ L η δW) {p q t δ : ℝ} {c : E} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p < q) (ht : t ∈ Icc p q) (hc : ‖ψ p - c‖ ≤ 2 * η) (hδ : 16 * L * δ ≤ η * δW)
    (htd : t - p < δ) :
    ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - c‖ ≤ 18 * η := by
  have hl : 0 < q - p := sub_pos.2 hpq
  have hL : 0 ≤ L := (norm_nonneg _).trans (h.bdd p hp)
  have hθ0 : 0 ≤ (t - p) / (q - p) := div_nonneg (sub_nonneg.2 ht.1) hl.le
  have hθ1 : (t - p) / (q - p) ≤ 1 := (div_le_one hl).2 (by linarith [ht.2])
  have key : ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ p‖ ≤ 16 * η := by
    rcases lt_or_ge (q - p) δW with hd | hd
    · have := hermD_sub_left_le hpq ht (φ p) (φ q) (ψ p) (ψ q) (D := 2 * η)
        ((h.kappa_left hp hq hpq hd).trans (by linarith [h.hη]))
        (h.psi_close hp hq (by rwa [abs_of_pos hl]))
      refine this.trans ?_
      nlinarith [h.hη]
    · have hk := h.kappa_bound hp hq hpq
      have hb := h.bdd p hp
      have hb' := h.bdd q hq
      have := hermD_sub_left_le hpq ht (φ p) (φ q) (ψ p) (ψ q) (D := 2 * L)
        (by have := norm_sub_le ((q - p)⁻¹ • (φ q - φ p)) (ψ p); linarith)
        (by have := norm_sub_le (ψ q) (ψ p); linarith)
      refine this.trans ?_
      have hθ : (t - p) / (q - p) ≤ δ / δW := by
        exact div_le_div₀ (by linarith [ht.1]) htd.le h.hδW hd
      have h16 : 16 * L * (δ / δW) ≤ η := by
        rw [← mul_div_assoc, div_le_iff₀ h.hδW]; exact hδ
      nlinarith
  calc _ ≤ ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ p‖ + ‖ψ p - c‖ := by
        simpa using norm_add_le (hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ p) (ψ p - c)
    _ ≤ 18 * η := by linarith

/-- The derivative of the Hermite cubic stays within `18 η` of `c` near the right endpoint `q`. -/
lemma Pars.gap_right (h : Pars S φ ψ L η δW) {p q t δ : ℝ} {c : E} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p < q) (ht : t ∈ Icc p q) (hc : ‖ψ q - c‖ ≤ 2 * η) (hδ : 16 * L * δ ≤ η * δW)
    (htd : q - t < δ) :
    ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - c‖ ≤ 18 * η := by
  have hl : 0 < q - p := sub_pos.2 hpq
  have hL : 0 ≤ L := (norm_nonneg _).trans (h.bdd p hp)
  have hθ0 : 0 ≤ (t - p) / (q - p) := div_nonneg (sub_nonneg.2 ht.1) hl.le
  have hθ1 : (t - p) / (q - p) ≤ 1 := (div_le_one hl).2 (by linarith [ht.2])
  have hθe : 1 - (t - p) / (q - p) = (q - t) / (q - p) := by
    field_simp
    ring
  have key : ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ q‖ ≤ 16 * η := by
    rcases lt_or_ge (q - p) δW with hd | hd
    · have := hermD_sub_right_le hpq ht (φ p) (φ q) (ψ p) (ψ q) (D := 2 * η)
        ((h.kappa_right hp hq hpq hd).trans (by linarith [h.hη]))
        (by
          have := h.psi_close hp hq (by rwa [abs_of_pos hl])
          rw [← norm_neg]; simpa using this)
      refine this.trans ?_
      nlinarith [h.hη]
    · have hk := h.kappa_bound hp hq hpq
      have hb := h.bdd p hp
      have hb' := h.bdd q hq
      have := hermD_sub_right_le hpq ht (φ p) (φ q) (ψ p) (ψ q) (D := 2 * L)
        (by have := norm_sub_le ((q - p)⁻¹ • (φ q - φ p)) (ψ q); linarith)
        (by have := norm_sub_le (ψ p) (ψ q); linarith)
      refine this.trans ?_
      have hθ : 1 - (t - p) / (q - p) ≤ δ / δW := by
        rw [hθe]
        exact div_le_div₀ (by linarith [ht.2]) htd.le h.hδW hd
      have h16 : 16 * L * (δ / δW) ≤ η := by
        rw [← mul_div_assoc, div_le_iff₀ h.hδW]; exact hδ
      nlinarith
  calc _ ≤ ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ q‖ + ‖ψ q - c‖ := by
        simpa using norm_add_le (hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ q) (ψ q - c)
    _ ≤ 18 * η := by linarith

end Lusin

end AFree
