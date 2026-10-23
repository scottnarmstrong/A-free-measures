module

public import AFree.Curves.Vec
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cone calculus

Elementary properties of the cone `C(e, α)`.
-/

@[expose] public section

open Set
open scoped Topology

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ}

lemma cone_isClosed (e : Vec d) (α : ℝ) : IsClosed (cone e α) :=
  isClosed_le (continuous_const.mul continuous_vecEuclideanNorm) (continuous_vecDot_left e)

lemma cone_smul_mem {v : Vec d} (hv : v ∈ cone e α) {r : ℝ} (hr : 0 ≤ r) :
    r • v ∈ cone e α := by
  show _ ≤ _
  have h : Real.cos α * vecEuclideanNorm v ≤ vecDot v e := hv
  rw [vecEuclideanNorm_smul, vecDot_smul_left, abs_of_nonneg hr]
  nlinarith

lemma cone_convex (e : Vec d) {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    Convex ℝ (cone e α) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  intro u hu v hv a b ha hb _
  have hu' : Real.cos α * vecEuclideanNorm u ≤ vecDot u e := hu
  have hv' : Real.cos α * vecEuclideanNorm v ≤ vecDot v e := hv
  show _ ≤ _
  have h1 := vecEuclideanNorm_add_le (a • u) (b • v)
  rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h1
  rw [vecDot_add_left, vecDot_smul_left, vecDot_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left hu' ha, mul_le_mul_of_nonneg_left hv' hb,
    mul_le_mul_of_nonneg_left h1 hc.le]

lemma cone_iff (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2) (v : Vec d) :
    v ∈ cone e α ↔
      0 ≤ vecDot v e ∧ vecEuclideanNorm (v - vecDot v e • e) ≤ Real.tan α * vecDot v e := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have ht : Real.tan α = Real.sin α / Real.cos α := Real.tan_eq_sin_div_cos α
  have hsc : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have hpy := vecNormSq_sub_dot_smul he v
  have hn2 := vecEuclideanNorm_sq v
  have hw2 := vecEuclideanNorm_sq (v - vecDot v e • e)
  set s := vecDot v e with hs
  set n := vecEuclideanNorm v with hn
  set w := vecEuclideanNorm (v - s • e) with hw
  have hn0 : 0 ≤ n := vecEuclideanNorm_nonneg v
  have hw0 : 0 ≤ w := vecEuclideanNorm_nonneg _
  have hwn : w ^ 2 = n ^ 2 - s ^ 2 := by rw [hw2, hpy, hn2]
  show Real.cos α * n ≤ s ↔ 0 ≤ s ∧ w ≤ Real.tan α * s
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  constructor
  · intro h
    have hs0 : 0 ≤ s := by nlinarith
    refine ⟨hs0, ?_⟩
    have : w ^ 2 ≤ (Real.tan α * s) ^ 2 := by
      rw [ht, div_mul_eq_mul_div, div_pow, le_div_iff₀ (by positivity), hwn]
      have h2 : (Real.cos α * n) ^ 2 ≤ s ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h
      nlinarith
    exact le_of_sq_le_sq (by simpa using this) (by rw [ht]; positivity)
  · rintro ⟨hs0, h⟩
    have h2 : w ^ 2 ≤ (Real.tan α * s) ^ 2 := pow_le_pow_left₀ hw0 h 2
    rw [ht, div_mul_eq_mul_div, div_pow, le_div_iff₀ (by positivity), hwn] at h2
    have h3 : (Real.cos α * n) ^ 2 ≤ s ^ 2 := by nlinarith
    exact le_of_sq_le_sq (by simpa using h3) hs0

lemma cone_inter_neg {v : Vec d} (hα : 0 < α) (hα2 : α < Real.pi / 2) (h1 : v ∈ cone e α)
    (h2 : -v ∈ cone e α) : v = 0 := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have h1' : Real.cos α * vecEuclideanNorm v ≤ vecDot v e := h1
  have h2' : Real.cos α * vecEuclideanNorm (-v) ≤ vecDot (-v) e := h2
  have hneg : vecDot (-v) e = - vecDot v e := by
    have : -v = (-1 : ℝ) • v := by simp
    rw [this, vecDot_smul_left]; ring
  rw [vecEuclideanNorm_neg, hneg] at h2'
  have : vecEuclideanNorm v ≤ 0 := by nlinarith [vecEuclideanNorm_nonneg v]
  exact vecEuclideanNorm_eq_zero_iff.mp (le_antisymm this (vecEuclideanNorm_nonneg v))

lemma norm_le_of_mem_cone {v : Vec d} (hα : 0 < α) (hα2 : α < Real.pi / 2) (hv : v ∈ cone e α) :
    vecEuclideanNorm v ≤ vecDot v e / Real.cos α := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  rw [le_div_iff₀ hc]
  have h : Real.cos α * vecEuclideanNorm v ≤ vecDot v e := hv
  linarith

lemma norm_sub_le_of_mem_cone {u w : Vec d} {β : ℝ} (hw : vecEuclideanNorm w = 1)
    (hu : vecEuclideanNorm u = 1) (hβ : 0 < β) (hβ2 : β < Real.pi / 2) (huc : u ∈ cone w β) :
    vecEuclideanNorm (u - w) ≤ 2 * Real.sin (β / 2) ∧ 2 * Real.sin (β / 2) ≤ β := by
  have hs : 0 ≤ Real.sin (β / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hcos : Real.cos β = 1 - 2 * Real.sin (β / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (β / 2)
    have h3 := Real.sin_sq_add_cos_sq (β / 2)
    rw [show 2 * (β / 2) = β by ring] at h2
    nlinarith
  refine ⟨?_, by linarith [Real.sin_le (show 0 ≤ β / 2 by linarith)]⟩
  apply vecEuclideanNorm_le_of_sq (by positivity)
  have h1 : Real.cos β * 1 ≤ vecDot u w := by
    have : Real.cos β * vecEuclideanNorm u ≤ vecDot u w := huc
    rwa [hu] at this
  have hu2 : vecNormSq u = 1 := by have := vecEuclideanNorm_sq u; rw [hu] at this; linarith
  have hw2 : vecNormSq w = 1 := by have := vecEuclideanNorm_sq w; rw [hw] at this; linarith
  have : vecNormSq (u - w) = vecNormSq u - 2 * vecDot u w + vecNormSq w := by
    show vecDot (u - w) (u - w) = _
    rw [vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_comm w u]
    unfold vecNormSq; ring
  rw [this, hu2, hw2]
  nlinarith

/-- Countable polar description of the cone. -/
lemma cone_eq_iInter_polar (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    ∃ D : Set (Vec d), D.Countable ∧ (∀ ℓ ∈ D, ∀ b ∈ cone e α, vecDot ℓ b ≤ 0) ∧
      cone e α = ⋂ ℓ ∈ D, {v | vecDot ℓ v ≤ 0} := by
  let P : Set (Vec d) := {ℓ | ∀ b ∈ cone e α, vecDot ℓ b ≤ 0}
  obtain ⟨D, hDP, hDc, hDd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace P).exists_countable_dense_subset
  refine ⟨D, hDc, fun ℓ hℓ => hDP hℓ, ?_⟩
  apply Set.Subset.antisymm
  · intro v hv
    simp only [mem_iInter]
    exact fun ℓ hℓ => hDP hℓ v hv
  · intro v hv
    by_contra hvC
    obtain ⟨f, u, hfv, hfb⟩ := geometric_hahn_banach_point_closed (cone_convex e hα hα2)
      (cone_isClosed e α) hvC
    let ℓ : Vec d := fun i => - f (Pi.single i 1)
    have hrep : ∀ x : Vec d, - f x = vecDot ℓ x := by
      intro x
      have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Vec d) := by
        refine (pi_eq_sum_univ x).trans (Finset.sum_congr rfl fun i _ => ?_)
        congr 1; funext j; simp [Pi.single_apply, eq_comm]
      conv_lhs => rw [hx]
      simp [vecDot, ℓ, map_sum, Finset.sum_neg_distrib, mul_comm]
    have h0 : (0 : Vec d) ∈ cone e α := by
      show Real.cos α * vecEuclideanNorm 0 ≤ vecDot 0 e
      simp [vecEuclideanNorm, vecNormSq, vecDot]
    have hu0 : u < 0 := by simpa using hfb 0 h0
    have hlb : ∀ b ∈ cone e α, vecDot ℓ b < -u := by
      intro b hb; have := hfb b hb; rw [← hrep]; linarith
    have hℓP : ℓ ∈ P := by
      intro b hb
      by_contra hpos
      push Not at hpos
      obtain ⟨N, hN⟩ := exists_nat_gt ((-u) / vecDot ℓ b)
      have := hlb ((N : ℝ) • b) (cone_smul_mem hb (Nat.cast_nonneg N))
      rw [vecDot_smul_right] at this
      rw [div_lt_iff₀ hpos] at hN
      linarith
    have hlv : 0 < vecDot ℓ v := by
      have := hfv; rw [← hrep] at *; linarith
    have hopen : IsOpen {x : Vec d | 0 < vecDot x v} :=
      isOpen_lt continuous_const (continuous_vecDot_left v)
    obtain ⟨ℓ', hℓ'o, hℓ'D⟩ := mem_closure_iff.mp (hDd hℓP) _ hopen hlv
    have := mem_iInter₂.mp hv ℓ' hℓ'D
    have h2 : vecDot ℓ' v ≤ 0 := this
    have h3 : 0 < vecDot ℓ' v := hℓ'o
    linarith

/-- Cone calculus for `C = C(e, α)`, `|e| = 1`, `α ∈ (0, π/2)`:
(a) `C` is a closed convex cone, `C ∩ (-C) = {0}`, and `v ∈ C ↔ v ⬝ e ≥ 0 ∧ |v_W| ≤ tan α (v ⬝ e)`;
(b) `|v| ≤ (v ⬝ e) / cos α` on `C`;
(c) unit `u ∈ C(w, β)`, `|w| = 1`, `β ∈ (0, π/2)` gives `|u - w| ≤ 2 sin (β/2) ≤ β`;
(d) `C = ⋂_{ℓ ∈ D} {ℓ ⬝ v ≤ 0}` for a countable `D` in the polar cone `C° = {ℓ : ℓ ⬝ C ≤ 0}`. -/
theorem cone_calculus (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2) :
    (IsClosed (cone e α) ∧ Convex ℝ (cone e α) ∧ (∀ v ∈ cone e α, ∀ r : ℝ, 0 ≤ r → r • v ∈ cone e α) ∧
      (∀ v, v ∈ cone e α → -v ∈ cone e α → v = 0) ∧
      ∀ v : Vec d, v ∈ cone e α ↔
        0 ≤ vecDot v e ∧ vecEuclideanNorm (v - vecDot v e • e) ≤ Real.tan α * vecDot v e) ∧
    (∀ v ∈ cone e α, vecEuclideanNorm v ≤ vecDot v e / Real.cos α) ∧
    (∀ (w u : Vec d) (β : ℝ), vecEuclideanNorm w = 1 → vecEuclideanNorm u = 1 → 0 < β →
      β < Real.pi / 2 → u ∈ cone w β →
        vecEuclideanNorm (u - w) ≤ 2 * Real.sin (β / 2) ∧ 2 * Real.sin (β / 2) ≤ β) ∧
    ∃ D : Set (Vec d), D.Countable ∧ (∀ ℓ ∈ D, ∀ b ∈ cone e α, vecDot ℓ b ≤ 0) ∧
      cone e α = ⋂ ℓ ∈ D, {v | vecDot ℓ v ≤ 0} :=
  ⟨⟨cone_isClosed e α, cone_convex e hα hα2, fun _ hv _ hr => cone_smul_mem hv hr,
      fun _ h1 h2 => cone_inter_neg hα hα2 h1 h2, cone_iff he hα hα2⟩,
    fun _ hv => norm_le_of_mem_cone hα hα2 hv,
    fun _ _ _ hw hu hβ hβ2 huc => norm_sub_le_of_mem_cone hw hu hβ hβ2 huc,
    cone_eq_iInter_polar hα hα2⟩

end AFree
