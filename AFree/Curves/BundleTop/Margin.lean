module

public import AFree.Curves.BundleTop.Setup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Margins of independence

A tuple `u` has margin `η` if `|Σ aⱼ uⱼ| ≥ η |a|` for all coefficient vectors `a`.
-/

@[expose] public section

open Set Filter Topology

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d k : ℕ}

/-- The tuple `u` has margin `η`: `η |a| ≤ |Σ aⱼ uⱼ|` for every `a`. -/
def Margin (η : ℝ) (u : Fin k → Vec d) : Prop :=
  ∀ a : Vec k, η * vecEuclideanNorm a ≤ vecEuclideanNorm (∑ j, a j • u j)

lemma Margin.mono {η η' : ℝ} {u : Fin k → Vec d} (h : Margin η u) (h' : η' ≤ η) :
    Margin η' u := fun a =>
  (mul_le_mul_of_nonneg_right h' (vecEuclideanNorm_nonneg a)).trans (h a)

lemma Margin.linearIndependent {η : ℝ} {u : Fin k → Vec d} (hη : 0 < η) (h : Margin η u) :
    LinearIndependent ℝ u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have := h g
  rw [hg] at this
  have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
  rw [h0] at this
  have : vecEuclideanNorm g ≤ 0 := by nlinarith [vecEuclideanNorm_nonneg g]
  have hg0 : vecEuclideanNorm g = 0 := le_antisymm this (vecEuclideanNorm_nonneg g)
  intro j
  exact congrFun (vecEuclideanNorm_eq_zero_iff.1 hg0) j

lemma isClosed_margin (η : ℝ) : IsClosed {u : Fin k → Vec d | Margin η u} := by
  have : {u : Fin k → Vec d | Margin η u} =
      ⋂ a : Vec k, {u | η * vecEuclideanNorm a ≤ vecEuclideanNorm (∑ j, a j • u j)} := by
    ext u; simp [Margin]
  rw [this]
  refine isClosed_iInter fun a => isClosed_le continuous_const ?_
  exact continuous_vecEuclideanNorm.comp
    (continuous_finsetSum _ fun j _ => (continuous_apply j).const_smul (a j))

lemma vecEuclideanNorm_sum_le' {ι : Type*} (s : Finset ι) (f : ι → Vec d) :
    vecEuclideanNorm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, vecEuclideanNorm (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vecEuclideanNorm, vecNormSq, vecDot]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (vecEuclideanNorm_add_le _ _).trans (by linarith)

/-- Perturbing the vectors of a tuple with margin `η` keeps margin `3η/4`. -/
lemma Margin.perturb {η ε : ℝ} {v u : Fin k → Vec d} (h : Margin η v)
    (hε : (k : ℝ) * ε ≤ η / 4) (hu : ∀ j, vecEuclideanNorm (u j - v j) ≤ ε) :
    Margin (3 * η / 4) u := by
  intro a
  have hsplit : ∑ j, a j • u j = ∑ j, a j • v j + ∑ j, a j • (u j - v j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_sub]; abel
  have h1 : vecEuclideanNorm (∑ j, a j • (u j - v j)) ≤ (k : ℝ) * ε * vecEuclideanNorm a := by
    refine (vecEuclideanNorm_sum_le' _ _).trans ?_
    have : ∀ j, vecEuclideanNorm (a j • (u j - v j)) ≤ vecEuclideanNorm a * ε := fun j => by
      rw [vecEuclideanNorm_smul]
      exact mul_le_mul (abs_apply_le_vecEuclideanNorm a j) (hu j) (vecEuclideanNorm_nonneg _)
        (vecEuclideanNorm_nonneg _)
    refine (Finset.sum_le_sum fun j _ => this j).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf; exact le_rfl
  have h2 : vecEuclideanNorm (∑ j, a j • v j) ≤
      vecEuclideanNorm (∑ j, a j • u j) + vecEuclideanNorm (∑ j, a j • (u j - v j)) := by
    have := vecEuclideanNorm_add_le (∑ j, a j • u j) (-∑ j, a j • (u j - v j))
    rw [vecEuclideanNorm_neg] at this
    have e : ∑ j, a j • u j + -∑ j, a j • (u j - v j) = ∑ j, a j • v j := by
      rw [hsplit]; abel
    rwa [e] at this
  have h3 := h a
  have h4 := vecEuclideanNorm_nonneg a
  nlinarith [mul_le_mul_of_nonneg_right hε h4]

/-- A linearly independent tuple has a positive margin. -/
lemma exists_margin_of_linearIndependent {u : Fin k → Vec d} (hu : LinearIndependent ℝ u) :
    ∃ η : ℝ, 0 < η ∧ Margin η u := by
  set S : Set (Vec k) := {a | vecEuclideanNorm a = 1} with hS
  have hSc : IsCompact S := isCompact_sphere
  set g : Vec k → ℝ := fun a => vecEuclideanNorm (∑ j, a j • u j) with hg
  have hgc : Continuous g := continuous_vecEuclideanNorm.comp
    (continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const)
  by_cases hne : S.Nonempty
  · obtain ⟨a0, ha0, hmin⟩ := hSc.exists_isMinOn hne hgc.continuousOn
    have hpos : 0 < g a0 := by
      rw [hg]; dsimp only
      refine vecEuclideanNorm_pos_iff.2 fun h0 => ?_
      have := Fintype.linearIndependent_iff.1 hu a0 h0
      have : a0 = 0 := funext this
      rw [this] at ha0
      have h0' : vecEuclideanNorm (0 : Vec k) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      simp [hS, h0'] at ha0
    refine ⟨g a0, hpos, fun a => ?_⟩
    by_cases ha : a = 0
    · subst ha
      have h0' : vecEuclideanNorm (0 : Vec k) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      rw [h0', mul_zero]; exact vecEuclideanNorm_nonneg _
    · have hn : 0 < vecEuclideanNorm a := vecEuclideanNorm_pos_iff.2 ha
      set b : Vec k := (vecEuclideanNorm a)⁻¹ • a with hb
      have hbS : b ∈ S := by
        show vecEuclideanNorm b = 1
        rw [hb, vecEuclideanNorm_smul, abs_inv, abs_of_pos hn]
        exact inv_mul_cancel₀ hn.ne'
      have h1 := hmin hbS
      have hgb : g b = (vecEuclideanNorm a)⁻¹ * g a := by
        simp only [hg, hb]
        have : ∑ j, ((vecEuclideanNorm a)⁻¹ • a) j • u j =
            (vecEuclideanNorm a)⁻¹ • ∑ j, a j • u j := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => by simp [smul_smul]
        rw [this, vecEuclideanNorm_smul, abs_inv, abs_of_pos hn]
      have h2 : g a0 ≤ (vecEuclideanNorm a)⁻¹ * g a := by rw [← hgb]; exact h1
      calc g a0 * vecEuclideanNorm a ≤ ((vecEuclideanNorm a)⁻¹ * g a) * vecEuclideanNorm a :=
            mul_le_mul_of_nonneg_right h2 hn.le
        _ = g a := by field_simp
  · refine ⟨1, one_pos, fun a => ?_⟩
    by_cases ha : a = 0
    · subst ha
      have h0' : vecEuclideanNorm (0 : Vec k) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      rw [h0', mul_zero]; exact vecEuclideanNorm_nonneg _
    · exfalso
      apply hne
      have hn : 0 < vecEuclideanNorm a := vecEuclideanNorm_pos_iff.2 ha
      refine ⟨(vecEuclideanNorm a)⁻¹ • a, ?_⟩
      show vecEuclideanNorm ((vecEuclideanNorm a)⁻¹ • a) = 1
      rw [vecEuclideanNorm_smul, abs_inv, abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'

end AFree.BundleTop
