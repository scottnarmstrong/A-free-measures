module

public import AFree.Curves.Defs
public import AFree.Curves.Vec
public import AFree.Curves.ConeCalc
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Independent cones

Cones around nearly independent axes with small apertures contain linearly independent vectors.
-/

@[expose] public section

open Set

namespace AFree

open PDE

variable {d : ℕ}

private lemma vecEuclideanNorm_sum_le (a : Fin d → ℝ) (v : Fin d → Vec d) :
    vecEuclideanNorm (∑ j, a j • v j) ≤ ∑ j, |a j| * vecEuclideanNorm (v j) := by
  have key : ∀ s : Finset (Fin d),
      vecEuclideanNorm (∑ j ∈ s, a j • v j) ≤ ∑ j ∈ s, |a j| * vecEuclideanNorm (v j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [vecEuclideanNorm, vecNormSq, vecDot]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      refine (vecEuclideanNorm_add_le _ _).trans ?_
      rw [vecEuclideanNorm_smul]
      linarith
  exact key Finset.univ

private lemma sum_abs_le_sqrt_mul (a : Vec d) :
    ∑ j, |a j| ≤ Real.sqrt d * vecEuclideanNorm a := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun j => |a j|)
  simp only [sq_abs, Finset.card_univ, Fintype.card_fin] at h
  rw [vecEuclideanNorm, ← Real.sqrt_mul (Nat.cast_nonneg d), vecNormSq_eq_sum_sq]
  exact Real.le_sqrt_of_sq_le h

/-- Let `w_j` be unit vectors and `η > 0` with `|Σ a_j w_j| ≥ η |a|`, and
`β_j ∈ (0, π/2)` with `√d β_j < η`. Then any `u_j ∈ C(w_j, β_j) ∖ {0}` are linearly independent,
hence span `ℝ^d`. -/
theorem indep_cones {w : Fin d → Vec d} (hw : ∀ j, vecEuclideanNorm (w j) = 1) {η : ℝ}
    (hlow : ∀ a : Vec d, η * vecEuclideanNorm a ≤ vecEuclideanNorm (∑ j, a j • w j))
    {β : Fin d → ℝ} (hβ : ∀ j, 0 < β j ∧ β j < Real.pi / 2) (hβη : ∀ j, Real.sqrt d * β j < η)
    {u : Fin d → Vec d} (hu : ∀ j, u j ∈ cone (w j) (β j)) (hu0 : ∀ j, u j ≠ 0) :
    LinearIndependent ℝ u ∧ Submodule.span ℝ (range u) = ⊤ := by
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro b hb
    have hpos : ∀ j, 0 < vecEuclideanNorm (u j) := fun j =>
      vecEuclideanNorm_pos_iff.2 (hu0 j)
    set a : Vec d := fun j => b j * vecEuclideanNorm (u j) with ha
    set uh : Fin d → Vec d := fun j => (vecEuclideanNorm (u j))⁻¹ • u j with huh
    have huh1 : ∀ j, vecEuclideanNorm (uh j) = 1 := fun j => by
      rw [huh]; dsimp only
      rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 (hpos j)), inv_mul_cancel₀ (hpos j).ne']
    have huhc : ∀ j, uh j ∈ cone (w j) (β j) := fun j =>
      cone_smul_mem (hu j) (inv_nonneg.2 (hpos j).le)
    have hsum0 : ∑ j, a j • uh j = 0 := by
      have : ∀ j, a j • uh j = b j • u j := fun j => by
        rw [ha, huh]; dsimp only
        rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos j).ne', mul_one]
      simp_rw [this]
      exact hb
    have hdist : ∀ j, vecEuclideanNorm (w j - uh j) ≤ β j := fun j => by
      have := (cone_calculus (hw j) (hβ j).1 (hβ j).2).2.2.1 (w j) (uh j) (β j) (hw j) (huh1 j)
        (hβ j).1 (hβ j).2 (huhc j)
      rw [vecEuclideanNorm_sub_comm]
      exact this.1.trans this.2
    have hwsum : ∑ j, a j • w j = ∑ j, a j • (w j - uh j) := by
      have : ∑ j, a j • (w j - uh j) = ∑ j, a j • w j - ∑ j, a j • uh j := by
        simp [smul_sub, Finset.sum_sub_distrib]
      rw [this, hsum0, sub_zero]
    by_contra hne
    obtain ⟨j₀, hj₀⟩ := not_forall.1 hne
    have ha0 : a j₀ ≠ 0 := mul_ne_zero hj₀ (hpos j₀).ne'
    have hd : 0 < (d : ℝ) := by
      have : 0 < d := Fin.pos j₀
      exact_mod_cast this
    have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
    have h1 := hlow a
    have h2 : vecEuclideanNorm (∑ j, a j • w j) ≤ ∑ j, |a j| * β j := by
      rw [hwsum]
      refine (vecEuclideanNorm_sum_le a _).trans (Finset.sum_le_sum fun j _ => ?_)
      exact mul_le_mul_of_nonneg_left (hdist j) (abs_nonneg _)
    have h3 : ∑ j, |a j| * β j < ∑ j, |a j| * (η / Real.sqrt d) := by
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₀, Finset.mem_univ _, ?_⟩
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [le_div_iff₀ hsq]; linarith [hβη j, mul_comm (β j) (Real.sqrt d)]
      · refine mul_lt_mul_of_pos_left ?_ (abs_pos.2 ha0)
        rw [lt_div_iff₀ hsq]; linarith [hβη j₀, mul_comm (β j₀) (Real.sqrt d)]
    have h4 : ∑ j, |a j| * (η / Real.sqrt d) ≤ η * vecEuclideanNorm a := by
      rw [← Finset.sum_mul]
      calc (∑ j, |a j|) * (η / Real.sqrt d) ≤ (Real.sqrt d * vecEuclideanNorm a) * (η / Real.sqrt d) := by
            gcongr
            · exact div_nonneg (by nlinarith [hβη j₀, (hβ j₀).1]) hsq.le
            · exact sum_abs_le_sqrt_mul a
        _ = η * vecEuclideanNorm a := by field_simp
    linarith
  refine ⟨hli, ?_⟩
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)

/-- A member of an orthonormal family is a unit vector. -/
lemma vecEuclideanNorm_eq_one_of_orthonormal {e : Fin d → Vec d}
    (he : ∀ i j, vecDot (e i) (e j) = if i = j then 1 else 0) (j : Fin d) :
    vecEuclideanNorm (e j) = 1 := by
  have := he j j
  simpa [vecEuclideanNorm, vecNormSq, vecDot] using this

/-- For orthonormal `e_j`, `|Σ a_j e_j| = |a|`. -/
lemma vecEuclideanNorm_sum_smul_orthonormal {e : Fin d → Vec d}
    (he : ∀ i j, vecDot (e i) (e j) = if i = j then 1 else 0) (a : Vec d) :
    vecEuclideanNorm (∑ j, a j • e j) = vecEuclideanNorm a := by
  have h : vecNormSq (∑ j, a j • e j) = vecNormSq a := by
    simp only [vecNormSq_eq_sum_sq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hd : ∀ i j : Fin d, ∑ k, e i k * e j k = if i = j then 1 else 0 := fun i j => by
      simpa [vecDot] using he i j
    calc ∑ k, (∑ j, a j * e j k) ^ 2
        = ∑ k, ∑ i, ∑ j, (a i * a j) * (e i k * e j k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, ∑ j, (a i * a j) * ∑ k, e i k * e j k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, a i ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [hd, sq]
  rw [vecEuclideanNorm, vecEuclideanNorm, h]

end AFree
