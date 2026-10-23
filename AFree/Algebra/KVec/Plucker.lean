module

public import AFree.Algebra.KVec.Basic

/-!
# The Plücker obstruction in `Λ₂(ℝ⁵)`

The `2`-vector `P₀ = (√2)⁻¹ (e₀₁ + e₂₃)` is not simple; this is used in the counterexample of [DPR, Remark 1.11].
-/

@[expose] public section

open Matrix PDE

namespace AFree

variable {d : ℕ}

/-- The index `{i, j} ∈ KIdx d 2` for `i < j`. -/
def pairIdx (i j : Fin d) (h : i < j) : KIdx d 2 := ⟨{i, j}, Finset.card_pair (ne_of_lt h)⟩

theorem orderEmbOfFin_pair (i j : Fin d) (h : i < j) :
    (pairIdx i j h).1.orderEmbOfFin (pairIdx i j h).2 0 = i ∧
      (pairIdx i j h).1.orderEmbOfFin (pairIdx i j h).2 1 = j := by
  have hf : (![i, j] : Fin 2 → Fin d) = (pairIdx i j h).1.orderEmbOfFin (pairIdx i j h).2 := by
    refine Finset.orderEmbOfFin_unique (pairIdx i j h).2 (fun x => ?_) ?_
    · fin_cases x <;> simp [pairIdx]
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
  exact ⟨by rw [← hf]; rfl, by rw [← hf]; rfl⟩

theorem wedge_pair (v : Fin 2 → Vec d) (i j : Fin d) (h : i < j) :
    wedge v (pairIdx i j h) = v 0 i * v 1 j - v 0 j * v 1 i := by
  obtain ⟨h0, h1⟩ := orderEmbOfFin_pair i j h
  rw [wedge_apply, Matrix.det_fin_two]
  simp only [wedgeMat, Matrix.of_apply, h0, h1]
  ring

/-- The Plücker relation for the coordinates of a wedge of two vectors, for four indices
`i₀ < i₁ < i₂ < i₃`. -/
theorem plucker_identity (v : Fin 2 → Vec d) (a b c e : Fin d) (hab : a < b) (hac : a < c)
    (hae : a < e) (hbc : b < c) (hbe : b < e) (hce : c < e) :
    wedge v (pairIdx a b hab) * wedge v (pairIdx c e hce)
      - wedge v (pairIdx a c hac) * wedge v (pairIdx b e hbe)
      + wedge v (pairIdx a e hae) * wedge v (pairIdx b c hbc) = 0 := by
  simp only [wedge_pair]
  ring

/-- The explicit `P₀ = (√2)⁻¹ (e₀₁ + e₂₃) ∈ Λ₂(ℝ⁵)` of the counterexample (`0`-based indices). -/
noncomputable def pluckerP0 : KVec 5 2 :=
  fun I => if I.1 = {0, 1} ∨ I.1 = {2, 3} then (Real.sqrt 2)⁻¹ else 0

/-- A `2`-vector of `ℝ⁵` with `w₀₁ w₂₃ - w₀₂ w₁₃ + w₀₃ w₁₂ ≠ 0` is not simple. -/
theorem not_isSimpleKVec_of_plucker_ne (w : KVec 5 2)
    (h : w (pairIdx 0 1 (by decide)) * w (pairIdx 2 3 (by decide))
      - w (pairIdx 0 2 (by decide)) * w (pairIdx 1 3 (by decide))
      + w (pairIdx 0 3 (by decide)) * w (pairIdx 1 2 (by decide)) ≠ 0) :
    ¬ IsSimpleKVec w := by
  rintro ⟨c, v, rfl⟩
  apply h
  simp only [Pi.smul_apply, smul_eq_mul]
  have := plucker_identity v 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  linear_combination c * c * this

/-- `P₀` is not simple. -/
theorem pluckerP0_not_isSimpleKVec : ¬ IsSimpleKVec pluckerP0 := by
  apply not_isSimpleKVec_of_plucker_ne
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h02 : ¬ (({0, 2} : Finset (Fin 5)) = {0, 1} ∨ ({0, 2} : Finset (Fin 5)) = {2, 3}) := by
    decide
  have h13 : ¬ (({1, 3} : Finset (Fin 5)) = {0, 1} ∨ ({1, 3} : Finset (Fin 5)) = {2, 3}) := by
    decide
  have h03 : ¬ (({0, 3} : Finset (Fin 5)) = {0, 1} ∨ ({0, 3} : Finset (Fin 5)) = {2, 3}) := by
    decide
  have h12 : ¬ (({1, 2} : Finset (Fin 5)) = {0, 1} ∨ ({1, 2} : Finset (Fin 5)) = {2, 3}) := by
    decide
  simp [pluckerP0, pairIdx, hs, h02, h13, h03, h12]

end AFree
