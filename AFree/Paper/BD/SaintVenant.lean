module

public import AFree.Defs

/-!
# The Saint-Venant operator

The tensor `T_{ab} ∈ ℝ^{κ×ι}` with `κ = (Fin d)^4`, `ι = (Fin d)^2`, and the family
`A_α = Σ_{e_a+e_b=α} T_{ab}` (`A_α = 0` for `|α| ≠ 2`), as in the proof of [DPR, Theorem 1.7].
-/

@[expose] public section

open Matrix

namespace AFree

variable {d : ℕ}

/-- `(T_{ab})_{(ijkl),(pq)} = δ_{ja}δ_{lb}δ_{pi}δ_{qk} + δ_{ia}δ_{kb}δ_{pj}δ_{ql}
- δ_{ia}δ_{lb}δ_{pj}δ_{qk} - δ_{ja}δ_{kb}δ_{pi}δ_{ql}`. -/
noncomputable def saintVenantT (a b : Fin d) :
    Matrix (Fin d × Fin d × Fin d × Fin d) (Fin d × Fin d) ℝ :=
  Matrix.of fun r c =>
    (if r.2.1 = a ∧ r.2.2.2 = b ∧ c.1 = r.1 ∧ c.2 = r.2.2.1 then 1 else 0) +
    (if r.1 = a ∧ r.2.2.1 = b ∧ c.1 = r.2.1 ∧ c.2 = r.2.2.2 then 1 else 0) -
    (if r.1 = a ∧ r.2.2.2 = b ∧ c.1 = r.2.1 ∧ c.2 = r.2.2.1 then 1 else 0) -
    (if r.2.1 = a ∧ r.2.2.1 = b ∧ c.1 = r.1 ∧ c.2 = r.2.2.2 then 1 else 0)

/-- The Saint-Venant family `A_α = Σ_{(a,b) : e_a+e_b=α} T_{ab}` (zero unless `|α| = 2`). -/
noncomputable def saintVenant (α : Fin d → ℕ) :
    Matrix (Fin d × Fin d × Fin d × Fin d) (Fin d × Fin d) ℝ :=
  ∑ a, ∑ b, if (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) = α then saintVenantT a b else 0

theorem sum_antidiagonalTuple_two {X : Type*} [AddCommMonoid X]
    (G : (Fin d → ℕ) → Fin d → Fin d → X) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple d 2, ∑ a, ∑ b,
        (if (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) = α then G α a b else 0) =
      ∑ a, ∑ b, G (Pi.single a 1 + Pi.single b 1) a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hm : (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) ∈ Finset.Nat.antidiagonalTuple d 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp [Finset.sum_add_distrib, Pi.single_apply]
  simp [hm]

theorem saintVenant_eq_zero_of_ne {h : ℕ} (hh : h ≠ 2) {α : Fin d → ℕ}
    (hα : α ∈ Finset.Nat.antidiagonalTuple d h) : saintVenant α = 0 := by
  unfold saintVenant
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have : (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) ≠ α := by
    rintro rfl
    rw [Finset.Nat.mem_antidiagonalTuple] at hα
    apply hh
    rw [← hα]
    simp [Finset.sum_add_distrib, Pi.single_apply]
  simp [this]

theorem prod_pow_single_add (ξ : Fin d → ℝ) (a b : Fin d) :
    ∏ i, ξ i ^ ((Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) i) = ξ a * ξ b := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  simp [Pi.single_apply, pow_ite]

/-- The symbol `Σ_{|α|=2} ξ^α A_α = Σ_{a,b} ξ_a ξ_b T_{ab}`. -/
theorem sum_symbol_saintVenant (ξ : Fin d → ℝ) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple d 2, (∏ i, ξ i ^ α i) • saintVenant α =
      ∑ a, ∑ b, (ξ a * ξ b) • saintVenantT a b := by
  have : ∀ α, (∏ i, ξ i ^ α i) • saintVenant α =
      ∑ a, ∑ b, if (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) = α then
        (∏ i, ξ i ^ α i) • saintVenantT a b else 0 := by
    intro α
    unfold saintVenant
    simp only [Finset.smul_sum, smul_ite, smul_zero]
  simp only [this]
  rw [sum_antidiagonalTuple_two (fun α a b => (∏ i, ξ i ^ α i) • saintVenantT a b)]
  simp only [prod_pow_single_add]

/-- Components of `Σ_{a,b} T_{ab} W_{ab}`. -/
theorem sum_saintVenantT_mulVec (W : Fin d → Fin d → Fin d × Fin d → ℝ) (i j k l : Fin d) :
    (∑ a, ∑ b, saintVenantT a b *ᵥ W a b) (i, j, k, l) =
      W j l (i, k) + W i k (j, l) - W i l (j, k) - W j k (i, l) := by
  simp only [Finset.sum_apply, saintVenantT, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Fintype.sum_prod_type]
  simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_and]

end AFree
