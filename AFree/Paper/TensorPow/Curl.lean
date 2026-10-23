module

public import AFree.Defs

/-!
# The curl-type operator on `Dʳu`

The operator `𝒜` whose kernel contains the `r`-th derivatives, and its symbol (proof of [DPR, Theorem 1.6]).
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- Row index set `κ = Fin ℓ × (Fin r → Fin d) × Fin r × Fin d × Fin d` of the curl-type operator. -/
abbrev CurlrRow (ℓ d r : ℕ) := Fin ℓ × (Fin r → Fin d) × Fin r × Fin d × Fin d

/-- Column index set `ι = Fin ℓ × (Fin r → Fin d)` of `Dʳu`. -/
abbrev CurlrCol (ℓ d r : ℕ) := Fin ℓ × (Fin r → Fin d)

/-- The matrix `A_m ∈ ℝ^{κ × ι}` with
`(A_m)_{(k,α,h,i,j),(k',β)} = 1_{k'=k} (1_{β = α[h↦i]} 1_{m=j} - 1_{β = α[h↦j]} 1_{m=i})`. -/
def curlrCoeff (ℓ d r : ℕ) : Fin d → Matrix (CurlrRow ℓ d r) (CurlrCol ℓ d r) ℝ :=
  fun m row col => if col.1 = row.1 then
    ((if col.2 = Function.update row.2.1 row.2.2.1 row.2.2.2.1 ∧ m = row.2.2.2.2 then 1 else 0) -
      (if col.2 = Function.update row.2.1 row.2.2.1 row.2.2.2.2 ∧ m = row.2.2.2.1 then 1 else 0))
    else 0

/-- The action of a single `A_m`: at `(k,α,h,i,j)` it is
`1_{m=j} x(k, α[h↦i]) - 1_{m=i} x(k, α[h↦j])`. -/
theorem curlrCoeff_mulVec {ℓ d r : ℕ} (m : Fin d) (x : CurlrCol ℓ d r → ℝ)
    (k : Fin ℓ) (α : Fin r → Fin d) (h : Fin r) (i j : Fin d) :
    (curlrCoeff ℓ d r m *ᵥ x) (k, α, h, i, j) =
      (if m = j then x (k, Function.update α h i) else 0) -
        (if m = i then x (k, Function.update α h j) else 0) := by
  simp only [Matrix.mulVec, dotProduct, curlrCoeff, Fintype.sum_prod_type]
  simp [ite_and, sub_mul, Finset.sum_sub_distrib, ite_mul]

/-- For `w : Fin d → ℝ^ι`,
`(Σ_m A_m w_m)_{(k,α,h,i,j)} = w_j(k, α[h↦i]) - w_i(k, α[h↦j])`. -/
theorem curlrCoeff_sum_mulVec {ℓ d r : ℕ} (w : Fin d → CurlrCol ℓ d r → ℝ)
    (k : Fin ℓ) (α : Fin r → Fin d) (h : Fin r) (i j : Fin d) :
    (∑ m, curlrCoeff ℓ d r m *ᵥ w m) (k, α, h, i, j) =
      w j (k, Function.update α h i) - w i (k, Function.update α h j) := by
  simp only [Finset.sum_apply, curlrCoeff_mulVec]
  simp [Finset.sum_sub_distrib]

/-- For `ξ ∈ ℝ^d` and `P ∈ ℝ^ι`,
`((Σ_m ξ_m A_m) P)_{(k,α,h,i,j)} = ξ_j P(k, α[h↦i]) - ξ_i P(k, α[h↦j])`. -/
theorem curlrCoeff_symbol_mulVec {ℓ d r : ℕ} (ξ : Vec d) (P : CurlrCol ℓ d r → ℝ)
    (k : Fin ℓ) (α : Fin r → Fin d) (h : Fin r) (i j : Fin d) :
    ((∑ m, ξ m • curlrCoeff ℓ d r m) *ᵥ P) (k, α, h, i, j) =
      ξ j * P (k, Function.update α h i) - ξ i * P (k, Function.update α h j) := by
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, curlrCoeff_mulVec]
  simp [mul_sub, Finset.sum_sub_distrib]

end AFree
