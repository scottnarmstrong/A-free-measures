module

public import AFree.Paper.OrderK.HarmonicBasic

/-!
# Symbol classes of the specific multipliers

Symbol classes. With `a(ξ) = (Σ_{|α|=k} ξ^α A_α) P₀`,
`q = (2π)^{2k} |a|²` and `D = 1 + q`, the symbols `m_{0,α,c}`, `m_1`, `m_{β,c}`.
-/

@[expose] public section

open MeasureTheory PDE MvPolynomial Matrix
open scoped ComplexConjugate

namespace AFree

noncomputable section

variable {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- `a(ξ) = (Σ_{|α|=k} ξ^α A_α) P₀ ∈ ℝ^κ` (the real symbol `𝔸_k(ξ) P₀`). -/
def symbA (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) : κ → ℝ :=
  (∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α) *ᵥ P₀

/-- `q(ξ) = (2π)^{2k} |a(ξ)|²`. -/
def symbQ (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) : ℝ :=
  (2 * Real.pi) ^ (2 * k) * ∑ c, symbA k A P₀ ξ c * symbA k A P₀ ξ c

/-- `m_1 = 1 / D`, `D = 1 + q`. -/
def m1Symb (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) : Vec d → ℂ :=
  fun ξ => (1 + (symbQ k A P₀ ξ : ℂ))⁻¹

/-- `m_{0,α,c} = (2π)^{2k} ξ^α a_c / D`. -/
def m0Symb (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (α : Fin d → ℕ) (c : κ) :
    Vec d → ℂ :=
  fun ξ => (((2 * Real.pi) ^ (2 * k) * (∏ i, ξ i ^ α i) * symbA k A P₀ ξ c /
    (1 + symbQ k A P₀ ξ) : ℝ) : ℂ)

/-- `γ_β = (-2πi)^k (2πi)^{|β|}`. -/
def gammaCoef (d k : ℕ) (β : Fin d → ℕ) : ℂ :=
  (-(2 * Real.pi * Complex.I)) ^ k * (2 * Real.pi * Complex.I) ^ (∑ i, β i)

/-- `m_{β,c} = γ_β ξ^β a_c / D`. -/
def mBetaSymb (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (β : Fin d → ℕ) (c : κ) :
    Vec d → ℂ :=
  fun ξ => gammaCoef d k β * (((∏ i, ξ i ^ β i) * symbA k A P₀ ξ c : ℝ) : ℂ) *
    (1 + (symbQ k A P₀ ξ : ℂ))⁻¹

omit [Fintype κ] in
theorem symbA_apply (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) (c : κ) :
    symbA k A P₀ ξ c = ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      (∏ i, ξ i ^ α i) * (A α *ᵥ P₀) c := by
  unfold symbA
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  simp [Matrix.smul_mulVec]

theorem prod_neg_pow (α : Fin d → ℕ) (ξ : Vec d) :
    ∏ i, (-ξ) i ^ α i = (-1) ^ (∑ i, α i) * ∏ i, ξ i ^ α i := by
  have : ∀ i, (-ξ) i ^ α i = (-1) ^ α i * ξ i ^ α i := fun i => by
    rw [Pi.neg_apply, neg_eq_neg_one_mul, mul_pow]
  simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

omit [Fintype κ] in
theorem symbA_neg (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) (c : κ) :
    symbA k A P₀ (-ξ) c = (-1) ^ k * symbA k A P₀ ξ c := by
  rw [symbA_apply, symbA_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [prod_neg_pow, (Finset.Nat.mem_antidiagonalTuple.1 hα)]
  ring

theorem symbQ_neg (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) :
    symbQ k A P₀ (-ξ) = symbQ k A P₀ ξ := by
  unfold symbQ
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [symbA_neg]
  have : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  linear_combination (symbA k A P₀ ξ c * symbA k A P₀ ξ c) * this

theorem symbQ_eq_norm_sq (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) :
    symbQ k A P₀ ξ = (2 * Real.pi) ^ (2 * k) * piEuclideanNorm (symbA k A P₀ ξ) ^ 2 := by
  unfold symbQ piEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun c _ => mul_self_nonneg _)]

theorem symbQ_nonneg (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) :
    0 ≤ symbQ k A P₀ ξ := by
  rw [symbQ_eq_norm_sq]; positivity

/-! ### Polynomial models -/

section Poly

variable (R : Type*) [CommRing R]

/-- The monomial `ξ^α` as a polynomial. -/
def monoPoly (α : Fin d → ℕ) : MvPolynomial (Fin d) R := ∏ i, X i ^ α i

theorem isHomogeneous_monoPoly (α : Fin d → ℕ) : (monoPoly R α).IsHomogeneous (∑ i, α i) :=
  IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow i (α i)

theorem eval_monoPoly (α : Fin d → ℕ) (f : Fin d → R) :
    eval f (monoPoly R α) = ∏ i, f i ^ α i := by
  simp [monoPoly]

variable [Algebra ℝ R]

/-- The polynomial `a_c(ξ) = Σ_α ξ^α (A_α P₀)_c`. -/
def aPoly (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (c : κ) :
    MvPolynomial (Fin d) R :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, C (algebraMap ℝ R ((A α *ᵥ P₀) c)) * monoPoly R α

omit [Fintype κ] in
theorem isHomogeneous_aPoly (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (c : κ) :
    (aPoly R k A P₀ c).IsHomogeneous k := by
  refine IsHomogeneous.sum _ _ _ fun α hα => ?_
  have := (isHomogeneous_monoPoly R α).C_mul (algebraMap ℝ R ((A α *ᵥ P₀) c))
  rwa [Finset.Nat.mem_antidiagonalTuple.1 hα] at this

omit [Fintype κ] in
theorem eval_aPoly_real (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (c : κ)
    (ξ : Vec d) : eval ξ (aPoly ℝ k A P₀ c) = symbA k A P₀ ξ c := by
  simp [aPoly, eval_monoPoly, symbA_apply, mul_comm]

omit [Fintype κ] in
theorem eval_aPoly_complex (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (c : κ)
    (ξ : Vec d) :
    eval (fun i => (ξ i : ℂ)) (aPoly ℂ k A P₀ c) = ((symbA k A P₀ ξ c : ℝ) : ℂ) := by
  simp [aPoly, eval_monoPoly, symbA_apply, mul_comm]

end Poly

/-- The real polynomial `q`. -/
def qPoly (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) : MvPolynomial (Fin d) ℝ :=
  C ((2 * Real.pi) ^ (2 * k)) * ∑ c, aPoly ℝ k A P₀ c * aPoly ℝ k A P₀ c

theorem eval_qPoly (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) :
    eval ξ (qPoly k A P₀) = symbQ k A P₀ ξ := by
  simp [qPoly, symbQ, eval_aPoly_real]

theorem isHomogeneous_qPoly (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) :
    (qPoly k A P₀).IsHomogeneous (2 * k) := by
  have h : (∑ c, aPoly ℝ k A P₀ c * aPoly ℝ k A P₀ c).IsHomogeneous (k + k) :=
    IsHomogeneous.sum _ _ _ fun c _ =>
      (isHomogeneous_aPoly ℝ k A P₀ c).mul (isHomogeneous_aPoly ℝ k A P₀ c)
  rw [two_mul]
  exact h.C_mul _

theorem IsSymbol.congr_order {s s' : ℝ} (h : s = s') {m : Vec d → ℂ} (hm : IsSymbol s m) :
    IsSymbol s' m := h ▸ hm

theorem isSymbol_polySymbol_of_isHomogeneous {p : MvPolynomial (Fin d) ℂ} {j : ℕ}
    (hp : p.IsHomogeneous j) : IsSymbol (j : ℝ) (polySymbol p) :=
  isSymbol_polySymbol p hp.totalDegree_le

theorem isSymbol_m1Symb (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ}
    (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ)) :
    IsSymbol (-(2 * k : ℝ)) (m1Symb k A P₀) := by
  have hlow : ∀ ξ : Vec d, (2 * Real.pi) ^ (2 * k) * c0 ^ 2 * vecEuclideanNorm ξ ^ (2 * k) ≤
      eval ξ (qPoly k A P₀) := fun ξ => by
    rw [eval_qPoly, symbQ_eq_norm_sq]
    have h1 := pow_le_pow_left₀ (by have := vecEuclideanNorm_nonneg ξ; positivity) (hell ξ) 2
    have h2 : (c0 * vecEuclideanNorm ξ ^ k) ^ 2 = c0 ^ 2 * vecEuclideanNorm ξ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, mul_comm k 2]
    rw [h2] at h1
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (2 * k)]
  have := isSymbol_inv_one_add (qPoly k A P₀) (isHomogeneous_qPoly k A P₀)
    (by positivity : 0 < (2 * Real.pi) ^ (2 * k) * c0 ^ 2) hlow
  have e : m1Symb k A P₀ = fun ξ => (1 + ((eval ξ (qPoly k A P₀) : ℝ) : ℂ))⁻¹ := by
    funext ξ
    simp [m1Symb, eval_qPoly]
  rw [e]
  exact this

/-! ### The order-`0` and negative-order symbols -/

theorem m0Symb_eq_mul (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (α : Fin d → ℕ)
    (c : κ) :
    m0Symb k A P₀ α c = polySymbol (C (((2 * Real.pi) ^ (2 * k) : ℝ) : ℂ) * monoPoly ℂ α *
      aPoly ℂ k A P₀ c) * m1Symb k A P₀ := by
  funext ξ
  simp only [m0Symb, m1Symb, polySymbol, Pi.mul_apply, map_mul, eval_C, eval_monoPoly,
    eval_aPoly_complex, div_eq_mul_inv]
  push_cast
  ring

theorem mBetaSymb_eq_mul (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ)
    (β : Fin d → ℕ) (c : κ) :
    mBetaSymb k A P₀ β c = polySymbol (C (gammaCoef d k β) * monoPoly ℂ β * aPoly ℂ k A P₀ c) *
      m1Symb k A P₀ := by
  funext ξ
  simp only [mBetaSymb, m1Symb, polySymbol, Pi.mul_apply, map_mul, eval_C, eval_monoPoly,
    eval_aPoly_complex]
  push_cast
  ring

theorem isSymbol_m0Symb (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ}
    (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    {α : Fin d → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple d k) (c : κ) :
    IsSymbol 0 (m0Symb k A P₀ α c) := by
  have hh : (C (((2 * Real.pi) ^ (2 * k) : ℝ) : ℂ) * monoPoly ℂ α *
      aPoly ℂ k A P₀ c).IsHomogeneous (0 + ∑ i, α i + k) :=
    (((isHomogeneous_C _ _).mul (isHomogeneous_monoPoly ℂ α)).mul (isHomogeneous_aPoly ℂ k A P₀ c))
  rw [Finset.Nat.mem_antidiagonalTuple.1 hα] at hh
  have h1 := isSymbol_polySymbol_of_isHomogeneous hh
  rw [m0Symb_eq_mul]
  exact (h1.mul (isSymbol_m1Symb k A P₀ hc0 hell)).congr_order (by push_cast; ring)

theorem isSymbol_mBetaSymb (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ}
    (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ))
    (β : Fin d → ℕ) (c : κ) :
    IsSymbol (((∑ i, β i : ℕ) : ℝ) - k) (mBetaSymb k A P₀ β c) := by
  have hh : (C (gammaCoef d k β) * monoPoly ℂ β * aPoly ℂ k A P₀ c).IsHomogeneous
      (0 + ∑ i, β i + k) :=
    (((isHomogeneous_C _ _).mul (isHomogeneous_monoPoly ℂ β)).mul (isHomogeneous_aPoly ℂ k A P₀ c))
  have h1 := isSymbol_polySymbol_of_isHomogeneous hh
  rw [mBetaSymb_eq_mul]
  exact (h1.mul (isSymbol_m1Symb k A P₀ hc0 hell)).congr_order (by push_cast; ring)

theorem m0Symb_neg (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {α : Fin d → ℕ}
    (hα : α ∈ Finset.Nat.antidiagonalTuple d k) (c : κ) (ξ : Vec d) :
    m0Symb k A P₀ α c (-ξ) = m0Symb k A P₀ α c ξ := by
  have hk := Finset.Nat.mem_antidiagonalTuple.1 hα
  simp only [m0Symb, prod_neg_pow, symbA_neg, symbQ_neg, hk]
  congr 1
  have : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  rw [div_left_inj' (by have := symbQ_nonneg k A P₀ ξ; positivity)]
  linear_combination ((2 * Real.pi) ^ (2 * k) * (∏ i, ξ i ^ α i) * symbA k A P₀ ξ c) * this

theorem m0Symb_im (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (α : Fin d → ℕ)
    (c : κ) (ξ : Vec d) : (m0Symb k A P₀ α c ξ).im = 0 := by
  exact Complex.ofReal_im _

/-- Symbol classes of the specific multipliers: with `|a(ξ)| ≥ c₀ |ξ|^k`,
(a) `q ≥ (2π)^{2k} c₀² |ξ|^{2k}` and `m_1 ∈ S^{-2k}`; (b) `m_{0,α,c} ∈ S⁰` is real valued and even,
hence `m(-ξ) = conj m(ξ)`; (c) `m_{β,c} ∈ S^{|β|-k} ⊆ S^{-1}` for `|β| ≤ k - 1`. -/
theorem lem_symbolsk (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) {c0 : ℝ}
    (hc0 : 0 < c0)
    (hell : ∀ ξ : Vec d, c0 * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ)) :
    ((∀ ξ : Vec d, (2 * Real.pi) ^ (2 * k) * c0 ^ 2 * vecEuclideanNorm ξ ^ (2 * k) ≤
        symbQ k A P₀ ξ) ∧ IsSymbol (-(2 * k : ℝ)) (m1Symb k A P₀)) ∧
    (∀ α ∈ Finset.Nat.antidiagonalTuple d k, ∀ c : κ, IsSymbol 0 (m0Symb k A P₀ α c) ∧
      (∀ ξ, (m0Symb k A P₀ α c ξ).im = 0) ∧ (∀ ξ, m0Symb k A P₀ α c (-ξ) = m0Symb k A P₀ α c ξ) ∧
      ∀ ξ, m0Symb k A P₀ α c (-ξ) = conj (m0Symb k A P₀ α c ξ)) ∧
    (∀ β : Fin d → ℕ, ∀ c : κ,
      IsSymbol (((∑ i, β i : ℕ) : ℝ) - k) (mBetaSymb k A P₀ β c) ∧
      (∑ i, β i + 1 ≤ k → IsSymbol (-1) (mBetaSymb k A P₀ β c))) := by
  refine ⟨⟨fun ξ => ?_, isSymbol_m1Symb k A P₀ hc0 hell⟩, fun α hα c => ?_, fun β c => ?_⟩
  · rw [symbQ_eq_norm_sq]
    have h1 := pow_le_pow_left₀ (by have := vecEuclideanNorm_nonneg ξ; positivity) (hell ξ) 2
    have h2 : (c0 * vecEuclideanNorm ξ ^ k) ^ 2 = c0 ^ 2 * vecEuclideanNorm ξ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, mul_comm k 2]
    rw [h2] at h1
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (2 * k)]
  · have heven := m0Symb_neg k A P₀ hα c
    refine ⟨isSymbol_m0Symb k A P₀ hc0 hell hα c, m0Symb_im k A P₀ α c, heven, fun ξ => ?_⟩
    rw [heven]
    exact (Complex.conj_eq_iff_im.2 (m0Symb_im k A P₀ α c ξ)).symm
  · refine ⟨isSymbol_mBetaSymb k A P₀ hc0 hell β c, fun hβ => ?_⟩
    refine (isSymbol_mBetaSymb k A P₀ hc0 hell β c).mono ?_
    have : ((∑ i, β i + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hβ
    push_cast at this ⊢
    linarith

end

end AFree
