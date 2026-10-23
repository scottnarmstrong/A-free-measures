module

public import AFree.Defs
public import AFree.Algebra.KVec.Interior
public import AFree.Measure.Decomp.Blocks

/-!
# The system for a family of currents

For `Tᵢ` with values in `Λ_{kᵢ}` the block measures `𝐓`, `σ` of `(Tᵢ)`, `(Sᵢ)` satisfy `𝒜𝐓 = σ` for the
explicit operator `A_ℓ`; this is the reduction in the proof of [DPR, Theorem 1.10].
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {d r : ℕ}

/-- The coefficient `A_ℓ ∈ ℝ^{κ×ι}` with `ι = Σᵢ Λ_{kᵢ}-indices`,
`κ = Σᵢ Λ_{kᵢ-1}-indices`: entry `-sgn(ℓ,J)` at `(⟨i,J⟩,⟨i,J ∪ {ℓ}⟩)` for `ℓ ∉ J`. -/
noncomputable def systemCoeff (k : Fin r → ℕ) (ℓ : Fin d) :
    Matrix (Σ i, KIdx d (k i - 1)) (Σ i, KIdx d (k i)) ℝ :=
  fun a b => by
    classical
    exact if a.1 = b.1 ∧ ℓ ∉ a.2.1 ∧ b.2.1 = insert ℓ a.2.1 then -insertSign ℓ a.2.1 else 0

/-- Row formula for one coefficient matrix. -/
theorem systemCoeff_mulVec (k : Fin r → ℕ) (ℓ : Fin d) (x : (Σ i, KIdx d (k i)) → ℝ)
    (i : Fin r) (J : KIdx d (k i - 1)) :
    (systemCoeff k ℓ *ᵥ x) ⟨i, J⟩ =
      if ℓ ∉ J.1 then
        (if h : (insert ℓ J.1).card = k i then
          -(insertSign ℓ J.1 * x ⟨i, ⟨insert ℓ J.1, h⟩⟩) else 0) else 0 := by
  classical
  simp only [mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · by_cases hℓ : ℓ ∉ J.1
    · by_cases h : (insert ℓ J.1).card = k i
      · simp only [hℓ, h, not_false_eq_true, ↓reduceIte, ↓reduceDIte]
        rw [Finset.sum_eq_single ⟨insert ℓ J.1, h⟩]
        · simp [systemCoeff, hℓ]
        · intro b _ hb
          have : ¬ b.1 = insert ℓ J.1 := fun e => hb (Subtype.ext e)
          simp [systemCoeff, this]
        · simp
      · simp only [hℓ, h, not_false_eq_true, ↓reduceIte, ↓reduceDIte]
        refine Finset.sum_eq_zero fun b _ => ?_
        have : ¬ b.1 = insert ℓ J.1 := fun e => h (e ▸ b.2)
        simp [systemCoeff, this]
    · simp only [hℓ, ↓reduceIte]
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [systemCoeff, hℓ]
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [systemCoeff, Ne.symm hj]
  · simp

/-- `(Σ_ℓ A_ℓ w_ℓ)_{⟨i,J⟩} = -Σ_{ℓ∉J} sgn(ℓ,J) w_ℓ⟨i,J ∪ {ℓ}⟩`. -/
theorem systemCoeff_sum_mulVec (k : Fin r → ℕ) (w : Fin d → (Σ i, KIdx d (k i)) → ℝ)
    (i : Fin r) (J : KIdx d (k i - 1)) :
    (∑ ℓ, systemCoeff k ℓ *ᵥ w ℓ) ⟨i, J⟩ =
      -∑ ℓ ∈ Finset.univ.filter (· ∉ J.1),
        if h : (insert ℓ J.1).card = k i then
          insertSign ℓ J.1 * w ℓ ⟨i, ⟨insert ℓ J.1, h⟩⟩ else 0 := by
  rw [Finset.sum_apply, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [systemCoeff_mulVec]
  by_cases hℓ : ℓ ∉ J.1
  · by_cases h : (insert ℓ J.1).card = k i
    · simp only [hℓ, h, not_false_eq_true, ↓reduceIte, ↓reduceDIte]
    · simp only [hℓ, h, not_false_eq_true, ↓reduceIte, ↓reduceDIte, neg_zero]
  · simp [hℓ]

/-- `((Σ_ℓ ξ_ℓ A_ℓ) P)_{⟨i,J⟩} = -(P_i ⌟ ξ)(J)`. -/
theorem systemCoeff_symbol_mulVec (k : Fin r → ℕ) (ξ : Vec d) (P : (Σ i, KIdx d (k i)) → ℝ)
    (i : Fin r) (J : KIdx d (k i - 1)) :
    ((∑ ℓ, ξ ℓ • systemCoeff k ℓ) *ᵥ P) ⟨i, J⟩ =
      -interiorProduct (fun I : KIdx d (k i) => P ⟨i, I⟩) ξ J := by
  have : (∑ ℓ, ξ ℓ • systemCoeff k ℓ) *ᵥ P = ∑ ℓ, systemCoeff k ℓ *ᵥ (ξ ℓ • P) := by
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [smul_mulVec, mulVec_smul]
  rw [this, systemCoeff_sum_mulVec, interiorProduct]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : (insert ℓ J.1).card = k i
  · simp only [h, ↓reduceDIte, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [h, ↓reduceDIte]

/-- The symbol identity and the wave cone: `P ∈ Λ_A` iff some unit `ξ` has
`P_i ⌟ ξ = 0` for all `i`. -/
theorem mem_waveConeFirstOrder_systemCoeff_iff (k : Fin r → ℕ) (P : (Σ i, KIdx d (k i)) → ℝ) :
    P ∈ waveConeFirstOrder (systemCoeff k) ↔
      ∃ ξ : Vec d, vecEuclideanNorm ξ = 1 ∧
        ∀ i, interiorProduct (fun I : KIdx d (k i) => P ⟨i, I⟩) ξ = 0 := by
  refine exists_congr fun ξ => and_congr_right fun _ => ?_
  constructor
  · intro h i
    funext J
    have := congrFun h ⟨i, J⟩
    rw [systemCoeff_symbol_mulVec] at this
    simpa using this
  · intro h
    funext a
    obtain ⟨i, J⟩ := a
    rw [systemCoeff_symbol_mulVec, h i]
    simp

end AFree
