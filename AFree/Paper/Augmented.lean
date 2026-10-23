module

public import AFree.Analysis.WaveCone

/-!
# The augmented operator

[DPR, Remark 1.3]: the equation `𝒜μ = σ` with a measure on the right-hand side is reduced to a homogeneous one for
the augmented operator `Ã(μ, σ) = 𝒜μ - σ`; its principal part ignores the `σ` component, so its
wave cone is the product of the wave cone of `𝒜` with the whole `σ`-space.
-/

@[expose] public section

open Matrix

namespace AFree

open PDE

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The first-order coefficients of the augmented operator:
`Ã_ℓ (P, Q) = A_ℓ P`. -/
def augmentedCoeff (A : Fin d → Matrix κ ι ℝ) : Fin d → Matrix κ (ι ⊕ κ) ℝ :=
  fun ℓ k => Sum.elim (A ℓ k) 0

/-- The zeroth-order coefficient of the augmented operator:
`Ã₀ (P, Q) = A₀ P - Q`. -/
def augmentedZeroth [DecidableEq κ] (A₀ : Matrix κ ι ℝ) : Matrix κ (ι ⊕ κ) ℝ :=
  fun k => Sum.elim (A₀ k) (fun k' => if k' = k then -1 else 0)

/-- `Ã_ℓ (P, Q) = A_ℓ P`. -/
theorem augmentedCoeff_mulVec (A : Fin d → Matrix κ ι ℝ) (ℓ : Fin d) (R : ι ⊕ κ → ℝ) :
    augmentedCoeff A ℓ *ᵥ R = A ℓ *ᵥ (fun i => R (Sum.inl i)) := by
  funext k
  simp [augmentedCoeff, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

/-- `Ã₀ (P, Q) = A₀ P - Q`. -/
theorem augmentedZeroth_mulVec [DecidableEq κ] (A₀ : Matrix κ ι ℝ) (R : ι ⊕ κ → ℝ) :
    augmentedZeroth A₀ *ᵥ R = A₀ *ᵥ (fun i => R (Sum.inl i)) - (fun k => R (Sum.inr k)) := by
  funext k
  simp [augmentedZeroth, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]

/-- `P̃ ∈ Λ_Ã` iff its `ι`-component lies in `Λ_𝒜`. -/
theorem mem_waveConeFirstOrder_augmentedCoeff_iff (A : Fin d → Matrix κ ι ℝ) (R : ι ⊕ κ → ℝ) :
    R ∈ waveConeFirstOrder (augmentedCoeff A) ↔
      (fun i => R (Sum.inl i)) ∈ waveConeFirstOrder A := by
  have h : ∀ ξ : Vec d, (∑ ℓ, ξ ℓ • augmentedCoeff A ℓ) *ᵥ R =
      (∑ ℓ, ξ ℓ • A ℓ) *ᵥ (fun i => R (Sum.inl i)) := by
    intro ξ
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, augmentedCoeff_mulVec]
  constructor
  · rintro ⟨ξ, h1, h2⟩
    exact ⟨ξ, h1, by rw [← h]; exact h2⟩
  · rintro ⟨ξ, h1, h2⟩
    exact ⟨ξ, h1, by rw [h]; exact h2⟩

end AFree
