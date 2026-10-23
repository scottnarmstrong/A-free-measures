module

public import AFree.Paper.BD.Calculus
public import AFree.Paper.BD.SaintVenant

/-!
# `Eu` is free for the Saint-Venant operator

The symmetrised gradient of a BD function is free for the Saint-Venant operator, as used in the proof
of [DPR, Theorem 1.7].
-/

public section

open MeasureTheory PDE Matrix

namespace AFree

variable {d : ℕ}

namespace BD

section Triple

variable {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a b c : Fin d)

include hφ

theorem triple_swap12 :
    euclideanCoordDeriv a (euclideanCoordDeriv b (euclideanCoordDeriv c φ)) =
      euclideanCoordDeriv b (euclideanCoordDeriv a (euclideanCoordDeriv c φ)) :=
  coordDeriv_comm (contDiff_euclideanCoordDeriv hφ c) a b

theorem triple_swap23 :
    euclideanCoordDeriv a (euclideanCoordDeriv b (euclideanCoordDeriv c φ)) =
      euclideanCoordDeriv a (euclideanCoordDeriv c (euclideanCoordDeriv b φ)) := by
  rw [coordDeriv_comm hφ b c]

/-- Third derivatives are symmetric: `∂_a∂_b∂_c φ = ∂_c∂_b∂_a φ`. -/
theorem triple_rev :
    euclideanCoordDeriv a (euclideanCoordDeriv b (euclideanCoordDeriv c φ)) =
      euclideanCoordDeriv c (euclideanCoordDeriv b (euclideanCoordDeriv a φ)) := by
  rw [triple_swap12 hφ a b c, triple_swap23 hφ b a c, triple_swap12 hφ b c a]

end Triple

end BD

open BD

/-- The `(ijkl)` component of the free-sum for the vector `W_{ab} = ∫ ∂_b∂_a φ dEu`. -/
theorem sum_saintVenantT_integral_eq_zero {Ω : Set (Vec d)} {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu)
    {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Ω φ) :
    ∑ a, ∑ b, saintVenantT a b *ᵥ
        (∫ᵛ x, euclideanCoordDeriv b (euclideanCoordDeriv a φ) x ∂•Eu) = 0 := by
  funext r
  obtain ⟨i, j, k, l⟩ := r
  rw [sum_saintVenantT_mulVec (fun a b => ∫ᵛ x, euclideanCoordDeriv b
    (euclideanCoordDeriv a φ) x ∂•Eu)]
  have hs := hφ.1
  have key : ∀ a b p q, (∫ᵛ x, euclideanCoordDeriv b (euclideanCoordDeriv a φ) x ∂•Eu) (p, q) =
      -((∫ x in Ω, u x p * euclideanCoordDeriv q (euclideanCoordDeriv b
          (euclideanCoordDeriv a φ)) x) +
        ∫ x in Ω, u x q * euclideanCoordDeriv p (euclideanCoordDeriv b
          (euclideanCoordDeriv a φ)) x) / 2 := fun a b p q =>
    integral_eq_of_isBDGradientOn hEu (isTest_D (isTest_D hφ a) b) p q
  rw [key, key, key, key]
  have e1 := triple_swap12 hs k l j
  have e2 := triple_rev hs i l j
  have e3 := triple_swap12 hs l k i
  have e4 := triple_rev hs j k i
  rw [e1, e2, e3, e4]
  simp only [Pi.zero_apply]
  ring

/-- If `Eu` is the symmetrised gradient of `u ∈ BD(Ω)`, then `Eu` is free for the
Saint-Venant operator `saintVenant` of order `2` (`IsFree Ω 2 saintVenant Eu`). The first claim of
the lemma, `|Eu|(Ωᶜ) = 0`, is part of `IsBDGradientOn` (`hEu.2.1`). -/
theorem isFree_saintVenant_of_isBDGradientOn {Ω : Set (Vec d)} {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu) :
    IsFree Ω 2 saintVenant Eu := by
  intro φ hφ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 : ∀ h, h ≠ 2 → ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
      (-1 : ℝ) ^ h • (saintVenant α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•Eu) = 0 := fun h hh =>
    Finset.sum_eq_zero fun α hα => by
      rw [saintVenant_eq_zero_of_ne hh hα, Matrix.zero_mulVec, smul_zero]
  rw [h0 0 (by norm_num), h0 1 (by norm_num), zero_add, zero_add]
  have e : ∀ α, (-1 : ℝ) ^ 2 • (saintVenant α *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•Eu) =
      ∑ a, ∑ b, if (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) = α then
        saintVenantT a b *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•Eu else 0 := by
    intro α
    simp only [saintVenant, Matrix.sum_mulVec, Finset.smul_sum, apply_ite (fun M : Matrix _ _ ℝ =>
      M *ᵥ ∫ᵛ x, multiCoordDeriv α φ x ∂•Eu), Matrix.zero_mulVec]
    simp
  simp only [e]
  rw [sum_antidiagonalTuple_two (fun α a b => saintVenantT a b *ᵥ
    ∫ᵛ x, multiCoordDeriv α φ x ∂•Eu)]
  have e2 : ∀ a b, multiCoordDeriv (Pi.single a 1 + Pi.single b 1 : Fin d → ℕ) φ =
      euclideanCoordDeriv b (euclideanCoordDeriv a φ) := fun a b => multiCoordDeriv_two a b hφ.1
  simp only [e2]
  rw [zero_add]
  exact sum_saintVenantT_integral_eq_zero hEu hφ

end AFree
