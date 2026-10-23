module

public import AFree.Harmonic.Fourier

/-!
# Pointwise weighted bounds for the inverse Fourier transform of a Schwartz function

`(1 + ‖y‖)^N (‖F⁻¹ g y‖ + ‖∇ F⁻¹ g y‖)` is bounded by finitely many Schwartz seminorms of `g`,
with constants depending only on `d` and `N`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap NNReal

namespace AFree

noncomputable section

variable {d : ℕ}

theorem exists_vecFourierInv_weighted_le (d N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (g : 𝓢(Vec d, ℂ)) (y : Vec d),
      (1 + ‖y‖) ^ N * ‖vecFourierInv g y‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g ∧
      (1 + ‖y‖) ^ N * ‖fderiv ℝ (vecFourierInv g) y‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g := by
  let q : Seminorm ℂ 𝓢(Vec d, ℂ) :=
    ((Finset.Iic (N, 1)).sup (schwartzSeminormFamily ℂ (Vec d) ℂ)).comp
      (vecFourierInvCLM (d := d)).toLinearMap
  have hq : Continuous q :=
    (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ (Vec d) ℂ).continuous_seminorm i).comp
      (vecFourierInvCLM (d := d)).continuous
  obtain ⟨s, C, hC0, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Vec d) ℂ) q hq
  refine ⟨s, 2 ^ N * C, by positivity, fun g y => ?_⟩
  have h1 : q g ≤ C * (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g := hC g
  have e : ⇑(vecFourierInvCLM g) = vecFourierInv g := vecFourierInv_coe g
  have hs0 : 0 ≤ (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g := apply_nonneg _ _
  have key : ∀ n, n ≤ 1 → (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n (vecFourierInv g) y‖ ≤
      2 ^ N * C * (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g := by
    intro n hn
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 1)) (k := N) (n := n)
      le_rfl hn (vecFourierInvCLM g) y
    rw [e] at this
    refine this.trans ?_
    have h2 : (Finset.Iic (N, 1)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)
        (vecFourierInvCLM g) = q g := rfl
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine ⟨?_, ?_⟩
  · have := key 0 (by norm_num)
    simpa using this
  · have := key 1 le_rfl
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0)] at this
    simpa using this

end

end AFree
