module

public import AFree.Harmonic.Fourier

/-!
# `L¹` bound for the inverse Fourier transform of a Schwartz function

The `L¹` norm of `F⁻¹ g` is bounded by finitely many Schwartz seminorms of `g` (continuity of
`F⁻¹` and of the inclusion `𝓢 → L¹`), with constants depending only on `d`.
-/

@[expose] public section

open MeasureTheory PDE
open scoped SchwartzMap ENNReal NNReal

namespace AFree

noncomputable section

variable {d : ℕ}

/-- Uniform `L¹` bound: there are a finite set `s` of seminorm indices and `C ≥ 0` (depending only
on `d`) with `‖F⁻¹ g‖_{L¹} ≤ C · sup_{(k,n) ∈ s} p_{k,n}(g)`. -/
theorem exists_integral_norm_vecFourierInv_le (d : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ g : 𝓢(Vec d, ℂ),
      ∫ x, ‖vecFourierInv g x‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g := by
  have : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let T : 𝓢(Vec d, ℂ) →L[ℂ] MeasureTheory.Lp ℂ 1 (volume : Measure (Vec d)) :=
    SchwartzMap.toLpCLM ℂ ℂ 1 volume ∘L vecFourierInvCLM
  let q : Seminorm ℂ 𝓢(Vec d, ℂ) := (normSeminorm ℂ _).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC0, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Vec d) ℂ) q hq
  refine ⟨s, C, C.coe_nonneg, fun g => ?_⟩
  have h1 : q g ≤ (C • s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) g := hC g
  have h2 : q g = ∫ x, ‖vecFourierInv g x‖ := by
    change ‖T g‖ = _
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp (vecFourierInvCLM g) 1 volume] with x hx
    change ‖(SchwartzMap.toLp (vecFourierInvCLM g) 1 volume : Vec d → ℂ) x‖ = _
    rw [hx, vecFourierInvCLM_apply]
  rw [← h2]
  exact h1

end

end AFree
