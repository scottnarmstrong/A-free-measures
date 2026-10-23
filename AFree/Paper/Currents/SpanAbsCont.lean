module

public import AFree.Paper.Currents.Covector
public import AFree.Algebra.KVec.Equiv

/-!
# Corollary 1.12: one-dimensional normal currents

[DPR, Corollary 1.12], deduced from [DPR, Theorem 1.10] with `kᵢ = 1`: a covector annihilating all polars cannot exist where they span `ℝᵈ`.
-/

public section

open MeasureTheory Matrix

namespace AFree

open PDE

/-- [DPR, Corollary 1.12]: if `μ ≪ |Tᵢ|` for `d` normal `1`-currents on `ℝᵈ` whose
polars span `ℝᵈ` `μ`-a.e., then `μ ≪ vol`. -/
theorem absolutelyContinuous_of_span_polar_eq_top {d : ℕ}
    (T : Fin d → VectorMeasure (Vec d) (KVec d 1))
    (hT : ∀ i, IsNormalCurrentOn Set.univ (T i))
    (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ i, μ ≪ euclideanVariation (T i))
    (hspan : ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤) :
    μ ≪ volume := by
  refine (Measure.singularPart_eq_zero μ volume).1 ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact singularPart_eq_zero_of_dimZero μ
  -- Step 1: [DPR, Theorem 1.10] with `Ω = ℝᵈ`, `kᵢ = 1`
  have h1 := ae_exists_covector_interiorProduct_eq_zero Set.univ isOpen_univ (fun _ => 1)
    (fun _ => ⟨le_rfl, hd⟩) T hT μ (by simp) (fun K hK _ => hK.measure_lt_top) hμ
  -- Step 2: `μˢ = 0`
  have h2 : ∀ᵐ x ∂μ.singularPart volume, False := by
    have hle : μ.singularPart volume ≪ μ :=
      Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)
    filter_upwards [h1, hle.ae_le hspan] with x ⟨ω, hω, h⟩ hs
    refine hω ?_
    have hvan : ∀ w ∈ Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)),
        vecDot w ω = 0 := by
      intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨i, rfl⟩
        exact ((oneip (polar (T i) x) ω).2).1 (h i)
      · simp [vecDot]
      · intro a b _ _ ha hb
        simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      · intro c a _ ha
        simp only [vecDot, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at *
        rw [ha, mul_zero]
    have h0 := hvan ω (hs ▸ Submodule.mem_top)
    have hsq : ∀ j, ω j * ω j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (ω j))).1 h0 j
        (Finset.mem_univ j)
      exact this
    funext j
    exact mul_self_eq_zero.1 (hsq j)
  have : μ.singularPart volume Set.univ = 0 := by simpa [ae_iff] using h2
  exact Measure.measure_univ_eq_zero.1 this

end AFree
