module

public import AFree.Curves.Bundle.ACTest

/-!
# The `L^d` case of the decomposability bundle

The absolutely continuous case of [AM, Proposition 2.9(iii)]: see `AFree.bundle_ac`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

open Bundle.AC in
private theorem coord_mem_ae {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    {V : Vec d → Submodule ℝ (Vec d)} (hV : IsDecompTestField μ V) (i : Fin d) :
    ∀ᵐ x ∂μ, basisVec i ∈ V x := by
  rcases d with _ | n
  · exact i.elim0
  · have h : ∀ᵐ x ∂μ, ∀ m : ℕ, |x i| < (m : ℝ) → basisVec i ∈ V x :=
      ae_all_iff.2 fun m => slab_ae μ hμ hV i m
    filter_upwards [h] with x hx
    obtain ⟨m, hm⟩ := exists_nat_gt |x i|
    exact hx m hm

/-- The absolutely continuous case of [AM, Proposition 2.9(iii)]: if `μ` is finite, `μ ≪ vol` and
`V ∈ 𝒢_μ`, then `V = ⊤` `μ`-a.e. (Segments `E_t` along `e_i` over a Borel sampler of a
measure equivalent to `vol`, Fubini, and the `C¹`-arc test; the steps are
`Bundle.AC.family_isRectifiable` (setup, family) and `Bundle.AC.slab_ae` (test).) -/
theorem bundle_ac {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] (hμ : μ ≪ volume)
    {V : Vec d → Submodule ℝ (Vec d)} (hV : IsDecompTestField μ V) :
    ∀ᵐ x ∂μ, V x = ⊤ := by
  have h : ∀ᵐ x ∂μ, ∀ i : Fin d, basisVec i ∈ V x := ae_all_iff.2 (coord_mem_ae μ hμ hV)
  filter_upwards [h] with x hx
  refine eq_top_iff.2 fun v _ => ?_
  have : v = ∑ i, v i • basisVec i := by
    ext j; simp [Finset.sum_apply, basisVec_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)

end AFree
