module

public import AFree.Curves.Lemma31.Current
public import AFree.Curves.BundleTop
public import AFree.Curves.Bundle
public import AFree.Proofs.SpanAbsContProof

/-!
# [DPR, Lemma 3.1]

The two implications, (ii) ⇒ (i) through span-implies-absolute-continuity and (i) ⇒ (ii) through the
Gaussian currents, and the equivalence.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace AFree

open PDE

/-- (ii) ⇒ (i): the span condition gives `μ ≪ 𝓛^d` ([DPR, Corollary 1.12]); a bundle
exists and equals `⊤` `μ`-a.e. by `bundle_ac`. -/
theorem lemma31_ii_to_i {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    (T : Fin d → VectorMeasure (Vec d) (KVec d 1)) (hT : ∀ i, IsNormalCurrentOn Set.univ (T i))
    (hμ : ∀ i, μ ≪ euclideanVariation (T i))
    (hspan : ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤) :
    ∃ V, IsDecompBundle μ V ∧ ∀ᵐ x ∂μ, V x = ⊤ := by
  have hac : μ ≪ volume := SpanAbsContProof.result T hT μ hμ hspan
  obtain ⟨V, hV⟩ := Bundle.bundle_exists μ
  exact ⟨V, hV, bundle_ac μ hac hV.1⟩

/-- (i) ⇒ (ii), first step: `μ ≪ 𝓛^d` from
the cone-selection argument of `BundleTop`. -/
theorem lemma31_i_to_ii_absolute_continuity {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    (V : Vec d → Submodule ℝ (Vec d)) (hV : IsDecompBundle μ V) (htop : ∀ᵐ x ∂μ, V x = ⊤) :
    μ ≪ volume :=
  absolutelyContinuous_of_decompBundle_eq_top μ V hV htop

/-- [DPR, Lemma 3.1]: for a finite measure `μ`, some decomposability bundle equals `ℝ^d` `μ`-a.e.
iff there are normal `1`-currents `T₁, …, T_d` with `μ ≪ |Tᵢ|` whose polars span `ℝ^d` `μ`-a.e. -/
theorem lemma31 {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    (∃ V, IsDecompBundle μ V ∧ ∀ᵐ x ∂μ, V x = ⊤) ↔
      ∃ T : Fin d → VectorMeasure (Vec d) (KVec d 1), (∀ i, IsNormalCurrentOn Set.univ (T i)) ∧
        (∀ i, μ ≪ euclideanVariation (T i)) ∧
        ∀ᵐ x ∂μ, Submodule.span ℝ (Set.range fun i => kvecOneToVec (polar (T i) x)) = ⊤ := by
  constructor
  · rintro ⟨V, hV, htop⟩
    have hac := lemma31_i_to_ii_absolute_continuity μ V hV htop
    refine ⟨gaussCurrent, gaussian_normal, fun i => (gaussian_vector_measure i).2 μ hac,
      ?_⟩
    have hp : ∀ i, ∀ᵐ x ∂μ, kvecOneToVec (polar (gaussCurrent i) x) = basisVec i :=
      fun i => (gaussian_polar i).2 μ hac
    filter_upwards [ae_all_iff.2 hp] with x hx
    have : (Set.range fun i => kvecOneToVec (polar (gaussCurrent i) x)) =
        Set.range fun i : Fin d => basisVec i := by simp only [hx]
    rw [this, eq_top_iff]
    intro v _
    rw [← sum_smul_basisVec v]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨T, hT, hμ, hspan⟩
    exact lemma31_ii_to_i μ T hT hμ hspan

end AFree
