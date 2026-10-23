module

public import AFree.Rademacher.Chain.Nondiff
public import AFree.Curves.Bundle
public import AFree.Curves.BundleTop

/-!
# Theorem 1.14 for finite measures, and for locally finite measures

The converse of Rademacher's theorem, first for finite and then for locally finite measures.
-/

@[expose] public section

open PDE MeasureTheory Set
open scoped ENNReal NNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- If `μ` is finite and every Lipschitz `f` is differentiable `μ`-a.e., then
`μ ≪ 𝓛^d`. -/
theorem thm_radfin (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    (hμ : ∀ f : Vec d → ℝ, (∃ K, LipschitzWith K f) → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x) :
    μ ≪ volume := by
  obtain ⟨V, hV⟩ := Bundle.bundle_exists μ
  have htop : ∀ᵐ x ∂μ, V x = ⊤ := by
    by_contra hne
    have hpos : 0 < μ {x | V x ≠ ⊤} := by
      refine pos_iff_ne_zero.2 fun h0 => hne ?_
      exact ae_iff.2 (by simpa using h0)
    obtain ⟨K, f, hf, Z, -, hZ, hnd⟩ := thm_nondiff hV.1 hpos
    have h := hμ f ⟨K, hf⟩
    have hsub : Z ⊆ {x | ¬ DifferentiableAt ℝ f x} := hnd
    have h0 : μ {x | ¬ DifferentiableAt ℝ f x} = 0 := ae_iff.1 h
    exact hZ.ne' (measure_mono_null hsub h0)
  exact absolutelyContinuous_of_decompBundle_eq_top μ V hV htop

/-- [DPR, Theorem 1.14]. If `μ` is locally finite and every Lipschitz `f` is
differentiable `μ`-a.e., then `μ ≪ 𝓛^d`. -/
theorem thm_rademacher (μ : Measure (Vec d)) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ f : Vec d → ℝ, (∃ K, LipschitzWith K f) → ∀ᵐ x ∂μ, DifferentiableAt ℝ f x) :
    μ ≪ volume := by
  intro A hA
  have hn : ∀ n : ℕ, μ (A ∩ Metric.closedBall (0 : Vec d) n) = 0 := by
    intro n
    have : IsFiniteMeasure (μ.restrict (Metric.closedBall (0 : Vec d) n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
    have hrad := thm_radfin (μ.restrict (Metric.closedBall (0 : Vec d) n))
      (fun f hf => ae_restrict_of_ae (hμ f hf))
    have := hrad hA
    rwa [Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet] at this
  have hcov : A ⊆ ⋃ n : ℕ, A ∩ Metric.closedBall (0 : Vec d) n := by
    intro x hx
    obtain ⟨n, hn'⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨n, hx, by simpa using hn'⟩
  exact measure_mono_null hcov (measure_iUnion_null hn)

end AFree.Rademacher
