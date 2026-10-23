module

public import AFree.Measure.Mollify
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Concentration of singular measures under mollification

A finite measure singular to Lebesgue measure concentrates, after mollification, on sets of small Lebesgue measure. The proof uses inner regularity of the measure, outer regularity of Lebesgue measure, Urysohn's lemma, the Fubini identity and the uniform convergence of the mollifications.
-/

public section

open MeasureTheory Filter Topology Set PDE

namespace AFree

/-- Let `lam` be a finite measure singular to Lebesgue measure, `U` open, `δ > 0`.
There are an open `W ⊆ U` with `|W| < δ` and `ε₀ > 0` such that
`lam U ≤ ∫_W lam_ε dx + δ` for all `ε ∈ (0, ε₀]`. -/
theorem concentration {d : ℕ} (lam : Measure (Vec d)) [IsFiniteMeasure lam]
    (hs : lam ⟂ₘ (volume : Measure (Vec d))) {U : Set (Vec d)} (hU : IsOpen U) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ W : Set (Vec d), IsOpen W ∧ W ⊆ U ∧ volume W < ENNReal.ofReal δ ∧
      ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
        (lam U).toReal ≤ (∫ x in W, mollifyMeasure ε lam x) + δ := by
  obtain ⟨S, hSm, hS0, hSc⟩ := hs
  have hA : MeasurableSet (U ∩ Sᶜ) := hU.measurableSet.inter hSm.compl
  have hAeq : lam (U ∩ Sᶜ) = lam U := by
    apply measure_inter_conull
    simpa using hS0
  obtain ⟨K, hKA, hKc, hK⟩ := hA.exists_isCompact_lt_add (measure_ne_top lam _)
    (ENNReal.ofReal_pos.2 (half_pos hδ)).ne'
  have hKvol : volume K = 0 :=
    measure_mono_null (hKA.trans inter_subset_right) hSc
  obtain ⟨V, hKV, hVo, hV⟩ := Set.exists_isOpen_lt_of_lt K (ENNReal.ofReal δ)
    (by rw [hKvol]; exact ENNReal.ofReal_pos.2 hδ)
  have hW : IsOpen (V ∩ U) := hVo.inter hU
  have hKW : K ⊆ V ∩ U := fun x hx => ⟨hKV hx, (hKA hx).1⟩
  obtain ⟨ψ, hψ1, hψ0, hψc, hψI⟩ := exists_continuous_one_zero_of_isCompact hKc
    hW.isClosed_compl (disjoint_compl_right_iff_subset.2 hKW)
  have hψm : Measurable (ψ : Vec d → ℝ) := ψ.continuous.measurable
  have hψb : ∀ x, |(ψ : Vec d → ℝ) x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hψI x).1]; exact (hψI x).2
  set M : ℝ := lam.real univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  obtain ⟨ε₀, hε₀, hε⟩ := exists_forall_abs_integral_mul_sub_le ψ.continuous hψc
    (η := δ / (2 * (M + 1))) (by positivity)
  refine ⟨V ∩ U, hW, inter_subset_right, lt_of_le_of_lt (measure_mono inter_subset_left) hV,
    ε₀, hε₀, fun ε hεI => ?_⟩
  have hε0 : 0 < ε := hεI.1
  -- Fubini
  have hF := integral_mul_mollifyMeasure hε0 lam hψm hψb
  have hgint := integrable_integral_mul_scaledMollifier hε0 lam hψm hψb
  have hψint : Integrable (ψ : Vec d → ℝ) lam := ψ.continuous.integrable_of_hasCompactSupport hψc
  have hdiff : ‖∫ y, ((∫ x, ψ x * scaledMollifier ε (x - y)) - ψ y) ∂lam‖ ≤ δ / 2 := by
    have := norm_integral_le_of_norm_le_const (μ := lam)
      (f := fun y => (∫ x, ψ x * scaledMollifier ε (x - y)) - ψ y)
      (C := δ / (2 * (M + 1))) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hε ε hεI y)
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hM0, hδ]
  rw [integral_sub hgint hψint] at hdiff
  have hdiff' : -(δ / 2) ≤ (∫ y, (∫ x, (ψ : Vec d → ℝ) x * scaledMollifier ε (x - y)) ∂lam)
      - ∫ y, (ψ : Vec d → ℝ) y ∂lam :=
    (abs_le.1 (by simpa only [Real.norm_eq_abs] using hdiff)).1
  -- compare with the indicator of `K`
  have hKint : (lam K).toReal ≤ ∫ y, (ψ : Vec d → ℝ) y ∂lam := by
    have h1 : ∫ y, K.indicator (1 : Vec d → ℝ) y ∂lam = lam.real K :=
      integral_indicator_one hKc.measurableSet
    rw [← Measure.real] at *
    rw [← h1]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hKc.measurableSet) hψint
      fun y => ?_
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, Pi.one_apply, hψ1 hy]; simp
    · rw [Set.indicator_of_notMem hy]; exact (hψI y).1
  have hUK : (lam U).toReal ≤ (lam K).toReal + δ / 2 := by
    have h2 : lam U ≤ lam K + ENNReal.ofReal (δ / 2) := by rw [← hAeq]; exact hK.le
    have := ENNReal.toReal_mono (by finiteness) h2
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (half_pos hδ).le] at this
  -- compare with the integral over `W`
  have hm : Integrable (fun x => mollifyMeasure ε lam x) := by
    simpa using integrable_mul_mollifyMeasure hε0 lam (ψ := fun _ => (1 : ℝ)) measurable_const
      (C := 1) (fun _ => by simp)
  have hψm' := integrable_mul_mollifyMeasure hε0 lam hψm hψb
  have hWle : ∫ x, (ψ : Vec d → ℝ) x * mollifyMeasure ε lam x ≤
      ∫ x in V ∩ U, mollifyMeasure ε lam x := by
    rw [← integral_indicator hW.measurableSet]
    refine integral_mono hψm' (hm.indicator hW.measurableSet) fun x => ?_
    by_cases hx : x ∈ V ∩ U
    · rw [Set.indicator_of_mem hx]
      exact mul_le_of_le_one_left (mollifyMeasure_nonneg hε0.le _ _) (hψI x).2
    · rw [Set.indicator_of_notMem hx, hψ0 (by exact hx)]; simp
  rw [hF] at hWle
  have e1 : (lam U).toReal ≤ (∫ y, (ψ : Vec d → ℝ) y ∂lam) + δ / 2 := by linarith
  have e2 : (∫ y, (ψ : Vec d → ℝ) y ∂lam) ≤
      (∫ y, (∫ x, (ψ : Vec d → ℝ) x * scaledMollifier ε (x - y)) ∂lam) + δ / 2 := by linarith
  have e3 : (∫ y, (∫ x, (ψ : Vec d → ℝ) x * scaledMollifier ε (x - y)) ∂lam) ≤
      ∫ x in V ∩ U, mollifyMeasure ε lam x := hWle
  linarith

end AFree
