module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Measure.BallVolume
public import AFree.Analysis.Bump

/-!
# The Vitali lemma [DPR, Lemma 2.2]

The negative part `f⁻` is the
explicit `max (-f x) 0`. The conclusion `f_j → 0` in `L¹_loc(B₁)` is
`tendsto_setIntegral_abs_of_vitali`.
-/

public section

open MeasureTheory Filter Topology PDE
open scoped ENNReal

namespace AFree

/-- [DPR, Lemma 2.2] in the reduced form (2.15) of its proof: under (a), (b), (c), `∫ ψ |f_j| → 0` for cutoffs `0 ≤ ψ ≤ 1` with
`tsupport ψ ⊆ B₁`. Negative part is `max (-f j x) 0`. -/
theorem tendsto_integral_mul_abs_of_vitali {d : ℕ} (f : ℕ → Vec d → ℝ)
    (hint : ∀ j, IntegrableOn (f j) (euclideanBall (0 : Vec d) 1))
    (ha : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanBall (0 : Vec d) 1 →
      Tendsto (fun j => ∫ x, ψ x * f j x) atTop (𝓝 0))
    (hb : ∀ l : ℝ, 0 < l →
      Tendsto (fun j => volume {x ∈ euclideanBall (0 : Vec d) 1 | l < max (-f j x) 0})
        atTop (𝓝 0))
    (hc : UnifIntegrable (fun j => fun x => max (-f j x) 0) 1
      (volume.restrict (euclideanBall (0 : Vec d) 1))) :
    ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanBall (0 : Vec d) 1 → (∀ x, 0 ≤ ψ x) → (∀ x, ψ x ≤ 1) →
      Tendsto (fun j => ∫ x, ψ x * |f j x|) atTop (𝓝 0) := by
  intro ψ hψsmooth hψk hψs hψ0 hψ1
  have hψc : Continuous ψ := hψsmooth.continuous
  set B := euclideanBall (0 : Vec d) 1 with hB
  have hBm : MeasurableSet B := measurableSet_euclideanBall _ _
  have hBfin : volume B ≠ ∞ := volume_euclideanBall_ne_top _ zero_le_one
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hBfin⟩
  set μ := volume.restrict B with hμ
  have hfm : ∀ j, MemLp (f j) 1 μ := fun j => memLp_one_iff_integrable.2 (hint j)
  set g : ℕ → Vec d → ℝ := fun j x => max (-f j x) 0 with hg
  have hgi : ∀ j, Integrable (g j) μ := fun j => (hint j).neg.pos_part
  have hgnn : ∀ j x, 0 ≤ g j x := fun j x => le_max_right _ _
  -- convergence in measure to zero
  have hmeas : TendstoInMeasure μ g atTop (fun _ => (0 : ℝ)) := by
    intro ε hε
    rcases eq_or_ne ε ∞ with rfl | hεt
    · simp
    · set l : ℝ := ε.toReal with hl
      have hlpos : 0 < l := ENNReal.toReal_pos hε.ne' hεt
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hb (l / 2) (by linarith))
        (fun _ => bot_le) (fun j => ?_)
      rw [hμ, Measure.restrict_apply' hBm]
      refine measure_mono (fun x hx => ⟨hx.2, ?_⟩)
      have h1 : ε ≤ edist (g j x) 0 := hx.1
      simp only [edist_dist, Real.dist_eq, sub_zero] at h1
      rw [abs_of_nonneg (hgnn j x)] at h1
      have h2 : ε.toReal ≤ g j x := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        rwa [ENNReal.toReal_ofReal (hgnn j x)] at this
      show l / 2 < g j x
      linarith
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure (μ := μ) (p := 1) le_rfl ENNReal.one_ne_top
    (fun j => (hgi j).aestronglyMeasurable) (MemLp.zero) hc hmeas
  have hint0 : Tendsto (fun j => ∫ x, g j x ∂μ) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
    simp only [ENNReal.toReal_zero] at this
    refine this.congr (fun j => ?_)
    show (eLpNorm (g j - 0) 1 μ).toReal = _
    rw [sub_zero, eLpNorm_one_eq_lintegral_enorm]
    rw [integral_eq_lintegral_of_nonneg_ae (μ := μ) (f := g j)
      (Filter.Eventually.of_forall (hgnn j)) (hgi j).aestronglyMeasurable]
    refine congrArg ENNReal.toReal (lintegral_congr (fun x => ?_))
    rw [← ofReal_norm, Real.norm_of_nonneg (hgnn j x)]
    · exact (hgi j).aestronglyMeasurable
  have hψ_out : ∀ x, x ∉ B → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hψs h))
  have hbdd : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ 1 :=
    Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hψ0 x)]; exact hψ1 x
  have hψf : ∀ j, Integrable (fun x => ψ x * f j x) μ := fun j =>
    (hint j).bdd_mul hψc.aestronglyMeasurable hbdd
  have hψg : ∀ j, Integrable (fun x => ψ x * g j x) μ := fun j =>
    (hgi j).bdd_mul hψc.aestronglyMeasurable hbdd
  have hres : ∀ (F : Vec d → ℝ), (∀ x, x ∉ B → F x = 0) → ∫ x, F x = ∫ x, F x ∂μ :=
    fun F hF => (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm
  have hA : Tendsto (fun j => ∫ x, ψ x * f j x ∂μ) atTop (𝓝 0) :=
    (ha ψ hψsmooth hψk hψs).congr (fun j =>
      hres _ (fun x hx => by rw [hψ_out x hx, zero_mul]))
  have hup : Tendsto (fun j => (∫ x, ψ x * f j x ∂μ) + 2 * ∫ x, g j x ∂μ) atTop (𝓝 0) := by
    simpa using hA.add (hint0.const_mul 2)
  have hI : ∀ j, ∫ x, ψ x * |f j x| = ∫ x, (ψ x * f j x + 2 * (ψ x * g j x)) ∂μ := by
    intro j
    rw [hres _ (fun x hx => by rw [hψ_out x hx, zero_mul])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg]
    rcases le_total 0 (f j x) with h | h
    · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun j => ?_) (fun j => ?_)
  · rw [hres _ (fun x hx => by rw [hψ_out x hx, zero_mul])]
    exact integral_nonneg (fun x => mul_nonneg (hψ0 x) (abs_nonneg _))
  · rw [hI j, integral_add (hψf j) ((hψg j).const_mul 2), integral_const_mul]
    refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ zero_le_two) _
    refine integral_mono (hψg j) (hgi j) (fun x => ?_)
    have := hgnn j x
    have := hψ1 x
    nlinarith

/-- The conclusion of [DPR, Lemma 2.2], `f_j → 0` in `L¹_loc(B₁)`: under the hypotheses of `tendsto_integral_mul_abs_of_vitali`,
`∫_K |f_j| → 0` for every compact `K ⊆ B₁`, using a smooth Urysohn function. -/
theorem tendsto_setIntegral_abs_of_vitali {d : ℕ} (f : ℕ → Vec d → ℝ)
    (hint : ∀ j, IntegrableOn (f j) (euclideanBall (0 : Vec d) 1))
    (ha : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanBall (0 : Vec d) 1 →
      Tendsto (fun j => ∫ x, ψ x * f j x) atTop (𝓝 0))
    (hb : ∀ l : ℝ, 0 < l →
      Tendsto (fun j => volume {x ∈ euclideanBall (0 : Vec d) 1 | l < max (-f j x) 0})
        atTop (𝓝 0))
    (hc : UnifIntegrable (fun j => fun x => max (-f j x) 0) 1
      (volume.restrict (euclideanBall (0 : Vec d) 1)))
    {K : Set (Vec d)} (hK : IsCompact K) (hKB : K ⊆ euclideanBall (0 : Vec d) 1) :
    Tendsto (fun j => ∫ x in K, |f j x|) atTop (𝓝 0) := by
  obtain ⟨ψ, hψs, hψ01, hψK, hψsupp, hψc⟩ := exists_smooth_urysohn_euclideanBall hK hKB
  have hmain := tendsto_integral_mul_abs_of_vitali f hint ha hb hc ψ hψs hψc hψsupp
    (fun x => (hψ01 x).1) (fun x => (hψ01 x).2)
  refine squeeze_zero (fun j => setIntegral_nonneg hK.measurableSet fun x _ => abs_nonneg _)
    (fun j => ?_) hmain
  have hBm : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  have hIB : IntegrableOn (fun x => ψ x * |f j x|) (euclideanBall (0 : Vec d) 1) :=
    (hint j).abs.bdd_mul hψs.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hψ01 x).1]; exact (hψ01 x).2)
  have hI : Integrable (fun x => ψ x * |f j x|) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hIB
    intro x hx
    exact hψsupp (subset_tsupport _ (Function.support_mul_subset_left _ _ hx))
  calc ∫ x in K, |f j x| = ∫ x in K, ψ x * |f j x| :=
        setIntegral_congr_fun hK.measurableSet fun x hx => by simp [hψK x hx]
    _ ≤ ∫ x, ψ x * |f j x| :=
        setIntegral_le_integral hI (Filter.Eventually.of_forall fun x =>
          mul_nonneg (hψ01 x).1 (abs_nonneg _))

end AFree
