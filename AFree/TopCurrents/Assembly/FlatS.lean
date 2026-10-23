module

public import AFree.TopCurrents.Assembly.VMeas
public import AFree.TopCurrents.NormalAC
public import AFree.TopCurrents.BdTop

/-!
# The top-dimensional measures `S_u = u 𝓛^d e_top`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

/-- The coordinate densities of `u e_top`. -/
noncomputable def topH (u : Vec d → ℝ) : KIdx d d → Vec d → ℝ :=
  fun J x => if J = topKIdx d then u x else 0

/-- `S_u`: the `Λ_d`-valued vector measure `E ↦ (∫_E u) e_top`. -/
noncomputable def sMeas (u : Vec d → ℝ) : VectorMeasure (Vec d) (KVec d d) := vMeas (topH u)

lemma integrable_topH {u : Vec d → ℝ} (hu : Integrable u volume) (J : KIdx d d) :
    Integrable (topH u J) volume := by
  unfold topH; split_ifs
  · exact hu
  · exact integrable_zero _ _ _

lemma sMeas_apply_top {u : Vec d → ℝ} (hu : Integrable u volume) {E : Set (Vec d)}
    (hE : MeasurableSet E) : sMeas u E (topKIdx d) = ∫ x in E, u x := by
  rw [sMeas, vMeas_apply (integrable_topH hu) hE]; simp [topH]

lemma sMeas_integral_top {u : Vec d → ℝ} (hu : Integrable u volume) {g : Vec d → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x, g x ∂•(sMeas u)) (topKIdx d) = ∫ x, g x * u x := by
  rw [sMeas, vMeas_integral (integrable_topH hu) hg hC]; simp [topH]

lemma ofReal_abs_integral_le_uMass {w : Vec d → ℝ} (hw : Integrable w volume) {E : Set (Vec d)}
    (hE : MeasurableSet E) : ENNReal.ofReal |∫ x in E, w x| ≤ uMass w E := by
  unfold uMass
  rw [withDensity_apply _ hE, ← ofReal_integral_eq_lintegral_ofReal hw.abs.restrict
    (Eventually.of_forall fun _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by simpa using norm_integral_le_integral_norm (μ := volume.restrict E) w)

/-- `|μ| ≤ |w| 𝓛^d` for a `Λ_d`-valued measure whose top coordinate is `w 𝓛^d`. -/
lemma euclideanVariation_le_uMass {w : Vec d → ℝ} (hw : Integrable w volume)
    (μ : VectorMeasure (Vec d) (KVec d d))
    (hμ : ∀ E, MeasurableSet E → μ E (topKIdx d) = ∫ x in E, w x) :
    euclideanVariation μ ≤ uMass w :=
  euclideanVariation_le_of_forall μ fun E hE => by
    rw [piEuclideanNorm_topKVec, hμ E hE]
    exact ofReal_abs_integral_le_uMass hw hE

lemma uMass_univ {w : Vec d → ℝ} (hw : Integrable w volume) :
    uMass w Set.univ = ENNReal.ofReal (∫ x, |w x|) := by
  unfold uMass
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal hw.abs (Eventually.of_forall fun _ => abs_nonneg _)]

lemma uMass_compl_eq_zero {w : Vec d → ℝ} {K : Set (Vec d)} (hK : MeasurableSet K)
    (hw : ∀ᵐ x, x ∉ K → w x = 0) : uMass w Kᶜ = 0 := by
  unfold uMass
  rw [withDensity_apply _ hK.compl]
  have : ∀ᵐ x ∂(volume.restrict Kᶜ), ENNReal.ofReal |w x| = 0 :=
    (ae_restrict_iff' hK.compl).2 (hw.mono fun x hx hxK => by simp [hx hxK])
  rw [lintegral_congr_ae this, lintegral_zero]

/-- `S_u - S_w` has top coordinate `(u - w) 𝓛^d`. -/
lemma sMeas_sub_apply_top {u w : Vec d → ℝ} (hu : Integrable u volume) (hw : Integrable w volume)
    {E : Set (Vec d)} (hE : MeasurableSet E) :
    (sMeas u - sMeas w) E (topKIdx d) = ∫ x in E, (u x - w x) := by
  rw [sub_apply, Pi.sub_apply, sMeas_apply_top hu hE, sMeas_apply_top hw hE,
    integral_sub hu.integrableOn hw.integrableOn]

/-- A smooth compactly supported function is in `Lip_b`. -/
lemma isBddLipFun_of_test {f : Vec d → ℝ} (hf : IsTestFunctionOn Set.univ f) : IsBddLipFun f := by
  obtain ⟨L, hL⟩ := hf.1.lipschitzWith_of_hasCompactSupport hf.2.1 (by simp)
  refine ⟨⟨L, fun x y => ?_⟩, ?_⟩
  · have h1 : |f x - f y| ≤ L * ‖x - y‖ := by
      have := hL.dist_le_mul x y
      rwa [Real.dist_eq, dist_eq_norm] at this
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    refine (pi_norm_le_iff_of_nonneg (vecEuclideanNorm_nonneg _)).2 fun i => ?_
    simpa using abs_apply_le_vecEuclideanNorm (x - y) i
  · obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
    exact ⟨C, fun x => by simpa using hC x⟩

end AFree
