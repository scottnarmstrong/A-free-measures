module

public import AFree.Curves.Lemma31.Gauss
public import AFree.Curves.Exhaust.CurveCurrent
public import AFree.Measure.VectorIntegral

/-!
# The Gaussian currents `T_i = e_i w 𝓛^d`

Variation, polar and normality of the explicit currents, in the `KVec d 1` encoding.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

variable {d : ℕ}

/-- `ε_i ∈ KVec d 1`, `ε_i(⟨{j}, _⟩) = δ_ij`. -/
noncomputable def gaussDir (i : Fin d) : KVec d 1 := vecToKVecOne (basisVec i)

/-- The Gaussian current `T_i = e_i · w · 𝓛^d`, as `(w 𝓛^d).withDensityᵥ (const ε_i)`. -/
noncomputable def gaussCurrent (i : Fin d) : VectorMeasure (Vec d) (KVec d 1) :=
  (gaussMeasure d).withDensityᵥ fun _ => gaussDir i

lemma piEuclideanNorm_gaussDir (i : Fin d) : piEuclideanNorm (gaussDir i) = 1 := by
  rw [gaussDir, piEuclideanNorm_vecToKVecOne, vecEuclideanNorm_basisVec]

lemma gaussCurrent_apply (i : Fin d) {E : Set (Vec d)} (hE : MeasurableSet E) :
    gaussCurrent i E = (gaussMeasure d).real E • gaussDir i := by
  rw [gaussCurrent, withDensityᵥ_apply (integrable_const _) hE, setIntegral_const]

lemma piEuclideanNorm_gaussCurrent (i : Fin d) {E : Set (Vec d)} (hE : MeasurableSet E) :
    piEuclideanNorm (gaussCurrent i E) = (gaussMeasure d).real E := by
  rw [gaussCurrent_apply i hE, piEuclideanNorm_smul, piEuclideanNorm_gaussDir, mul_one,
    abs_of_nonneg measureReal_nonneg]

/-- `|T_i| = w 𝓛^d`. -/
lemma euclideanVariation_gaussCurrent (i : Fin d) :
    euclideanVariation (gaussCurrent i) = gaussMeasure d := by
  refine le_antisymm (euclideanVariation_le_of_forall _ fun E hE => ?_) ?_
  · rw [piEuclideanNorm_gaussCurrent i hE, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · refine Measure.le_iff.2 fun s hs => ?_
    refine le_trans ?_ (ofReal_piEuclideanNorm_le_euclideanVariation (gaussCurrent i) s)
    rw [piEuclideanNorm_gaussCurrent i hs, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `T_i = e_i w 𝓛^d` is a vector measure with
`|T_i| = w 𝓛^d`, and every `μ ≪ 𝓛^d` satisfies `μ ≪ |T_i|`. -/
theorem gaussian_vector_measure (i : Fin d) :
    euclideanVariation (gaussCurrent i) = gaussMeasure d ∧
      ∀ μ : Measure (Vec d), μ ≪ volume → μ ≪ euclideanVariation (gaussCurrent i) := by
  refine ⟨euclideanVariation_gaussCurrent i, fun μ hμ => ?_⟩
  rw [euclideanVariation_gaussCurrent]
  exact hμ.trans (withDensity_absolutelyContinuous'
    continuous_gauss.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => by simpa using gauss_pos x))

lemma polar_gaussCurrent_apply_ae (i : Fin d) (K : KIdx d 1) :
    ∀ᵐ x ∂(gaussMeasure d), polar (gaussCurrent i) x K = gaussDir i K := by
  have hV := euclideanVariation_gaussCurrent i
  have : IsFiniteMeasure (euclideanVariation (gaussCurrent i)) := by rw [hV]; infer_instance
  rw [← hV]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => ?_)
    (fun s _ _ => (integrable_const _).integrableOn) (fun s hs _ => ?_)
  · exact (integrable_polar_apply (gaussCurrent i) K).integrableOn
  · rw [← coordMeasure_eq_setIntegral _ _ hs, setIntegral_const, coordMeasure_apply, hV,
      gaussCurrent_apply i hs]
    simp [mul_comm]

/-- `polar T_i = e_i` (as a `1`-vector) `w 𝓛^d`-a.e., hence
`μ`-a.e. for every `μ ≪ 𝓛^d`, and `kvecOneToVec (polar T_i x) = e_i`. -/
theorem gaussian_polar (i : Fin d) :
    (∀ᵐ x ∂(gaussMeasure d), kvecOneToVec (polar (gaussCurrent i) x) = basisVec i) ∧
      ∀ μ : Measure (Vec d), μ ≪ volume →
        ∀ᵐ x ∂μ, kvecOneToVec (polar (gaussCurrent i) x) = basisVec i := by
  have h : ∀ᵐ x ∂(gaussMeasure d), kvecOneToVec (polar (gaussCurrent i) x) = basisVec i := by
    filter_upwards [ae_all_iff.2 (polar_gaussCurrent_apply_ae i)] with x hx
    funext j
    have := hx ⟨{j}, Finset.card_singleton j⟩
    simpa [kvecOneToVec, gaussDir, vecToKVecOne_apply] using this
  refine ⟨h, fun μ hμ => ?_⟩
  refine (hμ.trans (withDensity_absolutelyContinuous'
    continuous_gauss.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => by simpa using gauss_pos x))).ae_le h

lemma integrable_gaussMeasure_coord (i : Fin d) :
    Integrable (fun x : Vec d => 2 * x i) (gaussMeasure d) := by
  unfold gaussMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    continuous_gauss.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have := (integrable_coord_gauss i).const_mul 2
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [(gauss_pos x).le]
  ring

/-- The boundary `S_i = 2 x_i w 𝓛^d` of `T_i`. -/
noncomputable def gaussBoundary (i : Fin d) : VectorMeasure (Vec d) (KVec d (1 - 1)) :=
  (gaussMeasure d).withDensityᵥ fun x _ => 2 * x i

lemma integrable_gaussBoundary_density (i : Fin d) :
    Integrable (fun (x : Vec d) (_ : KIdx d (1 - 1)) => 2 * x i) (gaussMeasure d) :=
  integrable_pi_iff.2 fun _ => integrable_gaussMeasure_coord i

lemma integral_gaussCurrent_apply (i : Fin d) {ψ : Vec d → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ x, ‖ψ x‖ ≤ C) (j : Fin d) :
    (∫ᵛ x, ψ x ∂•(gaussCurrent i)) ⟨{j}, Finset.card_singleton j⟩ =
      (if j = i then ∫ x, ψ x ∂(gaussMeasure d) else 0) := by
  unfold gaussCurrent
  rw [integral_withDensityᵥ_smul _ (integrable_const _) hψ hC]
  have hi : ∀ K : KIdx d 1, Integrable (fun x => ψ x • gaussDir i K) (gaussMeasure d) :=
    fun K => (Integrable.of_bound (C := C) hψ.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)).smul_const _
  rw [eval_integral (f := fun x => ψ x • gaussDir i) hi]
  have hK : gaussDir i ⟨{j}, Finset.card_singleton j⟩ = if j = i then 1 else 0 := by
    simp [gaussDir, vecToKVecOne_apply, basisVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul, hK]
  split_ifs with h
  · simp
  · simp

/-- `T_i = e_i w 𝓛^d` is a normal current on `Set.univ`, with
boundary `2 x_i w 𝓛^d`. -/
theorem gaussian_normal (i : Fin d) : IsNormalCurrentOn Set.univ (gaussCurrent i) := by
  refine ⟨by simp, gaussBoundary i, by simp, fun φ hφ J => ?_⟩
  have hJ : J.1 = ∅ := Finset.card_eq_zero.1 (by simpa using J.2)
  obtain ⟨hs, hc, -⟩ := hφ
  have hφm : Measurable φ := hs.continuous.measurable
  obtain ⟨Cφ, hCφ⟩ := hs.continuous.bounded_above_of_compact_support hc
  have hder : ∀ j, Measurable (euclideanCoordDeriv j φ) ∧
      ∃ C, ∀ x, ‖euclideanCoordDeriv j φ x‖ ≤ C := fun j =>
    ⟨(continuous_euclideanCoordDeriv hs j).measurable,
      (continuous_euclideanCoordDeriv hs j).bounded_above_of_compact_support
        (hc.fderiv_apply ℝ _)⟩
  have hL : (∫ᵛ x, φ x ∂•(gaussBoundary i)) J = ∫ x, φ x * (2 * x i) ∂(gaussMeasure d) := by
    unfold gaussBoundary
    rw [integral_withDensityᵥ_smul _ (integrable_gaussBoundary_density i) hφm hCφ]
    have hi : ∀ K : KIdx d (1 - 1), Integrable (fun x => φ x * (2 * x i)) (gaussMeasure d) :=
      fun K => ((integrable_gaussMeasure_coord i).bdd_mul hφm.aestronglyMeasurable
        (Filter.Eventually.of_forall hCφ)).congr (Filter.Eventually.of_forall fun x => by
          simp [mul_comm])
    rw [eval_integral (f := fun x => φ x • fun _ : KIdx d (1 - 1) => 2 * x i) hi J]
    simp
  rw [hL, ← integral_coordDeriv_gaussMeasure ⟨hs, hc, Set.subset_univ _⟩ i]
  have hf : (Finset.univ.filter (· ∉ J.1)) = Finset.univ := by simp [hJ]
  rw [hf]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      (if h : (insert j J.1).card = 1 then insertSign j J.1 *
        (∫ᵛ x, euclideanCoordDeriv j φ x ∂•(gaussCurrent i)) ⟨insert j J.1, h⟩ else 0) =
      if j = i then ∫ x, euclideanCoordDeriv j φ x ∂(gaussMeasure d) else 0 := by
    intro j _
    have hins : insert j J.1 = {j} := by rw [hJ]; simp
    have hcard : (insert j J.1).card = 1 := by rw [hins]; simp
    rw [dite_eq_left_of_eq_true (eq_true hcard)]
    have hK : (⟨insert j J.1, hcard⟩ : KIdx d 1) = ⟨{j}, Finset.card_singleton j⟩ :=
      Subtype.ext hins
    rw [hK, integral_gaussCurrent_apply i (hder j).1 (hder j).2.choose_spec j]
    simp [insertSign, hJ]
  rw [Finset.sum_congr rfl hterm]
  simp

end AFree
