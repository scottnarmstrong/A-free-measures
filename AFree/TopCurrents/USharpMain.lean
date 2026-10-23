module

public import AFree.TopCurrents.USharpAxioms
public import AFree.TopCurrents.WithDensityInt
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# `u_#` is a metric current ([AK, Example 3.2])
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents AFree.MetricCurrents.AKExt AFree.MetricCurrents.Nu

variable {d : ℕ} {u : Vec d → ℝ}

private lemma integral_uMass (hu : Integrable u volume) (g : Vec d → ℝ) :
    ∫ x, g x ∂(uMass u) = ∫ x, |u x| * g x := by
  unfold uMass
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hu.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [ENNReal.toReal_ofReal (abs_nonneg _)]

private lemma isFinite_uMass (hu : Integrable u volume) : IsFiniteMeasure (uMass u) :=
  isFiniteMeasure_withDensity_ofReal hu.abs.hasFiniteIntegral

private lemma usharp_admissible (hu : Integrable u volume) :
    IsAKMassAdmissible (usharp u) (uMass u) := by
  refine ⟨isFinite_uMass hu, fun f hf π K hπ => ?_⟩
  obtain ⟨hfL, Cf, hCf⟩ := hf
  have hfc := lipFun_continuous hfL
  rw [integral_uMass hu, ← integral_const_mul]
  have hint : Integrable (fun x => |u x| * |f x|) volume :=
    hu.abs.bdd_mul (c := Cf) (continuous_abs.comp hfc).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCf x) |>.congr
        (Eventually.of_forall fun x => mul_comm _ _)
  have := norm_integral_le_of_norm_le (f := fun x => f x * u x * jacDet π x)
    (hint.const_mul (∏ i, (K i : ℝ))) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := abs_jacDet_le hπ x
      have h2 : 0 ≤ |f x| * |u x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc |f x| * |u x| * |jacDet π x| ≤ |f x| * |u x| * ∏ i, (K i : ℝ) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = _ := by ring)
  simpa [usharp, Real.norm_eq_abs] using this

private lemma usharp_isMetricCurrent_aux (hu : Integrable u volume) :
    IsMetricCurrent d (usharp u) := by
  have hadd : ∀ f g, IsBddLipFun f → IsBddLipFun g → ∀ π : Fin d → Vec d → ℝ, IsLipTuple π →
      usharp u (f + g) π = usharp u f π + usharp u g π := by
    intro f g hf hg π hπ
    have := usharp_lin_f hu hf hg hπ 1 1
    simpa using this
  have hsmul : ∀ f, IsBddLipFun f → ∀ π : Fin d → Vec d → ℝ, IsLipTuple π → ∀ t : ℝ,
      usharp u (t • f) π = t * usharp u f π := by
    intro f hf π hπ t
    have := usharp_lin_f hu hf hf hπ t 0
    simpa using this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨_, usharp_admissible hu⟩, ?_, ?_, ?_, ?_⟩
  · intro f g hf hg π hπ
    rw [hadd f g hf hg π hπ]; exact abs_add_le _ _
  · intro f hf π hπ t ht
    rw [hsmul f hf π hπ t, abs_mul, abs_of_nonneg ht]
  · intro f hf π hπ i ψ hψ
    have := usharp_lin_slot hu hf hπ i hψ 1 1
    simp only [one_smul, one_mul] at this
    rw [this]; exact abs_add_le _ _
  · intro f hf π hπ i t ht
    have := usharp_lin_slot hu hf hπ i (hπ i) t 0
    simp only [zero_smul, add_zero, zero_mul] at this
    rw [this, abs_mul, abs_of_nonneg ht]
  · intro π hπ f g hf hg a b
    exact usharp_lin_f hu hf hg hπ a b
  · intro f hf π hπ i ψ hψ a b
    exact usharp_lin_slot hu hf hπ i hψ a b
  · intro f hf π hπ πn ⟨C, hC⟩ hlim
    exact usharp_continuity hu hf hC (fun i x => hlim i x)
  · intro f hf π hπ i ⟨U, hU, hfU, c, hc⟩
    exact usharp_locality i hU hfU hc


private lemma jacMat_coordTuple (x : Vec d) : jacMat (coordTuple d) x = 1 := by
  ext i j
  have : fderiv ℝ (coordTuple d i) x = ContinuousLinearMap.proj i := (hasFDerivAt_apply i x).fderiv
  simp [jacMat, this, Matrix.one_apply, Pi.single_apply]

private lemma usharp_coord (f : Vec d → ℝ) :
    usharp u f (coordTuple d) = ∫ x, f x * u x := by
  unfold usharp jacDet
  simp [jacMat_coordTuple]

private lemma totalVariation_eq (hu : Integrable u volume) {ν : SignedMeasure (Vec d)}
    (h : ∀ f : Vec d → ℝ, IsBddLipFun f → ∫ᵛ x, f x ∂•ν = ∫ x, f x * u x) :
    ν.totalVariation = uMass u := by
  have hν : ν = volume.withDensityᵥ u := by
    refine signedMeasure_eq_of_integral_lip _ _ fun f hf => ?_
    obtain ⟨hfL, C, hC⟩ := hf
    rw [h f ⟨hfL, C, hC⟩, integral_withDensityᵥ_real hu (lipFun_continuous hfL).measurable hC]
  rw [hν, SignedMeasure.totalVariation_eq_variation, Measure.variation_withDensityᵥ hu]
  unfold uMass
  simp [Real.enorm_eq_ofReal_abs]

/-- ([AK, Example 3.2]) For `u ∈ L¹(𝓛^d)`, `u_# ∈ M_d(ℝ^d)` with admissible measure `|u| 𝓛^d`,
mass `‖u_#‖ = |u| 𝓛^d`, `u_#(f, x) = ∫ f u dx` for `f ∈ Lip_b`, and `u_#` has compact support if `u`
vanishes a.e. off a compact set. -/
theorem usharp_isMetricCurrent (hu : Integrable u volume) :
    IsMetricCurrent d (usharp u) ∧ IsAKMassAdmissible (usharp u) (uMass u) ∧
      IsAKMass (usharp u) (uMass u) ∧
      (∀ f, IsBddLipFun f → usharp u f (coordTuple d) = ∫ x, f x * u x) ∧
      (∀ K : Set (Vec d), IsCompact K → (∀ᵐ x, x ∉ K → u x = 0) → HasCompactAKSupport (usharp u)) := by
  have hT := usharp_isMetricCurrent_aux hu
  obtain ⟨ν, hν, -, -, -, hle, hmass⟩ := nu_main hT
  have hcoord : ∀ f : Vec d → ℝ, IsBddLipFun f → usharp u f (coordTuple d) = ∫ x, f x * u x :=
    fun f _ => usharp_coord f
  have htv : ν.totalVariation = uMass u := by
    refine totalVariation_eq hu fun f hf => ?_
    rw [hν f (isBorelBdd_of_isBddLipFun hf), ← hcoord f hf,
      ← ((akext hT).1.1 f hf (coordTuple d) coordTuple_lip)]
  have hmassu : IsAKMass (usharp u) (uMass u) := by
    refine ⟨usharp_admissible hu, fun μ hμ => ?_⟩
    rw [← htv]; exact hle μ hμ
  refine ⟨hT, usharp_admissible hu, hmassu, hcoord, fun K hK hKu => ?_⟩
  refine ⟨K, hK, fun μ hμ => ?_⟩
  rw [hmass μ hμ, htv]
  unfold uMass
  rw [withDensity_apply _ hK.isClosed.measurableSet.compl]
  refine (lintegral_eq_zero_iff' ?_).2 ?_
  · exact (hu.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal).restrict
  · rw [Filter.EventuallyEq, ae_restrict_iff' hK.isClosed.measurableSet.compl]
    filter_upwards [hKu] with x hx hxK
    simp [hx hxK]

end AFree
