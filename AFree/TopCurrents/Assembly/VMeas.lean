module

public import AFree.Curves.Exhaust.VecDensity
public import AFree.TopCurrents.Basic

/-!
# Vector measures with prescribed integrable coordinate densities

`vMeas h` is the `ι → ℝ`-valued measure `E ↦ (∫_E hᵢ)ᵢ`, built as a vector density against the finite
measure `W 𝓛^d`, `W = Σᵢ |hᵢ|`, so that the integral of bounded Borel functions can be computed.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- `W = Σᵢ |hᵢ|`. -/
noncomputable def vW (h : ι → Vec d → ℝ) (x : Vec d) : ℝ := ∑ i, |h i x|

/-- The finite measure `W 𝓛^d`. -/
noncomputable def vMass (h : ι → Vec d → ℝ) : Measure (Vec d) :=
  volume.withDensity fun x => ENNReal.ofReal (vW h x)

/-- The vector measure `E ↦ (∫_E hᵢ)ᵢ`. -/
noncomputable def vMeas (h : ι → Vec d → ℝ) : VectorMeasure (Vec d) (ι → ℝ) :=
  (vMass h).withDensityᵥ fun x i => h i x / vW h x

variable {h : ι → Vec d → ℝ}

lemma vW_nonneg' {x : Vec d} : 0 ≤ vW h x := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma vW_nonneg (x : Vec d) : 0 ≤ vW h x := vW_nonneg'

lemma abs_le_vW (i : ι) (x : Vec d) : |h i x| ≤ vW h x :=
  Finset.single_le_sum (f := fun j => |h j x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

lemma div_vW_mul (i : ι) (x : Vec d) : h i x / vW h x * vW h x = h i x := by
  rcases (vW_nonneg (h := h) x).eq_or_lt with h0 | hp
  · have : h i x = 0 := abs_nonpos_iff.1 (by simpa [← h0] using abs_le_vW (h := h) i x)
    simp [← h0, this]
  · exact div_mul_cancel₀ _ hp.ne'

lemma toReal_ofReal_vW (x : Vec d) : (ENNReal.ofReal (vW h x)).toReal = vW h x :=
  ENNReal.toReal_ofReal vW_nonneg'

lemma integrable_vW (hh : ∀ i, Integrable (h i) volume) : Integrable (vW h) volume :=
  integrable_finsetSum _ fun i _ => (hh i).abs

lemma isFiniteMeasure_vMass (hh : ∀ i, Integrable (h i) volume) : IsFiniteMeasure (vMass h) :=
  isFiniteMeasure_withDensity_ofReal (integrable_vW hh).hasFiniteIntegral

lemma integral_vMass (hh : ∀ i, Integrable (h i) volume) (F : Vec d → ℝ) :
    ∫ x, F x ∂(vMass h) = ∫ x, vW h x * F x := by
  unfold vMass
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((integrable_vW hh).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [toReal_ofReal_vW]

lemma integrable_vDensity (hh : ∀ i, Integrable (h i) volume) :
    Integrable (fun x i => h i x / vW h x) (vMass h) := by
  have := isFiniteMeasure_vMass hh
  refine integrable_pi_iff.2 fun i => ?_
  refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((hh i).aemeasurable.div (integrable_vW hh).aemeasurable).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)
  · rw [Real.norm_eq_abs]
    rcases (vW_nonneg (h := h) x).eq_or_lt with h0 | hp
    · simp [← h0]
    · rw [abs_div, abs_of_pos hp]
      exact div_le_one_of_le₀ (abs_le_vW i x) hp.le

/-- `(vMeas h)(E)ᵢ = ∫_E hᵢ`. -/
theorem vMeas_apply (hh : ∀ i, Integrable (h i) volume) {E : Set (Vec d)} (hE : MeasurableSet E)
    (i : ι) : vMeas h E i = ∫ x in E, h i x := by
  have hint := integrable_vDensity hh
  unfold vMeas
  rw [withDensityᵥ_apply hint hE,
    eval_integral (fun j => (integrable_pi_iff.1 hint j).restrict) i]
  unfold vMass
  rw [restrict_withDensity hE,
    integral_withDensity_eq_integral_toReal_smul₀
      ((integrable_vW hh).aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [toReal_ofReal_vW, smul_eq_mul]
  rw [mul_comm, div_vW_mul]

/-- `(∫ g d(vMeas h))ᵢ = ∫ g hᵢ` for bounded Borel `g`. -/
theorem vMeas_integral (hh : ∀ i, Integrable (h i) volume) {g : Vec d → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (i : ι) :
    (∫ᵛ x, g x ∂•(vMeas h)) i = ∫ x, g x * h i x := by
  have hint := integrable_vDensity hh
  have := isFiniteMeasure_vMass hh
  unfold vMeas
  rw [integral_withDensityᵥ_smul (vMass h) hint hg hC]
  have hi : ∀ j, Integrable (fun x => (g x • fun k => h k x / vW h x) j) (vMass h) := by
    intro j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (integrable_pi_iff.1 hint j).bdd_mul (c := C) hg.aestronglyMeasurable
      (Eventually.of_forall hC)
  rw [eval_integral hi i, integral_vMass hh]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  calc vW h x * (g x * (h i x / vW h x)) = g x * (h i x / vW h x * vW h x) := by ring
    _ = g x * h i x := by rw [div_vW_mul]

end AFree
