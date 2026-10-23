module

public import AFree.Defs.Finite
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Coordinate absolute continuity and the vector integral against the polar

* `AFree.coordMeasure_absolutelyContinuous` etc.: the coordinates of a vector measure are absolutely continuous with respect to its variation, and the polar is integrable.
* `AFree.integral_smul_vectorMeasure_eq`: `∫ g dμ = ∫ g (dμ/d|μ|) d|μ|`, proved by indicators, simple
  functions, then bounded pointwise limits (dominated convergence on both sides).
-/

public section

open MeasureTheory Filter Topology

namespace AFree

open PDE

variable {ι : Type*} [Fintype ι] {X : Type*} [MeasurableSpace X]

theorem abs_apply_le_piEuclideanNorm (v : ι → ℝ) (i : ι) : |v i| ≤ piEuclideanNorm v := by
  rw [← Real.sqrt_mul_self_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j * v j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ i))

omit [Fintype ι] in
theorem coordMeasure_apply (μ : VectorMeasure X (ι → ℝ)) (i : ι) (E : Set X) :
    coordMeasure μ i E = μ E i := rfl

/-- `μᵢ ≪ |μ|`. -/
theorem coordMeasure_absolutelyContinuous (μ : VectorMeasure X (ι → ℝ)) (i : ι) :
    coordMeasure μ i ≪ᵥ (euclideanVariation μ).toENNRealVectorMeasure := by
  intro s hs
  by_cases hm : MeasurableSet s
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hm] at hs
    have h := ofReal_piEuclideanNorm_le_euclideanVariation μ s
    rw [hs, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
    have := abs_apply_le_piEuclideanNorm (μ s) i
    rw [coordMeasure_apply]
    exact abs_nonpos_iff.mp (this.trans h)
  · exact VectorMeasure.not_measurable _ hm

/-- The polar is measurable. -/
theorem measurable_polar (μ : VectorMeasure X (ι → ℝ)) : Measurable (polar μ) :=
  Measurable.of_eval fun _ => SignedMeasure.measurable_rnDeriv _ _

/-- Each coordinate of the polar is measurable. -/
theorem measurable_polar_apply (μ : VectorMeasure X (ι → ℝ)) (i : ι) :
    Measurable (fun x => polar μ x i) :=
  SignedMeasure.measurable_rnDeriv _ _

/-- Each coordinate of the polar is `|μ|`-integrable. -/
theorem integrable_polar_apply (μ : VectorMeasure X (ι → ℝ)) (i : ι) :
    Integrable (fun x => polar μ x i) (euclideanVariation μ) :=
  SignedMeasure.integrable_rnDeriv _ _

/-- The polar is `|μ|`-integrable (as a vector-valued function). -/
theorem integrable_polar (μ : VectorMeasure X (ι → ℝ)) :
    Integrable (polar μ) (euclideanVariation μ) :=
  integrable_pi_iff.2 (integrable_polar_apply μ)

/-- `μᵢ(E) = ∫_E (dμ/d|μ|)ᵢ d|μ|`. -/
theorem coordMeasure_eq_setIntegral (μ : VectorMeasure X (ι → ℝ)) (i : ι) {E : Set X}
    (hE : MeasurableSet E) :
    coordMeasure μ i E = ∫ x in E, polar μ x i ∂euclideanVariation μ := by
  have h := SignedMeasure.withDensityᵥ_rnDeriv_eq (coordMeasure μ i) (euclideanVariation μ)
    (coordMeasure_absolutelyContinuous μ i)
  conv_lhs => rw [← h]
  exact withDensityᵥ_apply (integrable_polar_apply μ i) hE

/-- Vector form of `coordMeasure_eq_setIntegral`: `μ(E) = ∫_E dμ/d|μ| d|μ|`. -/
theorem vectorMeasure_eq_setIntegral (μ : VectorMeasure X (ι → ℝ)) {E : Set X}
    (hE : MeasurableSet E) :
    μ E = ∫ x in E, polar μ x ∂euclideanVariation μ := by
  funext i
  rw [← coordMeasure_apply, coordMeasure_eq_setIntegral μ i hE,
    eval_integral (fun j => (integrable_polar_apply μ j).restrict) i]

theorem integrable_smul_polar (μ : VectorMeasure X (ι → ℝ)) {g : X → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => g x • polar μ x) (euclideanVariation μ) := by
  refine integrable_pi_iff.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (integrable_polar_apply μ i).bdd_mul hg.aestronglyMeasurable (Eventually.of_forall hC)

/-- Vector form: `∫ g dμ = ∫ g (dμ/d|μ|) d|μ|` for bounded measurable `g`. -/
theorem integral_smul_vectorMeasure_eq (μ : VectorMeasure X (ι → ℝ)) {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ∫ᵛ x, g x ∂•μ = ∫ x, g x • polar μ x ∂euclideanVariation μ := by
  -- simple functions
  have simple : ∀ f : SimpleFunc X ℝ,
      ∫ᵛ x, f x ∂•μ = ∫ x, f x • polar μ x ∂euclideanVariation μ := by
    intro f
    induction f using SimpleFunc.induction with
    | @const c s hs =>
      have e : ⇑(SimpleFunc.piecewise _ hs (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
          Set.indicator s (fun _ => c) := by
        ext x; by_cases hx : x ∈ s <;> simp [hx]
      rw [e, VectorMeasure.integral_indicator_const c hs]
      have e2 : (fun x => Set.indicator s (fun _ : X => c) x • polar μ x) =
          Set.indicator s (fun x => c • polar μ x) := by
        ext x j; by_cases hx : x ∈ s <;> simp [hx]
      rw [e2, integral_indicator hs, integral_smul, ← vectorMeasure_eq_setIntegral μ hs]
      simp
    | @add f g hd hf hg =>
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have if1 : μ.Integrable f := SimpleFunc.integrable_of_isFiniteMeasure _
      have ig1 : μ.Integrable g := SimpleFunc.integrable_of_isFiniteMeasure _
      have := VectorMeasure.integral_fun_add (B := ContinuousLinearMap.lsmul ℝ ℝ) if1 ig1
      simp only [SimpleFunc.coe_add, Pi.add_apply] at *
      rw [this, hf, hg, ← integral_add (integrable_smul_polar μ f.measurable hCf)
        (integrable_smul_polar μ g.measurable hCg)]
      simp [add_smul]
  have hsm : StronglyMeasurable g := hg.stronglyMeasurable
  have hbd : ∀ n x, ‖hsm.approxBounded C n x‖ ≤ C := fun n x => hsm.norm_approxBounded_le
    ((norm_nonneg _).trans (hC x)) n x
  have hlim : ∀ x, Tendsto (fun n => hsm.approxBounded C n x) atTop (𝓝 (g x)) :=
    fun x => hsm.tendsto_approxBounded_of_norm_le (hC x)
  have L : Tendsto (fun n => ∫ᵛ x, hsm.approxBounded C n x ∂•μ) atTop
      (𝓝 (∫ᵛ x, g x ∂•μ)) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => (SimpleFunc.measurable _).aestronglyMeasurable)
    (integrable_const C) (fun n => Eventually.of_forall (hbd n))
    (Eventually.of_forall hlim)
  have R : Tendsto (fun n => ∫ x, hsm.approxBounded C n x • polar μ x ∂euclideanVariation μ)
      atTop (𝓝 (∫ x, g x • polar μ x ∂euclideanVariation μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => C * ‖polar μ x‖)
      (fun n => ((SimpleFunc.measurable (hsm.approxBounded C n)).smul (measurable_polar μ)).aestronglyMeasurable)
      ((integrable_polar μ).norm.const_mul C) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hlim x).smul_const _)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hbd n x) (norm_nonneg _)
  exact tendsto_nhds_unique L (R.congr fun n => (simple _).symm)

/-- Coordinate form: `(∫ g dμ)ᵢ = ∫ g (dμ/d|μ|)ᵢ d|μ|`. -/
theorem integral_smul_vectorMeasure_apply (μ : VectorMeasure X (ι → ℝ)) {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (i : ι) :
    (∫ᵛ x, g x ∂•μ) i = ∫ x, g x * polar μ x i ∂euclideanVariation μ := by
  rw [integral_smul_vectorMeasure_eq μ hg hC,
    eval_integral (fun j => by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (integrable_pi_iff.1 (integrable_smul_polar μ hg hC)) j) i]
  simp

end AFree
