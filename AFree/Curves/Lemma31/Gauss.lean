module

public import AFree.Defs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The Gaussian weight

`w(x) = exp(-|x|²)`, the finite measure `w · 𝓛^d`, and the integration by parts
`∫ ∂_i φ w = ∫ φ 2 x_i w` for test functions.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

variable {d : ℕ}

/-- The Gaussian weight `w(x) = exp(-|x|²)`. -/
noncomputable def gauss (x : Vec d) : ℝ := Real.exp (-vecNormSq x)

lemma gauss_pos (x : Vec d) : 0 < gauss x := Real.exp_pos _

lemma continuous_gauss : Continuous (gauss (d := d)) := by
  unfold gauss vecNormSq vecDot
  fun_prop

lemma gauss_eq_prod (x : Vec d) : gauss x = ∏ j, Real.exp (-1 * (x j) ^ 2) := by
  unfold gauss vecNormSq vecDot
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

lemma integrable_gauss : Integrable (gauss (d := d)) volume := by
  have h : Integrable (fun x : Vec d => ∏ j, Real.exp (-1 * (x j) ^ 2))
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq one_pos)
  have h2 : (volume : Measure (Vec d)) = Measure.pi fun _ : Fin d => (volume : Measure ℝ) :=
    volume_pi
  rw [h2]
  have h3 : (gauss : Vec d → ℝ) = fun x => ∏ j, Real.exp (-1 * (x j) ^ 2) :=
    funext gauss_eq_prod
  rw [h3]
  exact h

lemma integrable_coord_gauss (i : Fin d) : Integrable (fun x : Vec d => x i * gauss x) volume := by
  have h : Integrable (fun x : Vec d => ∏ j, ((if j = i then x j else 1) *
      Real.exp (-1 * (x j) ^ 2))) (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    refine Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := fun j (t : ℝ) => (if j = i then t else 1) * Real.exp (-1 * t ^ 2)) (fun j => ?_)
    by_cases hj : j = i
    · simpa [hj] using integrable_mul_exp_neg_mul_sq one_pos
    · simpa [hj] using integrable_exp_neg_mul_sq one_pos
  have h2 : (volume : Measure (Vec d)) = Measure.pi fun _ : Fin d => (volume : Measure ℝ) :=
    volume_pi
  rw [h2]
  convert h using 2 with x
  rw [Finset.prod_mul_distrib, ← gauss_eq_prod]
  simp

lemma hasFDerivAt_gauss (x : Vec d) :
    HasFDerivAt (gauss (d := d)) (-(gauss x) • ∑ j : Fin d, (2 * x j) •
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x := by
  have hq : HasFDerivAt (fun y : Vec d => vecNormSq y)
      (∑ j : Fin d, (2 * x j) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x := by
    unfold vecNormSq vecDot
    have := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun (j : Fin d) (y : Vec d) => y j * y j)
      (A' := fun j => (2 * x j) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))
      (fun j _ => by
        have hp : HasFDerivAt (fun y : Vec d => y j)
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x :=
          hasFDerivAt_apply j x
        have := hp.mul hp
        convert this using 1
        ext v; simp; ring) (x := x)
    simpa using this
  have := (hq.neg).exp
  have h3 : (gauss : Vec d → ℝ) = fun y => Real.exp ((-fun y => vecNormSq y) y) := rfl
  rw [h3]
  convert this using 1
  ext v
  simp

lemma fderiv_gauss_basisVec (x : Vec d) (i : Fin d) :
    fderiv ℝ gauss x (basisVec i) = -(2 * x i) * gauss x := by
  rw [(hasFDerivAt_gauss x).fderiv]
  simp [basisVec, Pi.single_apply]
  ring

/-- The finite measure `w · 𝓛^d`. -/
noncomputable def gaussMeasure (d : ℕ) : Measure (Vec d) :=
  volume.withDensity fun x => ENNReal.ofReal (gauss x)

instance : IsFiniteMeasure (gaussMeasure d) :=
  isFiniteMeasure_withDensity_ofReal integrable_gauss.hasFiniteIntegral

lemma integral_gaussMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Vec d → E) :
    ∫ x, g x ∂(gaussMeasure d) = ∫ x, gauss x • g x := by
  unfold gaussMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (continuous_gauss.measurable.ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [(gauss_pos _).le]

lemma differentiable_gauss : Differentiable ℝ (gauss (d := d)) := fun x =>
  (hasFDerivAt_gauss x).differentiableAt

lemma continuous_euclideanCoordDeriv {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) :
    Continuous (euclideanCoordDeriv i φ) :=
  (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Integration by parts against the Gaussian: `∫ ∂_iφ w = ∫ φ 2x_i w`. -/
lemma integral_coordDeriv_gaussMeasure {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Set.univ φ)
    (i : Fin d) :
    ∫ x, euclideanCoordDeriv i φ x ∂(gaussMeasure d) =
      ∫ x, φ x * (2 * x i) ∂(gaussMeasure d) := by
  obtain ⟨hs, hc, -⟩ := hφ
  have hφd : Differentiable ℝ φ := hs.differentiable (by simp)
  have hg' : (fun x => φ x * fderiv ℝ gauss x (basisVec i)) =
      fun x => -(2 : ℝ) * (φ x * (x i * gauss x)) := by
    funext x; rw [fderiv_gauss_basisVec]; ring
  have hcont : Continuous fun x : Vec d => x i * gauss x :=
    (continuous_apply i).mul continuous_gauss
  have h1 : Integrable (fun x => euclideanCoordDeriv i φ x * gauss x) volume :=
    ((continuous_euclideanCoordDeriv hs i).mul continuous_gauss).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ _).mul_right)
  have h2 : Integrable (fun x => φ x * fderiv ℝ gauss x (basisVec i)) volume := by
    rw [hg']
    exact (((hs.continuous.mul hcont).integrable_of_hasCompactSupport
      (hc.mul_right))).const_mul _
  have h3 : Integrable (fun x => φ x * gauss x) volume :=
    (hs.continuous.mul continuous_gauss).integrable_of_hasCompactSupport hc.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec d)))
    (f := φ) (g := gauss) (v := basisVec i) h1 h2 h3 (fun x _ => hφd x)
    (fun x _ => differentiable_gauss x)
  rw [integral_gaussMeasure, integral_gaussMeasure]
  simp only [smul_eq_mul]
  have e1 : ∫ x, gauss x * euclideanCoordDeriv i φ x =
      ∫ x, euclideanCoordDeriv i φ x * gauss x := by
    congr 1; funext x; ring
  have e2 : ∫ x, gauss x * (φ x * (2 * x i)) = 2 * ∫ x, φ x * (x i * gauss x) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e1, e2]
  have e3 : ∫ x, φ x * fderiv ℝ gauss x (basisVec i) = -2 * ∫ x, φ x * (x i * gauss x) := by
    rw [hg', integral_const_mul]
  rw [e3] at key
  have : euclideanCoordDeriv i φ = fun x => fderiv ℝ φ x (basisVec i) := rfl
  rw [this] at *
  linarith

end AFree
