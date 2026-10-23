module

public import AFree.Paper.OrderK.BlowUpEq
public import AFree.Measure.Mollify
public import AFree.Measure.Decomp.Density
public import AFree.Measure.PolarFacts

/-!
# Mollification and derivatives

Derivatives of a mollified measure: `∂^β (fτ)_ε = ∫ (∂^β φ_ε)(x - y) f(y) dτ(y)`,
and the `L¹` bound `∫_U |(fτ)_ε| ≤ ∫_{U^ε} |f| dτ` for vector-valued `f` (Euclidean norm on `ℝ^ι`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set PDE

namespace AFree

noncomputable section

variable {d : ℕ}

theorem euclideanCoordDeriv_kernelIntegral {Φ : Vec d → ℝ} (hΦ : IsCc Φ) {τ : Measure (Vec d)}
    {f : Vec d → ℝ} (hf : Integrable f τ) (i : Fin d) :
    euclideanCoordDeriv i (kernelIntegral Φ τ f) = kernelIntegral (euclideanCoordDeriv i Φ) τ f := by
  funext x
  unfold euclideanCoordDeriv
  rw [fderiv_kernelIntegral_apply (hΦ.1.of_le (by exact_mod_cast le_top)) hΦ.2 hf]
  simp only [kernelIntegral, smul_eq_mul]

theorem iterate_euclideanCoordDeriv_kernelIntegral {Φ : Vec d → ℝ} (hΦ : IsCc Φ)
    {τ : Measure (Vec d)} {f : Vec d → ℝ} (hf : Integrable f τ) (i : Fin d) (n : ℕ) :
    (euclideanCoordDeriv i)^[n] (kernelIntegral Φ τ f) =
      kernelIntegral ((euclideanCoordDeriv i)^[n] Φ) τ f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      euclideanCoordDeriv_kernelIntegral (isCc_iterate_euclideanCoordDeriv hΦ i n) hf]

theorem multiCoordDeriv_kernelIntegral {Φ : Vec d → ℝ} (hΦ : IsCc Φ) {τ : Measure (Vec d)}
    {f : Vec d → ℝ} (hf : Integrable f τ) (β : Fin d → ℕ) :
    multiCoordDeriv β (kernelIntegral Φ τ f) = kernelIntegral (multiCoordDeriv β Φ) τ f := by
  have key : ∀ l : List (Fin d), foldDeriv l β (kernelIntegral Φ τ f) =
      kernelIntegral (foldDeriv l β Φ) τ f := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      show (euclideanCoordDeriv i)^[β i] (foldDeriv l β (kernelIntegral Φ τ f)) = _
      have hc : IsCc (foldDeriv l β Φ) := isCc_foldr_iterate hΦ β l
      rw [ih, iterate_euclideanCoordDeriv_kernelIntegral hc hf i (β i)]
      rfl
  exact key _

theorem piEuclideanNorm_integral_le {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    (μ : Measure X) {g : X → ι → ℝ} (hg : ∀ i, Integrable (fun x => g x i) μ) :
    piEuclideanNorm (fun i => ∫ x, g x i ∂μ) ≤ ∫ x, piEuclideanNorm (g x) ∂μ := by
  set w : ι → ℝ := fun i => ∫ x, g x i ∂μ with hw
  have hI := integrable_piEuclideanNorm_of_coord hg
  have hsq : piEuclideanNorm w ^ 2 = ∫ x, ∑ i, w i * g x i ∂μ := by
    rw [integral_finsetSum _ fun i _ => (hg i).const_mul (w i)]
    rw [← sum_mul_self_eq_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  have hle : piEuclideanNorm w ^ 2 ≤ piEuclideanNorm w * ∫ x, piEuclideanNorm (g x) ∂μ := by
    rw [hsq, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun i _ => (hg i).const_mul (w i))
      (hI.const_mul _) fun x => sum_mul_le_piEuclideanNorm_mul _ _
  have h0 : 0 ≤ ∫ x, piEuclideanNorm (g x) ∂μ := integral_nonneg fun x => piEuclideanNorm_nonneg _
  rcases (piEuclideanNorm_nonneg w).eq_or_lt with h | h
  · rw [← h]; exact h0
  · rw [sq] at hle
    exact le_of_mul_le_mul_left hle h

variable {ι : Type*} [Fintype ι]

theorem integral_piEuclideanNorm_mollify_le {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d))
    [IsFiniteMeasure τ] {f : Vec d → ι → ℝ} (hf : Integrable f τ) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    ∫ x in U, piEuclideanNorm (mollify ε τ f x) ≤
      ∫ y in {y | ∃ x ∈ U, x ∈ euclideanBall y ε}, piEuclideanNorm (f y) ∂τ := by
  have hcoord : ∀ i, Integrable (fun y => f y i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hf
  have hGint : Integrable (fun y => piEuclideanNorm (f y)) τ :=
    integrable_piEuclideanNorm_of_coord hcoord
  have hcont : Continuous (fun x => piEuclideanNorm (mollify ε τ f x)) :=
    continuous_piEuclideanNorm.comp (contDiff_mollify hε τ hf).continuous
  refine setIntegral_le_integral_thickening hε τ hU hGint (fun _ => piEuclideanNorm_nonneg _)
    hcont (fun _ => piEuclideanNorm_nonneg _) fun x => ?_
  have hint : Integrable (fun y => scaledMollifier ε (x - y) • f y) τ :=
    integrable_kernel (contDiff_scaledMollifier ε).continuous
      (hasCompactSupport_scaledMollifier hε) hf x
  have hcoord2 : ∀ i, Integrable (fun y => (scaledMollifier ε (x - y) • f y) i) τ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integrable_comp hint
  have heq : mollify ε τ f x = fun i => ∫ y, (scaledMollifier ε (x - y) • f y) i ∂τ := by
    funext i
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).integral_comp_comm
      hint).symm
  rw [heq]
  refine (piEuclideanNorm_integral_le τ hcoord2).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [piEuclideanNorm_smul, abs_of_nonneg (scaledMollifier_nonneg hε.le _)]

/-- For `f ∈ L¹(τ)`, every multi-index `β` and `ε > 0`,
`∂^β (fτ)_ε(x) = ∫ (∂^β φ_ε)(x - y) f(y) dτ(y)`; and for `f ∈ L¹(τ; ℝ^ι)`,
`∫_U |(fτ)_ε| ≤ ∫_{U^ε} |f| dτ` (Euclidean norm). -/
theorem lem_mollk {ε : ℝ} (hε : 0 < ε) (τ : Measure (Vec d)) [IsFiniteMeasure τ] :
    (∀ (f : Vec d → ℝ), Integrable f τ → ∀ (β : Fin d → ℕ) (x : Vec d),
      multiCoordDeriv β (mollify ε τ f) x =
        ∫ y, multiCoordDeriv β (scaledMollifier ε) (x - y) * f y ∂τ) ∧
    (∀ (f : Vec d → ι → ℝ), Integrable f τ → ∀ U : Set (Vec d), MeasurableSet U →
      ∫ x in U, piEuclideanNorm (mollify ε τ f x) ≤
        ∫ y in {y | ∃ x ∈ U, x ∈ euclideanBall y ε}, piEuclideanNorm (f y) ∂τ) := by
  refine ⟨fun f hf β x => ?_, fun f hf U hU => integral_piEuclideanNorm_mollify_le hε τ hf hU⟩
  have hΦ : IsCc (scaledMollifier (d := d) ε) :=
    ⟨contDiff_scaledMollifier ε, hasCompactSupport_scaledMollifier hε⟩
  have h1 : mollify ε τ f = kernelIntegral (scaledMollifier ε) τ f := rfl
  have := congrFun (multiCoordDeriv_kernelIntegral hΦ hf β) x
  rw [h1]
  simpa [kernelIntegral, smul_eq_mul] using this

end

end AFree
