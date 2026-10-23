module

public import AFree.Defs
public import AFree.Measure.Decomp.Density
public import AFree.Paper.Currents.Free

/-!
# Restriction of a locally normal current to a ball

Reduction, implicit in [DPR, Remark 1.11], of a locally normal current to normal currents on balls. The statement is proved for every `k`: the case distinction in
the definition of `IsBoundaryOn` and of `IsLocNormalCurrent` is the same, so `k = d - 2 ≥ 1` is not
needed.
-/

public section

open MeasureTheory

namespace AFree

open PDE

variable {d k : ℕ}

/-- A locally finite measure is finite on a ball. -/
theorem isFiniteMeasure_restrict_ball {τ : Measure (Vec d)} (hτ : IsLocallyFiniteMeasure τ)
    (R : ℝ) : IsFiniteMeasure (τ.restrict (Metric.ball (0 : Vec d) R)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (Metric.ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : Vec d) R).measure_lt_top⟩

/-- A bounded measurable `P` has integrable coordinates on a ball. -/
theorem integrable_coord_restrict_ball {τ : Measure (Vec d)} (hτ : IsLocallyFiniteMeasure τ)
    (R : ℝ) {P : Vec d → KVec d k} (hm : Measurable P) (h1 : ∀ᵐ x ∂τ, piEuclideanNorm (P x) = 1)
    (I : KIdx d k) : Integrable (fun x => P x I) (τ.restrict (Metric.ball (0 : Vec d) R)) := by
  have := isFiniteMeasure_restrict_ball hτ R
  refine Integrable.of_bound (C := 1)
    ((measurable_pi_apply I).comp hm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae h1] with x hx
  rw [Real.norm_eq_abs]
  exact (abs_apply_le_piEuclideanNorm _ I).trans hx.le

/-- Locally integrable data have integrable coordinates on a ball. -/
theorem integrable_coord_restrict_ball_of_locallyIntegrable {τ : Measure (Vec d)}
    (R : ℝ) {P : Vec d → KVec d k} (hP : LocallyIntegrable P τ) (I : KIdx d k) :
    Integrable (fun x => P x I) (τ.restrict (Metric.ball (0 : Vec d) R)) := by
  have h : IntegrableOn P (Metric.closedBall (0 : Vec d) R) τ :=
    hP.integrableOn_isCompact (isCompact_closedBall (0 : Vec d) R)
  exact integrable_pi_iff.1 (h.mono_set Metric.ball_subset_closedBall) I

/-- A test function on `B` vanishes outside `B`. -/
theorem IsTestFunctionOn.eq_zero_of_notMem {Ω : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsTestFunctionOn Ω φ) {x : Vec d} (hx : x ∉ Ω) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)

/-- The coordinates of `∫ᵛ φ d(σ.withDensityᵥ P)` for `σ = τ ⌞ B` and `φ` a test function on `B`. -/
theorem integral_restrict_withDensityᵥ_apply {τ : Measure (Vec d)} {B : Set (Vec d)}
    [IsFiniteMeasure (τ.restrict B)] {ι : Type*} [Fintype ι] {P : Vec d → ι → ℝ} (hP : ∀ i, Integrable (fun x => P x i) (τ.restrict B))
    {φ : Vec d → ℝ} (hφ : IsTestFunctionOn B φ) (i : ι) :
    (∫ᵛ x, φ x ∂•((τ.restrict B).withDensityᵥ P)) i = ∫ x, φ x * P x i ∂τ := by
  obtain ⟨hm, C, hC⟩ := hφ.measurable_bound
  rw [integral_withDensityᵥ_eq hP hm hC]
  have hgP : ∀ j, Integrable (fun x => φ x * P x j) (τ.restrict B) := fun j =>
    (hP j).bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  rw [eval_integral (f := fun x => φ x • P x) (fun j => by simpa using hgP j) i]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [hφ.eq_zero_of_notMem hx, zero_mul]

/-- `σ = τ ⌞ B`, `σ' = τ' ⌞ B` are finite and the coordinates of `P`, `P'` are
integrable on `B` for `τ`, `τ'`. -/
theorem cut_finiteness {τ τ' : Measure (Vec d)} {P : Vec d → KVec d k} {P' : Vec d → KVec d (k - 1)}
    (hτ : IsLocallyFiniteMeasure τ) (hPm : Measurable P) (hP1 : ∀ᵐ x ∂τ, piEuclideanNorm (P x) = 1)
    (hτ' : IsLocallyFiniteMeasure τ') (hP' : LocallyIntegrable P' τ') (R : ℝ) :
    IsFiniteMeasure (τ.restrict (Metric.ball (0 : Vec d) R)) ∧
      (∀ I, Integrable (fun x => P x I) (τ.restrict (Metric.ball (0 : Vec d) R))) ∧
      IsFiniteMeasure (τ'.restrict (Metric.ball (0 : Vec d) R)) ∧
      ∀ J, Integrable (fun x => P' x J) (τ'.restrict (Metric.ball (0 : Vec d) R)) :=
  ⟨isFiniteMeasure_restrict_ball hτ R, integrable_coord_restrict_ball hτ R hPm hP1,
    isFiniteMeasure_restrict_ball hτ' R, integrable_coord_restrict_ball_of_locallyIntegrable R hP'⟩

/-- `|T| = σ`, `polar T = P` `σ`-a.e. (part (i)), `|T|(Bᶜ) = 0` and
`|S|(Bᶜ) = 0`. -/
theorem cut_outside {τ τ' : Measure (Vec d)} {P : Vec d → KVec d k} {P' : Vec d → KVec d (k - 1)}
    (hP1 : ∀ᵐ x ∂τ, piEuclideanNorm (P x) = 1) (R : ℝ)
    [IsFiniteMeasure (τ.restrict (Metric.ball (0 : Vec d) R))]
    (hPi : ∀ I, Integrable (fun x => P x I) (τ.restrict (Metric.ball (0 : Vec d) R)))
    (hPi' : ∀ J, Integrable (fun x => P' x J) (τ'.restrict (Metric.ball (0 : Vec d) R))) :
    (euclideanVariation ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P) =
        τ.restrict (Metric.ball (0 : Vec d) R) ∧
      polar ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P) =ᵐ[
        τ.restrict (Metric.ball (0 : Vec d) R)] P) ∧
    euclideanVariation ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P)
        (Metric.ball (0 : Vec d) R)ᶜ = 0 ∧
    euclideanVariation ((τ'.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P')
        (Metric.ball (0 : Vec d) R)ᶜ = 0 := by
  have hB : MeasurableSet (Metric.ball (0 : Vec d) R) := Metric.isOpen_ball.measurableSet
  have hd := euclideanVariation_withDensityᵥ_eq_of_norm_eq_one hPi (ae_restrict_of_ae hP1)
  refine ⟨hd, ?_, euclideanVariation_withDensityᵥ_eq_zero hPi' ?_⟩
  · rw [hd.1]; simp [Measure.restrict_apply, hB]
  · simp [Measure.restrict_apply, hB]

/-- `S = σ'.withDensityᵥ P'` is the boundary of `T = σ.withDensityᵥ P`
on `B`, from the defining identity of a locally normal current. -/
theorem cut_boundary {τ τ' : Measure (Vec d)} {P : Vec d → KVec d k} {P' : Vec d → KVec d (k - 1)}
    (R : ℝ) [IsFiniteMeasure (τ.restrict (Metric.ball (0 : Vec d) R))]
    [IsFiniteMeasure (τ'.restrict (Metric.ball (0 : Vec d) R))]
    (hPi : ∀ I, Integrable (fun x => P x I) (τ.restrict (Metric.ball (0 : Vec d) R)))
    (hPi' : ∀ J, Integrable (fun x => P' x J) (τ'.restrict (Metric.ball (0 : Vec d) R)))
    (hS0 : euclideanVariation ((τ'.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P')
      (Metric.ball (0 : Vec d) R)ᶜ = 0)
    (hbd : ∀ φ : Vec d → ℝ, IsTestFunctionOn Set.univ φ → ∀ J : KIdx d (k - 1),
        ∫ x, φ x * P' x J ∂τ' = ∑ j ∈ Finset.univ.filter (· ∉ J.1),
          if h : (insert j J.1).card = k then
            insertSign j J.1 * ∫ x, euclideanCoordDeriv j φ x * P x ⟨insert j J.1, h⟩ ∂τ
          else 0) :
    IsBoundaryOn (Metric.ball (0 : Vec d) R)
      ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P)
      ((τ'.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P') := by
  refine ⟨hS0, fun φ hφ J => ?_⟩
  have hφu : IsTestFunctionOn Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  rw [integral_restrict_withDensityᵥ_apply hPi' hφ J, hbd φ hφu J]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [integral_restrict_withDensityᵥ_apply hPi (hφ.coordDeriv j) ⟨_, h⟩]
  · rfl

/-- Restriction of a locally normal current to the ball `B_R`: with `σ = τ ⌞ B`,
`σ' = τ' ⌞ B`, `T = σ.withDensityᵥ P`, `S = σ'.withDensityᵥ P'`: `σ`, `σ'` are finite, the
coordinates of `P`, `P'` are integrable, `|T| = σ`, `polar T = P` `σ`-a.e., `S` is the boundary
of `T` on `B`, and `|T|(Bᶜ) = 0`. -/
theorem cut {τ : Measure (Vec d)} {P : Vec d → KVec d k} (hT : IsLocNormalCurrent τ P) (R : ℝ) :
    IsFiniteMeasure (τ.restrict (Metric.ball (0 : Vec d) R)) ∧
      (∀ I, Integrable (fun x => P x I) (τ.restrict (Metric.ball (0 : Vec d) R))) ∧
      (euclideanVariation ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P) =
          τ.restrict (Metric.ball (0 : Vec d) R) ∧
        polar ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P) =ᵐ[
          τ.restrict (Metric.ball (0 : Vec d) R)] P) ∧
      ∃ (τ' : Measure (Vec d)) (P' : Vec d → KVec d (k - 1)),
        IsFiniteMeasure (τ'.restrict (Metric.ball (0 : Vec d) R)) ∧
        (∀ J, Integrable (fun x => P' x J) (τ'.restrict (Metric.ball (0 : Vec d) R))) ∧
        IsBoundaryOn (Metric.ball (0 : Vec d) R)
          ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P)
          ((τ'.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P') ∧
        euclideanVariation ((τ.restrict (Metric.ball (0 : Vec d) R)).withDensityᵥ P)
          (Metric.ball (0 : Vec d) R)ᶜ = 0 := by
  obtain ⟨hτ, hPm, hP1, τ', P', hτ', _, hP'loc, hbd⟩ := hT
  obtain ⟨hfin, hPi, hfin', hPi'⟩ := cut_finiteness hτ hPm hP1 hτ' hP'loc R
  obtain ⟨h1, h2, h3⟩ := cut_outside (τ' := τ') (P' := P') hP1 R hPi hPi'
  exact ⟨hfin, hPi, h1, τ', P', hfin', hPi', cut_boundary R hPi hPi' h3 hbd, h2⟩

end AFree
