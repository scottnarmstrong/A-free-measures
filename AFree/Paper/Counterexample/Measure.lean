module

public import AFree.Defs
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# The counterexample measure in `ℝ⁵`

The measure `τ = √2 · (ι₄)_* vol⁴` of [DPR, Remark 1.11], carried by a hyperplane.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

/-- The hyperplane `H = {x₄ = 0}` of `ℝ⁵`. -/
def ceH : Set (Vec 5) := {x | x 4 = 0}

/-- The measure `τ = ofReal √2 · μ_H[4] ⌞ H` of the counterexample. -/
noncomputable def ceTau : Measure (Vec 5) :=
  ENNReal.ofReal (Real.sqrt 2) • (μH[4] : Measure (Vec 5)).restrict ceH

/-- The embedding `ι₄ : ℝ⁴ → ℝ⁵`, `y ↦ (y₀, y₁, y₂, y₃, 0)`, as a continuous linear map. -/
noncomputable def ceEmb : Vec 4 →L[ℝ] Vec 5 :=
  ContinuousLinearMap.pi fun i : Fin 5 =>
    if h : i.1 < 4 then ContinuousLinearMap.proj (⟨i.1, h⟩ : Fin 4) else 0

theorem ceEmb_apply (y : Vec 4) (i : Fin 5) :
    ceEmb y i = if h : i.1 < 4 then y ⟨i.1, h⟩ else 0 := by
  unfold ceEmb
  by_cases h : i.1 < 4 <;> simp [h]

theorem ceEmb_castSucc (y : Vec 4) (j : Fin 4) : ceEmb y (Fin.castSucc j) = y j := by
  simp [ceEmb_apply]

theorem ceEmb_last (y : Vec 4) : ceEmb y 4 = 0 := by
  simp [ceEmb_apply]

/-- `ι₄` is a linear isometry of the maximum metrics. -/
theorem isometry_ceEmb : Isometry ceEmb := by
  refine AddMonoidHomClass.isometry_of_norm ceEmb fun y => ?_
  simp only [Pi.norm_def]
  congr 1
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    by_cases h : i.1 < 4
    · simp only [ceEmb_apply, h, ↓reduceDIte]
      exact Finset.le_sup (f := fun j => ‖y j‖₊) (Finset.mem_univ _)
    · simp [ceEmb_apply, h]
  · refine Finset.sup_le fun j _ => ?_
    have := Finset.le_sup (f := fun i : Fin 5 => ‖ceEmb y i‖₊) (Finset.mem_univ (Fin.castSucc j))
    rwa [ceEmb_castSucc] at this

theorem range_ceEmb : Set.range ceEmb = ceH := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ceEmb_last y
  · intro hx
    refine ⟨fun j => x (Fin.castSucc j), funext fun i => ?_⟩
    rw [ceEmb_apply]
    by_cases h : i.1 < 4
    · simp only [h, ↓reduceDIte]; rfl
    · simp only [h, ↓reduceDIte]
      have : i = 4 := by ext; have := i.2; simp at *; omega
      subst this; exact hx.symm

theorem measurableSet_ceH : MeasurableSet ceH :=
  isClosed_eq (continuous_apply 4) continuous_const |>.measurableSet

/-- for measurable `E`, `τ(E) = √2 · vol⁴(ι₄⁻¹ E)`. -/
theorem ceTau_apply {E : Set (Vec 5)} (hE : MeasurableSet E) :
    ceTau E = ENNReal.ofReal (Real.sqrt 2) * volume (ceEmb ⁻¹' E) := by
  have h4 : ((4 : ℕ) : ℝ) = (Fintype.card (Fin 4) : ℝ) := by simp
  have key : (μH[4] : Measure (Vec 5)) (E ∩ ceH) = volume (ceEmb ⁻¹' E) := by
    rw [← range_ceEmb, ← isometry_ceEmb.hausdorffMeasure_preimage (Or.inl (by norm_num))]
    have := hausdorffMeasure_pi_real (ι := Fin 4)
    rw [Fintype.card_fin] at this
    rw [show ((4 : ℕ) : ℝ) = 4 by norm_num] at this
    rw [this]
  rw [ceTau, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul, key]

/-- `τ = √2 · (ι₄)_* vol⁴`. -/
theorem ceTau_eq_map : ceTau = ENNReal.ofReal (Real.sqrt 2) • Measure.map ceEmb volume := by
  refine Measure.ext fun E hE => ?_
  rw [ceTau_apply hE, Measure.smul_apply, Measure.map_apply ceEmb.continuous.measurable hE,
    smul_eq_mul]

/-- `∫ f dτ = √2 ∫ f(ι₄ y) dy` for continuous `f`. -/
theorem integral_ceTau {f : Vec 5 → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂ceTau = Real.sqrt 2 * ∫ y, f (ceEmb y) := by
  rw [ceTau_eq_map, integral_smul_measure,
    integral_map ceEmb.continuous.aemeasurable hf.aestronglyMeasurable]
  simp [ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)]

end AFree
