module

public import AFree.Paper.Counterexample.Measure
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Properties of the counterexample measure

Local finiteness, support in the hyperplane `H`, non-vanishing, and the tangential integration by parts
identity for `τ`.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

theorem ceTau_compl : ceTau ceHᶜ = 0 := by
  rw [ceTau_apply measurableSet_ceH.compl, ← range_ceEmb]
  simp

theorem volume_ceH : (volume : Measure (Vec 5)) ceH = 0 := by
  have hne : LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) 4) ≠ ⊤ := by
    intro h
    have : (Pi.single 4 (1 : ℝ) : Vec 5) ∈ LinearMap.ker (LinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 5 => ℝ) 4) := by rw [h]; trivial
    simp at this
  have := Measure.addHaar_submodule (volume : Measure (Vec 5)) _ hne
  exact this

theorem ceTau_ne_zero : ceTau ≠ 0 := by
  intro h
  have := ceTau_apply (E := Set.univ) MeasurableSet.univ
  rw [h] at this
  simp at this

theorem ceTau_mutuallySingular : ceTau ⟂ₘ (volume : Measure (Vec 5)) :=
  ⟨ceHᶜ, measurableSet_ceH.compl, ceTau_compl, by simpa using volume_ceH⟩

/-- `τ` is locally finite, `τ(Hᶜ) = 0`, `vol⁵(H) = 0`, `τ ≠ 0`
and `τˢ = τ`. -/
theorem ceTau_basic :
    IsLocallyFiniteMeasure ceTau ∧ ceTau ceHᶜ = 0 ∧ (volume : Measure (Vec 5)) ceH = 0 ∧
      ceTau ≠ 0 ∧ ceTau.singularPart volume = ceTau := by
  refine ⟨?_, ceTau_compl, volume_ceH, ceTau_ne_zero,
    Measure.singularPart_eq_self.2 ceTau_mutuallySingular⟩
  have : IsFiniteMeasureOnCompacts ceTau := ⟨fun K hK => by
    rw [ceTau_apply hK.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (isometry_ceEmb.isClosedEmbedding.isCompact_preimage hK).measure_lt_top⟩
  infer_instance

/-- For a test function `φ` and `j < 4`, `∫ ∂_j φ dτ = 0`. -/
theorem integral_coordDeriv_ceTau {φ : Vec 5 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (j : Fin 4) :
    ∫ x, euclideanCoordDeriv (Fin.castSucc j) φ x ∂ceTau = 0 := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (euclideanCoordDeriv (Fin.castSucc j) φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [integral_ceTau hcont]
  set ψ : Vec 4 → ℝ := φ ∘ ceEmb with hψ
  have hψd : Differentiable ℝ ψ := hd.comp ceEmb.differentiable
  have hψc : HasCompactSupport ψ := hc.comp_isClosedEmbedding isometry_ceEmb.isClosedEmbedding
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp ceEmb.contDiff
  have heq : ∀ y, euclideanCoordDeriv (Fin.castSucc j) φ (ceEmb y)
      = fderiv ℝ ψ y (basisVec j) := by
    intro y
    have h1 : fderiv ℝ ψ y = (fderiv ℝ φ (ceEmb y)).comp ceEmb := by
      rw [hψ, fderiv_comp y (hd _) ceEmb.differentiableAt, ceEmb.fderiv]
    have h2 : ceEmb (basisVec j) = basisVec (Fin.castSucc j) := by
      funext i
      rw [ceEmb_apply]
      by_cases h : i.1 < 4
      · simp only [h, ↓reduceDIte, basisVec_apply]
        have : (⟨i.1, h⟩ : Fin 4) = j ↔ i = Fin.castSucc j := by
          constructor
          · rintro rfl; rfl
          · intro e; subst e; rfl
        simp only [this]
      · simp only [h, ↓reduceDIte, basisVec_apply]
        have : i ≠ Fin.castSucc j := fun e => h (by rw [e]; simp)
        simp [this]
    rw [h1, euclideanCoordDeriv, ContinuousLinearMap.comp_apply, h2]
  simp_rw [heq]
  have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec 4)))
    (f := fun _ => (1 : ℝ)) (g := ψ) (v := basisVec j)
    (by simp)
    (by simpa using ((hψs.continuous_fderiv (by simp)).clm_apply continuous_const
      ).integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ _))
    (by simpa using hψs.continuous.integrable_of_hasCompactSupport hψc)
    (fun _ _ => differentiableAt_const _) (fun _ _ => hψd.differentiableAt)
  simp at hI
  rw [hI, mul_zero]

end AFree
