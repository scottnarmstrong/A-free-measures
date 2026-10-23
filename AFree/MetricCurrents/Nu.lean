module

public import AFree.MetricCurrents.AKChain
public import AFree.MetricCurrents.MollMap
public import AFree.MetricCurrents.NuAux

/-!
# The density `ν` and the identity `‖T‖ = |ν|`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.MetricCurrents.Nu

/-- `ν` is the signed measure with `∫ h dν = T(h, x_1, …, x_d)` for every `h ∈ B^∞`. -/
def IsNuMeasure {d : ℕ} (T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ) (ν : SignedMeasure (Vec d)) :
    Prop :=
  ∀ h : Vec d → ℝ, IsBorelBdd h → ∫ᵛ x, h x ∂•ν = akExt T h (coordTuple d)

variable {d : ℕ} {T : (Vec d → ℝ) → (Fin d → Vec d → ℝ) → ℝ}

private lemma apply_of_isNu {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) {B : Set (Vec d)} (hB : MeasurableSet B) :
    ν B = akExt T (B.indicator 1) (coordTuple d) := by
  have h1 := hν _ (isBorelBdd_indicator hB)
  have := finite_variation ν
  have h2 := VectorMeasure.integral_indicator_const (B := ContinuousLinearMap.lsmul ℝ ℝ) (μ := ν)
    (1 : ℝ) hB
  rw [← h1]
  have e : (fun x => B.indicator (1 : Vec d → ℝ) x) = fun x => B.indicator (fun _ => (1 : ℝ)) x := by
    funext x; by_cases hx : x ∈ B <;> simp [hx]
  rw [e]
  simpa using h2.symm

private lemma tv_le_of_isNu (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) {μ : Measure (Vec d)} (hμ : IsAKMassAdmissible T μ) :
    ν.totalVariation ≤ μ := by
  rw [SignedMeasure.totalVariation_eq_variation]
  exact variation_le_of_apply hT (fun B hB => apply_of_isNu hν hB) hμ

/-- (a) `ν(B) = T(1_B, x)` is a finite signed measure with `∫ h dν = T(h, x)`
for `h ∈ B^∞`, `|ν(B)| ≤ μ(B)` and `|ν| ≤ μ` for every admissible `μ`. -/
theorem nu_signedMeasure (hT : IsMetricCurrent d T) :
    ∃ ν : SignedMeasure (Vec d), IsNuMeasure T ν ∧
      (∀ B, MeasurableSet B → ν B = akExt T (B.indicator 1) (coordTuple d)) ∧
      (∀ μ, IsAKMassAdmissible T μ → ∀ B, MeasurableSet B → ENNReal.ofReal |ν B| ≤ μ B) ∧
      (∀ μ, IsAKMassAdmissible T μ → ν.totalVariation ≤ μ) := by
  have hnu := isNu_of_apply hT (ν := nuMeasure hT) fun B hB => nuMeasure_apply hT hB
  refine ⟨nuMeasure hT, hnu, fun B hB => nuMeasure_apply hT hB, ?_, fun μ hμ => ?_⟩
  · intro μ hμ B hB
    have := hμ.1
    rw [nuMeasure_apply hT hB]
    calc ENNReal.ofReal |akExt T (B.indicator 1) (coordTuple d)| ≤ ENNReal.ofReal (μ.real B) :=
          ENNReal.ofReal_le_ofReal (ext_indicator_bound hT hμ hB)
      _ = μ B := ENNReal.ofReal_toReal (measure_ne_top μ B)
  · exact tv_le_of_isNu hT hnu hμ

/-- (b) `T(f, ψ) = ∫ f det Dψ dν` for `f ∈ Lip_b`, `ψ_i ∈ C¹` with
bounded gradients. -/
theorem nu_jacobian_integral (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) {f : Vec d → ℝ} (hf : IsBddLipFun f) {ψ : Fin d → Vec d → ℝ}
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (hM : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M) :
    T f ψ = ∫ᵛ x, f x * jacDet ψ x ∂•ν := by
  have hfB := isBorelBdd_of_isBddLipFun hf
  obtain ⟨hLip, heq⟩ := akchain hT coordTuple_lip hψ hM hfB
  have hw := isBorelBdd_mul_jacDet coordTuple_lip hψ hM hfB
  have hE1 : T f ψ = akExt T f ψ := ((akext hT).1.1 f hf ψ hLip).symm
  rw [hE1]
  exact heq.trans (hν _ hw).symm

/-- (c) `|T(f, π)| ≤ P(K) ∫ |f| d|ν|`; hence `|ν|` is admissible. -/
theorem nu_mass_bound (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) :
    (∀ f, IsBddLipFun f → ∀ (π : Fin d → Vec d → ℝ) (K : Fin d → ℝ≥0),
      (∀ i, IsEuclLipschitzWith (K i) (π i)) →
        |T f π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x| ∂ν.totalVariation) ∧
    IsAKMassAdmissible T ν.totalVariation := by
  have hb : ∀ f, IsBddLipFun f → ∀ (π : Fin d → Vec d → ℝ) (K : Fin d → ℝ≥0),
      (∀ i, IsEuclLipschitzWith (K i) (π i)) →
        |T f π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x| ∂ν.totalVariation := by
    intro f hf π K hπ
    rw [SignedMeasure.totalVariation_eq_variation]
    have := finite_variation ν
    have hfB := isBorelBdd_of_isBddLipFun hf
    have hρ := isMollifierKernel_stdMollifier d
    obtain ⟨hunif, hsm, -, -, hmin⟩ := mollmap hρ hπ
    set ψn : ℕ → Fin d → Vec d → ℝ :=
      fun n i => mollLip (stdMollifier d) (1 / ((n : ℝ) + 1)) (π i) with hψn
    have hbound : ∀ n, |T f (ψn n)| ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x| ∂ν.variation := by
      intro n
      have hψ : ∀ i, ContDiff ℝ 1 (ψn n i) := fun i =>
        (hsm i n).1.of_le (by exact_mod_cast le_top)
      have hM : ∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψn n i) y‖ ≤ M := by
        choose L hL using fun i => exists_lipschitzWith_of_eucl (hsm i n).2
        refine ⟨∑ i, (L i : ℝ), fun i y => ?_⟩
        exact (norm_fderiv_le_of_lipschitz ℝ (hL i)).trans
          (Finset.single_le_sum (f := fun i => (L i : ℝ)) (fun j _ => (L j).2)
            (Finset.mem_univ i))
      have hJ := nu_jacobian_integral hT hν hf hψ hM
      have hw := integrable_of_isBorelBdd (m := ν.variation)
        (isBorelBdd_mul_jacDet coordTuple_lip hψ hM hfB)
      have hfi := integrable_of_isBorelBdd (m := ν.variation) hfB
      rw [hJ]
      refine (abs_integral_le ν _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono hw.abs (hfi.abs.const_mul _) fun x => ?_
      have hd : |jacDet (ψn n) x| ≤ ∏ i, (K i : ℝ) := by
        have := hmin d id id Function.injective_id n x
        rw [Matrix.submatrix_id_id] at this
        exact this
      calc |f x * jacDet (ψn n) x| = |f x| * |jacDet (ψn n) x| := abs_mul _ _
        _ ≤ |f x| * ∏ i, (K i : ℝ) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
        _ = _ := mul_comm _ _
    have hlim := hT.2.2.2.2.1 f hf π (fun i => ⟨K i, hπ i⟩) ψn
      ⟨Finset.univ.sup K, fun n i => isEucl_mono (Finset.le_sup (Finset.mem_univ i)) (hsm i n).2⟩
      (fun i x => (hunif i).tendsto_at x)
    exact le_of_tendsto' hlim.abs hbound
  exact ⟨hb, inferInstance, hb⟩

/-- (d) Every mass measure of `T` equals `|ν|`. -/
theorem nu_mass_eq_variation (hT : IsMetricCurrent d T) {ν : SignedMeasure (Vec d)}
    (hν : IsNuMeasure T ν) {μ : Measure (Vec d)} (hμ : IsAKMass T μ) :
    μ = ν.totalVariation := by
  have hadm := (nu_mass_bound hT hν).2
  exact le_antisymm (hμ.2 _ hadm) (tv_le_of_isNu hT hν hμ.1)

/-- For `T ∈ M_d(ℝ^d)` there is a finite signed measure `ν` with
`ν(h) = T(h, x_1, …, x_d)`, `T(f, ψ) = ∫ f det Dψ dν` for `C¹` `ψ` with bounded gradients, `|ν|`
admissible and `|ν| ≤ μ` for every admissible `μ`, and every mass measure of `T` equals `|ν|`
(`ν.totalVariation`). -/
theorem nu_main (hT : IsMetricCurrent d T) :
    ∃ ν : SignedMeasure (Vec d), IsNuMeasure T ν ∧
      (∀ B, MeasurableSet B → ν B = akExt T (B.indicator 1) (coordTuple d)) ∧
      (∀ f, IsBddLipFun f → ∀ ψ : Fin d → Vec d → ℝ, (∀ i, ContDiff ℝ 1 (ψ i)) →
        (∃ M : ℝ, ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M) → T f ψ = ∫ᵛ x, f x * jacDet ψ x ∂•ν) ∧
      IsAKMassAdmissible T ν.totalVariation ∧
      (∀ μ, IsAKMassAdmissible T μ → ν.totalVariation ≤ μ) ∧
      (∀ μ, IsAKMass T μ → μ = ν.totalVariation) := by
  obtain ⟨ν, hν, happ, -, hle⟩ := nu_signedMeasure hT
  exact ⟨ν, hν, happ, fun f hf ψ hψ hM => nu_jacobian_integral hT hν hf hψ hM,
    (nu_mass_bound hT hν).2, hle, fun μ hμ => nu_mass_eq_variation hT hν hμ⟩

end AFree
