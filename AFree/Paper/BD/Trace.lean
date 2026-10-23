module

public import AFree.Paper.BD.TraceCore
public import AFree.Paper.BD.Symmetric
public import AFree.Measure.PolarFacts

/-!
# The trace of `Eu` has no singular part

Hypothesis `hdiv` is the one of [DPR, Corollary 1.8]: `div u = g ∈ L²(Ω)` in `𝒟'(Ω)`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

variable {d : ℕ}

/-- The divergence hypothesis of [DPR, Corollary 1.8]. -/
def HasL2Divergence (Ω : Set (Vec d)) (u : Vec d → Vec d) : Prop :=
  ∃ g : Vec d → ℝ, MemLp g 2 (volume.restrict Ω) ∧
    ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x

/-- `∫ φ dτ = ∫_Ω g φ` for `τ = Σ_i Eu_{ii}` and test functions `φ`. -/
theorem sum_integral_diag_eq {Ω : Set (Vec d)} {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu) {g : Vec d → ℝ}
    (hg : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x)
    {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Ω φ) :
    ∑ i, (∫ᵛ x, φ x ∂•Eu) (i, i) = ∫ x in Ω, g x * φ x := by
  have h1 : ∀ i, (∫ᵛ x, φ x ∂•Eu) (i, i) = -∫ x in Ω, u x i * euclideanCoordDeriv i φ x := by
    intro i
    rw [BD.integral_eq_of_isBDGradientOn hEu hφ i i]
    ring
  simp only [h1, Finset.sum_neg_distrib]
  have h2 := hg φ hφ
  rw [integral_finsetSum] at h2
  · linarith
  · intro i _
    have := BD.isTest_D hφ i
    exact BD.integrableOn_coord_mul hEu.1 i this.1.continuous this.2.1

theorem sum_apply_signed {X : Type*} [MeasurableSpace X] {ι' : Type*} (s : Finset ι')
    (f : ι' → SignedMeasure X) (E : Set X) : (∑ i ∈ s, f i) E = ∑ i ∈ s, f i E := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- A vector measure vanishes on sets that are null for `|μ|`. -/
theorem vectorMeasure_eq_zero_of_variation_eq_zero {ι : Type*} [Fintype ι] {X : Type*}
    [MeasurableSpace X] (μ : VectorMeasure X (ι → ℝ)) {E : Set X} (hE : MeasurableSet E)
    (h : euclideanVariation μ E = 0) : μ E = 0 := by
  rw [vectorMeasure_eq_setIntegral μ hE, Measure.restrict_eq_zero.2 h]
  simp

/-- The singular part is the restriction to a null set carrying it. -/
theorem lebesgueSingularPart_apply_eq {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    {N : Set (Vec d)} (hN : MeasurableSet N) (h0 : volume N = 0)
    (hac : (euclideanVariation Eu).restrict Nᶜ ≪ volume) {E : Set (Vec d)} (hE : MeasurableSet E) :
    lebesgueSingularPart Eu E = Eu (E ∩ N) := by
  rw [lebesgueSingularPart_eq_restrict Eu hN h0 hac, VectorMeasure.restrict_apply _ hN hE]

/-- The trace density `Σ_i polar(Eu)_{ii}`, tested: for a test function `φ`,
`∫ φ · tr polar d|Eu| = ∫_Ω g φ`. -/
theorem integral_trace_polar_eq {Ω : Set (Vec d)} {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu) {g : Vec d → ℝ}
    (hg : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ →
      ∫ x in Ω, ∑ i, u x i * euclideanCoordDeriv i φ x = -∫ x in Ω, g x * φ x)
    {φ : Vec d → ℝ} (hφ : IsTestFunctionOn Ω φ) :
    ∫ x, φ x * ∑ i, polar Eu x (i, i) ∂euclideanVariation Eu = ∫ x in Ω, g x * φ x := by
  rw [← sum_integral_diag_eq hEu hg hφ]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => integral_testFunction_polar Eu hφ (i, i)
  · intro i _
    exact BD.integrable_mul_of_test (integrable_polar_apply Eu (i, i)) hφ.1.continuous hφ.2.1

/-- `tr(Eu^s)` vanishes on Borel sets inside `Ω`. -/
theorem lebesgueSingularPart_trace_eq_zero_of_subset {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec d} {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    (hEu : IsBDGradientOn Ω u Eu) (hdiv : HasL2Divergence Ω u) {E : Set (Vec d)}
    (hE : MeasurableSet E) (hEΩ : E ⊆ Ω) :
    ∑ i, lebesgueSingularPart Eu E (i, i) = 0 := by
  obtain ⟨g, hg2, hg⟩ := hdiv
  obtain ⟨N, hN, h0, hac⟩ := exists_null_restrict_compl_ac (euclideanVariation Eu)
  have hP : Integrable (fun x => ∑ i, polar Eu x (i, i)) (euclideanVariation Eu) :=
    integrable_finsetSum _ fun i _ => integrable_polar_apply Eu (i, i)
  have hcore := BD.ae_eq_zero_on_null_of_test hΩ (euclideanVariation Eu) hP hg2
    (fun φ hφ => integral_trace_polar_eq hEu hg hφ) hN h0
  simp only [lebesgueSingularPart_apply_eq hN h0 hac hE]
  have hEN : MeasurableSet (E ∩ N) := hE.inter hN
  have : ∑ i, Eu (E ∩ N) (i, i) = ∫ x in E ∩ N, ∑ i, polar Eu x (i, i) ∂euclideanVariation Eu := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by
        rw [← coordMeasure_apply, coordMeasure_eq_setIntegral Eu (i, i) hEN]
    · intro i _
      exact (integrable_polar_apply Eu (i, i)).integrableOn
  rw [this]
  refine setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hcore] with x hx hxm
  exact hx hxm.2 (hEΩ hxm.1)

/-- `tr(Eu^s) = Σ_i (Eu_{ii})^s = 0` on all Borel sets. -/
theorem lebesgueSingularPart_trace_eq_zero {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {u : Vec d → Vec d} {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)}
    (hEu : IsBDGradientOn Ω u Eu) (hdiv : HasL2Divergence Ω u) {E : Set (Vec d)}
    (hE : MeasurableSet E) : ∑ i, lebesgueSingularPart Eu E (i, i) = 0 := by
  obtain ⟨N, hN, h0, hac⟩ := exists_null_restrict_compl_ac (euclideanVariation Eu)
  have hsplit : lebesgueSingularPart Eu E =
      lebesgueSingularPart Eu (E ∩ Ω) + lebesgueSingularPart Eu (E \ Ω) := by
    rw [← VectorMeasure.of_union (Set.disjoint_left.2 fun x h1 h2 => h2.2 h1.2)
      (hE.inter hΩ.measurableSet) (hE.diff hΩ.measurableSet), Set.inter_union_sdiff]
  have hoff : lebesgueSingularPart Eu (E \ Ω) = 0 := by
    rw [lebesgueSingularPart_apply_eq hN h0 hac (hE.diff hΩ.measurableSet)]
    refine vectorMeasure_eq_zero_of_variation_eq_zero Eu ((hE.diff hΩ.measurableSet).inter hN) ?_
    exact measure_mono_null (fun x hx => hx.1.2) hEu.2.1
  rw [hsplit, hoff, add_zero]
  exact lebesgueSingularPart_trace_eq_zero_of_subset hΩ hEu hdiv (hE.inter hΩ.measurableSet)
    Set.inter_subset_right

/-- If `div u = g ∈ L²(Ω)`, then `τ = Σ_i Eu_{ii}` has no singular part and
`tr(Eu^s) = Σ_i (Eu_{ii})^s = 0`. -/
theorem trace_singularPart_eq_zero {Ω : Set (Vec d)} (hΩ : IsOpen Ω) {u : Vec d → Vec d}
    {Eu : VectorMeasure (Vec d) (Fin d × Fin d → ℝ)} (hEu : IsBDGradientOn Ω u Eu)
    (hdiv : HasL2Divergence Ω u) :
    (∑ i, coordMeasure Eu (i, i)).singularPart volume = 0 ∧
      ∀ E, MeasurableSet E → ∑ i, lebesgueSingularPart Eu E (i, i) = 0 := by
  refine ⟨?_, fun E hE => lebesgueSingularPart_trace_eq_zero hΩ hEu hdiv hE⟩
  obtain ⟨N, hN, h0, hac⟩ := exists_null_restrict_compl_ac (euclideanVariation Eu)
  have hac' : (∑ i, coordMeasure Eu (i, i)) ≪ᵥ (volume : Measure (Vec d)).toENNRealVectorMeasure := by
    intro E hE
    by_cases hm : MeasurableSet E
    · rw [Measure.toENNRealVectorMeasure_apply_measurable hm] at hE
      have h1 : euclideanVariation Eu (E ∩ Nᶜ) = 0 := by
        have := hac hE
        rwa [Measure.restrict_apply' hN.compl] at this
      have h2 : Eu (E ∩ Nᶜ) = 0 :=
        vectorMeasure_eq_zero_of_variation_eq_zero Eu (hm.inter hN.compl) h1
      have h3 := lebesgueSingularPart_trace_eq_zero hΩ hEu hdiv hm
      rw [lebesgueSingularPart_apply_eq hN h0 hac hm] at h3
      have h4 : Eu E = Eu (E ∩ N) + Eu (E ∩ Nᶜ) := by
        rw [← VectorMeasure.of_union (Set.disjoint_left.2 fun x h1 h2 => h2.2 h1.2)
          (hm.inter hN) (hm.inter hN.compl), ← Set.inter_union_distrib_left, Set.union_compl_self,
          Set.inter_univ]
      rw [sum_apply_signed]
      simp only [coordMeasure_apply]
      rw [h4, h2, add_zero]
      exact h3
    · exact VectorMeasure.not_measurable _ hm
  have h := SignedMeasure.singularPart_add_withDensity_rnDeriv_eq
    (s := ∑ i, coordMeasure Eu (i, i)) (μ := (volume : Measure (Vec d)))
  rw [SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac'] at h
  exact add_eq_right.1 h

end AFree
