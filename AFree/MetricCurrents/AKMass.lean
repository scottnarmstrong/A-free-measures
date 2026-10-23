module

public import AFree.MetricCurrents.AKMassAux

/-!
# The mass of a metric functional [AK, Definition 2.6]

A metric functional with an admissible measure has a unique minimal admissible measure, the mass.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

variable {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}

/-- Step 1. For finite measures `μ₁, μ₂` there is a Borel set `B`
(namely `{g₁ ≤ g₂}`) such that `ν = μ₁⌞B + μ₂⌞Bᶜ` is finite, `ν ≤ μ₁`, `ν ≤ μ₂`, and `ν` is the greatest
lower bound of `μ₁, μ₂` among measures. -/
theorem akmass_pairwise_infimum (μ₁ μ₂ : Measure (Vec d)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    ∃ B : Set (Vec d), MeasurableSet B ∧ μ₁.restrict B + μ₂.restrict Bᶜ ≤ μ₁ ∧
      μ₁.restrict B + μ₂.restrict Bᶜ ≤ μ₂ ∧
      ∀ κ : Measure (Vec d), κ ≤ μ₁ → κ ≤ μ₂ → κ ≤ μ₁.restrict B + μ₂.restrict Bᶜ :=
  MetricCurrents.AKMassAux.pairwise_infimum μ₁ μ₂

/-- Step 2. If `μ₁, μ₂` are admissible, so is `μ₁⌞B + μ₂⌞Bᶜ`
for every Borel set `B` (uses (MF1) only). -/
theorem akmass_pairwise_admissible (hT : IsMetricFunctional k T) {μ₁ μ₂ : Measure (Vec d)}
    (h₁ : IsAKMassAdmissible T μ₁) (h₂ : IsAKMassAdmissible T μ₂) {B : Set (Vec d)}
    (hB : MeasurableSet B) : IsAKMassAdmissible T (μ₁.restrict B + μ₂.restrict Bᶜ) :=
  MetricCurrents.AKMassAux.pairwise_admissible hT h₁ h₂ hB

private theorem split_total (μ : Measure (Vec d)) (E : Set (Vec d)) (hE : MeasurableSet E) :
    μ Set.univ = μ E + μ Eᶜ := by
  exact (measure_add_measure_compl hE).symm

/-- Admissible measures are closed under the greatest lower bound of two of them. -/
private theorem exists_inf_admissible (hT : IsMetricFunctional k T) {μ₁ μ₂ : Measure (Vec d)}
    (h₁ : IsAKMassAdmissible T μ₁) (h₂ : IsAKMassAdmissible T μ₂) :
    ∃ ν, IsAKMassAdmissible T ν ∧ ν ≤ μ₁ ∧ ν ≤ μ₂ ∧ ∀ κ, κ ≤ μ₁ → κ ≤ μ₂ → κ ≤ ν := by
  have := h₁.1
  have := h₂.1
  obtain ⟨B, hB, a, b, c⟩ := akmass_pairwise_infimum μ₁ μ₂
  exact ⟨_, akmass_pairwise_admissible hT h₁ h₂ hB, a, b, c⟩

/-- The setwise infimum of a decreasing sequence of finite measures is a measure. -/
private theorem exists_iInf_measure {ν : ℕ → Measure (Vec d)} [∀ n, IsFiniteMeasure (ν n)]
    (hanti : ∀ n, ν (n + 1) ≤ ν n) :
    ∃ νlim : Measure (Vec d), ∀ E, MeasurableSet E → νlim E = ⨅ n, ν n E := by
  have anti : Antitone ν := antitone_nat_of_succ_le hanti
  refine ⟨Measure.ofMeasurable (fun E _ => ⨅ n, ν n E) (by simp) ?_,
    fun E hE => Measure.ofMeasurable_apply E hE⟩
  intro f hf hd
  have h1 : ∀ n, ν n (⋃ i, f i) = ∫⁻ i, ν n (f i) ∂Measure.count := fun n => by
    rw [measure_iUnion hd hf, lintegral_count]
  simp_rw [h1]
  have key := lintegral_iInf (μ := (Measure.count : Measure ℕ)) (f := fun n i => ν n (f i))
    (fun n => measurable_from_top) (fun n m h i => Measure.le_iff'.1 (anti h) _)
    (by rw [← h1]; exact measure_ne_top _ _)
  rw [← key, lintegral_count]

/-- Comparison of integrals against nested finite measures. -/
private theorem integral_le_of_le {ν νlim : Measure (Vec d)} [IsFiniteMeasure ν]
    [IsFiniteMeasure νlim] (hle : νlim ≤ ν) {f : Vec d → ℝ} (hfm : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∫ x, |f x| ∂ν ≤ ∫ x, |f x| ∂νlim + C * ((ν Set.univ).toReal - (νlim Set.univ).toReal) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hfa : Measurable fun x => |f x| := continuous_abs.measurable.comp hfm
  set ρ := ν - νlim with hρ
  have hsum : ρ + νlim = ν := Measure.sub_add_cancel_of_le hle
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le ν (Measure.sub_le)
  have iρ : Integrable (fun x => |f x|) ρ := MetricCurrents.AKMassAux.integrable_of_bdd hfa
    (C := C) (by simpa using hC)
  have iL : Integrable (fun x => |f x|) νlim := MetricCurrents.AKMassAux.integrable_of_bdd hfa
    (C := C) (by simpa using hC)
  have e1 : ∫ x, |f x| ∂ν = ∫ x, |f x| ∂ρ + ∫ x, |f x| ∂νlim := by
    rw [← hsum, integral_add_measure iρ iL]
  have e2 : ∫ x, |f x| ∂ρ ≤ C * (ν Set.univ).toReal - C * (νlim Set.univ).toReal := by
    have h3 : ∫ x, |f x| ∂ρ ≤ ∫ _x, C ∂ρ :=
      integral_mono iρ (integrable_const C) fun x => hC x
    rw [integral_const, smul_eq_mul] at h3
    have h4 : (ρ Set.univ).toReal = (ν Set.univ).toReal - (νlim Set.univ).toReal := by
      have := congrArg (fun m : Measure (Vec d) => (m Set.univ).toReal) hsum
      simp only [Measure.add_apply] at this
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
      linarith
    rw [Measure.real, h4] at h3
    linarith
  linarith

/-- Step 3. If some admissible measure exists there are
admissible `ν n`, decreasing, and a finite measure `νlim` with `νlim ≤ ν n`, `ν n E → νlim E` for every Borel
`E`, and total mass `νlim univ ≤ μ univ` for every admissible `μ`. -/
theorem akmass_decreasing_limit (hT : IsMetricFunctional k T) (hfin : ∃ μ, IsAKMassAdmissible T μ) :
    ∃ (ν : ℕ → Measure (Vec d)) (νlim : Measure (Vec d)), (∀ n, IsAKMassAdmissible T (ν n)) ∧
      (∀ n, ν (n + 1) ≤ ν n) ∧ (∀ n, νlim ≤ ν n) ∧ IsFiniteMeasure νlim ∧
      (∀ E, MeasurableSet E → Tendsto (fun n => ν n E) atTop (𝓝 (νlim E))) ∧
      ∀ μ, IsAKMassAdmissible T μ → νlim Set.univ ≤ μ Set.univ := by
  classical
  obtain ⟨μ₀, hμ₀⟩ := hfin
  have hμ₀f := hμ₀.1
  set m₀ : ℝ≥0∞ := ⨅ μ : {μ : Measure (Vec d) // IsAKMassAdmissible T μ}, μ.1 Set.univ with hm₀
  have hm₀top : m₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top μ₀ Set.univ) (iInf_le (fun μ : {μ : Measure (Vec d) //
      IsAKMassAdmissible T μ} => μ.1 Set.univ) ⟨μ₀, hμ₀⟩)
  have hex : ∀ n : ℕ, ∃ μ, IsAKMassAdmissible T μ ∧ μ Set.univ < m₀ + (n : ℝ≥0∞)⁻¹ := by
    intro n
    have : m₀ < m₀ + (n : ℝ≥0∞)⁻¹ :=
      ENNReal.lt_add_right hm₀top (by simp)
    obtain ⟨μ, hμ⟩ := iInf_lt_iff.1 this
    exact ⟨μ.1, μ.2, hμ⟩
  choose μs hμs hμs' using hex
  let s : ℕ → {μ : Measure (Vec d) // IsAKMassAdmissible T μ} :=
    fun n => Nat.rec (motive := fun _ => {μ : Measure (Vec d) // IsAKMassAdmissible T μ})
      ⟨μs 0, hμs 0⟩
      (fun n sn => ⟨(exists_inf_admissible hT sn.2 (hμs (n + 1))).choose,
        (exists_inf_admissible hT sn.2 (hμs (n + 1))).choose_spec.1⟩) n
  have hs0 : (s 0).1 = μs 0 := rfl
  have hsn : ∀ n, (s (n + 1)).1 = (exists_inf_admissible hT (s n).2 (hμs (n + 1))).choose :=
    fun n => rfl
  have hanti : ∀ n, (s (n + 1)).1 ≤ (s n).1 := fun n => by
    rw [hsn]; exact (exists_inf_admissible hT (s n).2 (hμs (n + 1))).choose_spec.2.1
  have hle : ∀ n, (s n).1 ≤ μs n := fun n => by
    cases n with
    | zero => rw [hs0]
    | succ n =>
      rw [hsn]; exact (exists_inf_admissible hT (s n).2 (hμs (n + 1))).choose_spec.2.2.1
  have hfinite : ∀ n, IsFiniteMeasure (s n).1 := fun n => (s n).2.1
  obtain ⟨νlim, hνlim⟩ := exists_iInf_measure (ν := fun n => (s n).1) hanti
  have anti : Antitone fun n => (s n).1 := antitone_nat_of_succ_le hanti
  have hlel : ∀ n, νlim ≤ (s n).1 := fun n => Measure.le_iff.2 fun E hE => by
    rw [hνlim E hE]; exact iInf_le (fun n => (s n).1 E) n
  have := hfinite 0
  have hfl : IsFiniteMeasure νlim := isFiniteMeasure_of_le _ (hlel 0)
  have htend : ∀ E, MeasurableSet E → Tendsto (fun n => (s n).1 E) atTop (𝓝 (νlim E)) := by
    intro E hE
    rw [hνlim E hE]
    exact tendsto_atTop_iInf fun a b h => Measure.le_iff'.1 (anti h) E
  refine ⟨fun n => (s n).1, νlim, fun n => (s n).2, hanti, hlel, hfl, htend, fun μ hμ => ?_⟩
  have h1 : νlim Set.univ ≤ m₀ := by
    have hlim : Tendsto (fun n : ℕ => m₀ + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (m₀ + 0)) :=
      tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    exact ((Measure.le_iff'.1 (hlel n) Set.univ).trans
      (Measure.le_iff'.1 (hle n) Set.univ)).trans (hμs' n).le
  exact h1.trans (iInf_le (fun μ : {μ : Measure (Vec d) // IsAKMassAdmissible T μ} =>
    μ.1 Set.univ) ⟨μ, hμ⟩)

/-- Step 4. A setwise limit `νlim` of a decreasing sequence of
admissible measures (with `ν₀` finite) is admissible. -/
theorem akmass_limit_admissible {ν : ℕ → Measure (Vec d)} {νlim : Measure (Vec d)}
    (hadm : ∀ n, IsAKMassAdmissible T (ν n)) (hanti : ∀ n, ν (n + 1) ≤ ν n)
    [IsFiniteMeasure νlim]
    (hlim : ∀ E, MeasurableSet E → Tendsto (fun n => ν n E) atTop (𝓝 (νlim E))) :
    IsAKMassAdmissible T νlim := by
  have anti : Antitone ν := antitone_nat_of_succ_le hanti
  have hle : ∀ n, νlim ≤ ν n := fun n => Measure.le_iff.2 fun E hE =>
    le_of_tendsto (hlim E hE) (eventually_atTop.2 ⟨n, fun m hm => Measure.le_iff'.1 (anti hm) E⟩)
  refine ⟨inferInstance, fun f hf π K hK => ?_⟩
  obtain ⟨Cf, hCf⟩ := hf.2
  have hfm := MetricCurrents.AKMassAux.measurable_of_bddLip hf
  have hP0 : 0 ≤ ∏ i, (K i : ℝ) := Finset.prod_nonneg fun i _ => (K i).2
  have hbound : ∀ n, |T f π| ≤ (∏ i, (K i : ℝ)) * (∫ x, |f x| ∂νlim +
      Cf * ((ν n Set.univ).toReal - (νlim Set.univ).toReal)) := fun n => by
    have := (hadm n).1
    refine ((hadm n).2 f hf π K hK).trans (mul_le_mul_of_nonneg_left ?_ hP0)
    exact integral_le_of_le (hle n) hfm hCf
  have ht : Tendsto (fun n => (ν n Set.univ).toReal) atTop (𝓝 (νlim Set.univ).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hlim _ MeasurableSet.univ)
  have ht2 : Tendsto (fun n => (∏ i, (K i : ℝ)) * (∫ x, |f x| ∂νlim +
      Cf * ((ν n Set.univ).toReal - (νlim Set.univ).toReal))) atTop
      (𝓝 ((∏ i, (K i : ℝ)) * (∫ x, |f x| ∂νlim + Cf * ((νlim Set.univ).toReal -
        (νlim Set.univ).toReal)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.mul (ht.sub tendsto_const_nhds)))
  have := ge_of_tendsto' ht2 hbound
  simpa using this

/-- Step 5. If `νlim` is admissible with minimal total mass among admissible
measures and admissible measures are closed under the pairwise infimum `μ₁⌞B + μ₂⌞Bᶜ`, then `νlim` is
the least admissible measure. -/
theorem akmass_minimal (hT : IsMetricFunctional k T) {νlim : Measure (Vec d)}
    (hadm : IsAKMassAdmissible T νlim)
    (hmin : ∀ μ, IsAKMassAdmissible T μ → νlim Set.univ ≤ μ Set.univ) : IsAKMass T νlim := by
  refine ⟨hadm, fun κ hκ => ?_⟩
  obtain ⟨ν, hν, h1, h2, -⟩ := exists_inf_admissible hT hadm hκ
  have hνf := hν.1
  have hlf := hadm.1
  have hm := hmin ν hν
  refine le_trans (Measure.le_iff.2 fun E hE => ?_) h2
  have a1 := split_total ν E hE
  have a2 := split_total νlim E hE
  have b1 := Measure.le_iff'.1 h1 E
  have b2 := Measure.le_iff'.1 h1 Eᶜ
  have : νlim E + νlim Eᶜ ≤ ν E + ν Eᶜ := by rw [← a1, ← a2]; exact hm
  have c : νlim E + νlim Eᶜ ≤ ν E + νlim Eᶜ := this.trans (add_le_add le_rfl b2)
  exact (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).1 c

/-- [AK, Definition 2.6] If `T` is a metric functional with some admissible measure, there is a
mass measure; it is unique; and the infimum of two admissible measures is admissible. -/
theorem akmass (hT : IsMetricFunctional k T) (hfin : ∃ μ, IsAKMassAdmissible T μ) :
    (∃ μ, IsAKMass T μ) ∧ (∀ μ ν, IsAKMass T μ → IsAKMass T ν → μ = ν) ∧
    (∀ μ₁ μ₂, IsAKMassAdmissible T μ₁ → IsAKMassAdmissible T μ₂ →
      ∃ ν, IsAKMassAdmissible T ν ∧ ν ≤ μ₁ ∧ ν ≤ μ₂ ∧ ∀ κ, κ ≤ μ₁ → κ ≤ μ₂ → κ ≤ ν) := by
  refine ⟨?_, fun μ ν hμ hν => le_antisymm (hμ.2 ν hν.1) (hν.2 μ hμ.1),
    fun μ₁ μ₂ h₁ h₂ => exists_inf_admissible hT h₁ h₂⟩
  obtain ⟨ν, νlim, hadm, hanti, -, hfl, hlim, hmin⟩ := akmass_decreasing_limit hT hfin
  have := akmass_limit_admissible hadm hanti hlim
  exact ⟨νlim, akmass_minimal hT this hmin⟩

end AFree
