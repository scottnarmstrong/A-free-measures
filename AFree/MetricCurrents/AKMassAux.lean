module

public import AFree.MetricCurrents.LipApprox
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Auxiliary lemmas for the existence of the mass: Lipschitz algebra and the pairwise infimum
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKMassAux

open PDE AFree

variable {d : ℕ}

theorem continuous_of_eucl {K : ℝ≥0} {f : Vec d → ℝ} (hf : IsEuclLipschitzWith K f) :
    Continuous f := by
  have : LipschitzWith (K * (Real.sqrt d).toNNReal) f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    calc |f x - f y| ≤ K * vecEuclideanNorm (x - y) := hf x y
      _ ≤ K * (Real.sqrt d * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) K.2
      _ = _ := by rw [NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]; ring
  exact this.continuous

theorem measurable_of_bddLip {f : Vec d → ℝ} (hf : IsBddLipFun f) : Measurable f := by
  obtain ⟨K, hK⟩ := hf.1
  exact (continuous_of_eucl hK).measurable

theorem isBddLip_mul {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g) :
    IsBddLipFun (fun x => f x * g x) := by
  obtain ⟨⟨Kf, hKf⟩, Cf, hCf⟩ := hf
  obtain ⟨⟨Kg, hKg⟩, Cg, hCg⟩ := hg
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hCg0 : 0 ≤ Cg := (abs_nonneg _).trans (hCg 0)
  refine ⟨⟨Cf.toNNReal * Kg + Cg.toNNReal * Kf, fun x y => ?_⟩, Cf * Cg, fun x => ?_⟩
  · have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [e]
    calc |f x * (g x - g y) + g y * (f x - f y)|
        ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
      _ ≤ Cf * (Kg * vecEuclideanNorm (x - y)) + Cg * (Kf * vecEuclideanNorm (x - y)) :=
        add_le_add (mul_le_mul (hCf x) (hKg x y) (abs_nonneg _) hCf0)
          (mul_le_mul (hCg y) (hKf x y) (abs_nonneg _) hCg0)
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hCf0, Real.coe_toNNReal _ hCg0]; ring
  · rw [abs_mul]; exact mul_le_mul (hCf x) (hCg x) (abs_nonneg _) hCf0

theorem isBddLip_one_sub {g : Vec d → ℝ} (hg : IsBddLipFun g) :
    IsBddLipFun (fun x => 1 - g x) := by
  obtain ⟨⟨Kg, hKg⟩, Cg, hCg⟩ := hg
  refine ⟨⟨Kg, fun x y => ?_⟩, 1 + Cg, fun x => ?_⟩
  · have : (1 - g x) - (1 - g y) = -(g x - g y) := by ring
    rw [this, abs_neg]; exact hKg x y
  · calc |1 - g x| ≤ |1| + |g x| := abs_sub _ _
      _ ≤ 1 + Cg := by simpa using hCg x

theorem integrable_of_bdd {m : Measure (Vec d)} [IsFiniteMeasure m] {g : Vec d → ℝ}
    (hg : Measurable g) {C : ℝ} (h : ∀ x, |g x| ≤ C) : Integrable g m :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    simpa using h x)

theorem split_apply (μ : Measure (Vec d)) {E B : Set (Vec d)} (hB : MeasurableSet B) :
    μ E = μ (E ∩ B) + μ (E ∩ Bᶜ) := by
  rw [← measure_inter_add_sdiff E hB, Set.sdiff_eq]

theorem integrable_abs_of_bdd {m : Measure (Vec d)} [IsFiniteMeasure m] {g : Vec d → ℝ}
    (hg : Measurable g) {C : ℝ} (h : ∀ x, |g x| ≤ C) : Integrable (fun x => |g x|) m :=
  integrable_of_bdd (continuous_abs.measurable.comp hg) (C := C) fun x => by simpa using h x

/-- Step 1 of the existence of the mass. -/
theorem pairwise_infimum (μ₁ μ₂ : Measure (Vec d)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    ∃ B : Set (Vec d), MeasurableSet B ∧ μ₁.restrict B + μ₂.restrict Bᶜ ≤ μ₁ ∧
      μ₁.restrict B + μ₂.restrict Bᶜ ≤ μ₂ ∧
      ∀ κ : Measure (Vec d), κ ≤ μ₁ → κ ≤ μ₂ → κ ≤ μ₁.restrict B + μ₂.restrict Bᶜ := by
  set lam := μ₁ + μ₂ with hlam
  have h1 : μ₁ ≪ lam := Measure.AbsolutelyContinuous.mk fun s _ h =>
    le_antisymm ((Measure.le_add_right (le_refl μ₁) s).trans h.le) bot_le
  have h2 : μ₂ ≪ lam := Measure.AbsolutelyContinuous.mk fun s _ h =>
    le_antisymm ((Measure.le_add_left (le_refl μ₂) s).trans h.le) bot_le
  set g₁ := μ₁.rnDeriv lam
  set g₂ := μ₂.rnDeriv lam
  have m1 : Measurable g₁ := Measure.measurable_rnDeriv _ _
  have m2 : Measurable g₂ := Measure.measurable_rnDeriv _ _
  have hB : MeasurableSet {x | g₁ x ≤ g₂ x} := measurableSet_le m1 m2
  refine ⟨{x | g₁ x ≤ g₂ x}, hB, ?_, ?_, ?_⟩
  · refine Measure.le_iff.2 fun E hE => ?_
    simp only [Measure.add_apply, Measure.restrict_apply hE]
    rw [split_apply μ₁ (E := E) hB]
    refine add_le_add le_rfl ?_
    rw [← Measure.setLIntegral_rnDeriv h1, ← Measure.setLIntegral_rnDeriv h2]
    refine setLIntegral_mono m1 fun x hx => ?_
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    exact hx.2.le
  · refine Measure.le_iff.2 fun E hE => ?_
    simp only [Measure.add_apply, Measure.restrict_apply hE]
    rw [split_apply μ₂ (E := E) hB]
    refine add_le_add ?_ le_rfl
    rw [← Measure.setLIntegral_rnDeriv h1, ← Measure.setLIntegral_rnDeriv h2]
    refine setLIntegral_mono m2 fun x hx => ?_
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    exact hx.2
  · intro κ k1 k2
    refine Measure.le_iff.2 fun E hE => ?_
    simp only [Measure.add_apply, Measure.restrict_apply hE]
    rw [split_apply κ (E := E) hB]
    exact add_le_add (k1 _) (k2 _)

variable {k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}

/-- Pointwise estimates for the cut-off. -/
theorem pt_le_one {a C : ℝ} (B : Set (Vec d)) (x : Vec d) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (ha : |a| ≤ C) :
    |a * φ| ≤ |a| * B.indicator (1 : Vec d → ℝ) x + C * |φ - B.indicator 1 x| := by
  have hC : 0 ≤ C := (abs_nonneg _).trans ha
  by_cases hx : x ∈ B
  · simp only [Set.indicator_of_mem hx, Pi.one_apply]
    rw [abs_mul, abs_of_nonneg hφ0]
    nlinarith [abs_nonneg a, abs_nonneg (φ - 1), mul_nonneg hC (abs_nonneg (φ - 1))]
  · simp only [Set.indicator_of_notMem hx, mul_zero, sub_zero]
    rw [abs_mul, abs_of_nonneg hφ0, zero_add]
    nlinarith [abs_nonneg a]

theorem pt_one_sub {a C : ℝ} (B : Set (Vec d)) (x : Vec d) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (ha : |a| ≤ C) :
    |a * (1 - φ)| ≤ |a| * Bᶜ.indicator (1 : Vec d → ℝ) x + C * |φ - B.indicator 1 x| := by
  have hC : 0 ≤ C := (abs_nonneg _).trans ha
  by_cases hx : x ∈ B
  · have : x ∉ Bᶜ := fun h => h hx
    simp only [Set.indicator_of_mem hx, Set.indicator_of_notMem this, Pi.one_apply, mul_zero,
      zero_add]
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - φ), abs_sub_comm φ 1,
      abs_of_nonneg (by linarith : 0 ≤ 1 - φ)]
    nlinarith [abs_nonneg a]
  · have : x ∈ Bᶜ := hx
    simp only [Set.indicator_of_notMem hx, Set.indicator_of_mem this, Pi.one_apply, sub_zero,
      mul_one]
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - φ), abs_of_nonneg hφ0]
    nlinarith [abs_nonneg a, mul_nonneg hC hφ0]

/-- Step 2 of the existence of the mass. -/
theorem pairwise_admissible (hT : IsMetricFunctional k T) {μ₁ μ₂ : Measure (Vec d)}
    (h₁ : IsAKMassAdmissible T μ₁) (h₂ : IsAKMassAdmissible T μ₂) {B : Set (Vec d)}
    (hB : MeasurableSet B) : IsAKMassAdmissible T (μ₁.restrict B + μ₂.restrict Bᶜ) := by
  obtain ⟨hf1, hb1⟩ := h₁
  obtain ⟨hf2, hb2⟩ := h₂
  refine ⟨inferInstance, fun f hf π K hK => ?_⟩
  set lam := μ₁ + μ₂ with hlam
  have hl1 : μ₁ ≤ lam := Measure.le_add_right le_rfl
  have hl2 : μ₂ ≤ lam := Measure.le_add_left le_rfl
  obtain ⟨Cf, hCf⟩ := hf.2
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hfm := measurable_of_bddLip hf
  have hfa : Measurable fun x => |f x| := continuous_abs.measurable.comp hfm
  have hπ : ∀ i, IsLipFun (π i) := fun i => ⟨K i, hK i⟩
  set P : ℝ := ∏ i, (K i : ℝ) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => (K i).2
  have hBm : Measurable (B.indicator (1 : Vec d → ℝ)) := measurable_const.indicator hB
  have hBc : Measurable (Bᶜ.indicator (1 : Vec d → ℝ)) := measurable_const.indicator hB.compl
  -- the integral of |f| against the sum
  have hint : ∫ x, |f x| ∂(μ₁.restrict B + μ₂.restrict Bᶜ) =
      ∫ x, |f x| * B.indicator (1 : Vec d → ℝ) x ∂μ₁ +
        ∫ x, |f x| * Bᶜ.indicator (1 : Vec d → ℝ) x ∂μ₂ := by
    have i1 : Integrable (fun x => |f x|) (μ₁.restrict B) :=
      integrable_of_bdd hfa (C := Cf) (by simpa using hCf)
    have i2 : Integrable (fun x => |f x|) (μ₂.restrict Bᶜ) :=
      integrable_of_bdd hfa (C := Cf) (by simpa using hCf)
    rw [integral_add_measure i1 i2]
    congr 1
    · rw [← integral_indicator hB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ B <;> simp [Set.indicator_of_mem, hx]
    · rw [← integral_indicator hB.compl]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ Bᶜ <;> simp [hx]
  rw [hint]
  have key : ∀ η : ℝ, 0 < η → |T f π| ≤ P * (∫ x, |f x| * B.indicator (1 : Vec d → ℝ) x ∂μ₁ +
        ∫ x, |f x| * Bᶜ.indicator (1 : Vec d → ℝ) x ∂μ₂) + P * (2 * Cf * η) := by
    intro η hη
    obtain ⟨F, F', φ, -, -, -, -, hφ, h01, -, -, -, hint'⟩ :=
      exists_lip_approx_indicator lam hB hη
    have hφm := measurable_of_bddLip hφ
    obtain ⟨Cφ, hCφ⟩ := hφ.2
    have hfφ := isBddLip_mul hf hφ
    have hf1φ := isBddLip_one_sub hφ
    have hff := isBddLip_mul hf hf1φ
    have hsplit : f = (fun x => f x * φ x) + (fun x => f x * (1 - φ x)) := by
      funext x; simp only [Pi.add_apply]; ring
    have hMF := hT.1 _ _ hfφ hff π hπ
    rw [← hsplit] at hMF
    have e1 := hb1 _ hfφ π K hK
    have e2 := hb2 _ hff π K hK
    -- control of the φ-error
    have hd0 : Measurable fun x => φ x - B.indicator (1 : Vec d → ℝ) x := hφm.sub hBm
    have hd : Measurable fun x => |φ x - B.indicator (1 : Vec d → ℝ) x| :=
      continuous_abs.measurable.comp hd0
    have hdb : ∀ x, |φ x - B.indicator (1 : Vec d → ℝ) x| ≤ Cφ + 1 := fun x => by
      calc _ ≤ |φ x| + |B.indicator (1 : Vec d → ℝ) x| := abs_sub _ _
        _ ≤ Cφ + 1 := add_le_add (hCφ x) (by
            by_cases hx : x ∈ B <;> simp [hx])
    have hdl : Integrable (fun x => |φ x - B.indicator (1 : Vec d → ℝ) x|) lam :=
      integrable_abs_of_bdd hd0 hdb
    have hd1 : ∫ x, |φ x - B.indicator (1 : Vec d → ℝ) x| ∂μ₁ ≤ η :=
      (integral_mono_measure hl1 (Filter.Eventually.of_forall fun x => abs_nonneg _) hdl).trans
        hint'.le
    have hd2 : ∫ x, |φ x - B.indicator (1 : Vec d → ℝ) x| ∂μ₂ ≤ η :=
      (integral_mono_measure hl2 (Filter.Eventually.of_forall fun x => abs_nonneg _) hdl).trans
        hint'.le
    have hI1 : Integrable (fun x => |f x| * B.indicator (1 : Vec d → ℝ) x) μ₁ :=
      integrable_of_bdd (g := fun x => |f x| * B.indicator (1 : Vec d → ℝ) x)
        (hfa.mul hBm) (C := Cf) fun x => by
          by_cases hx : x ∈ B <;> simp [hx, hCf0, hCf x]
    have hI2 : Integrable (fun x => |f x| * Bᶜ.indicator (1 : Vec d → ℝ) x) μ₂ :=
      integrable_of_bdd (g := fun x => |f x| * Bᶜ.indicator (1 : Vec d → ℝ) x)
        (hfa.mul hBc) (C := Cf) fun x => by
          by_cases hx : x ∈ Bᶜ <;> simp [hx, hCf0, hCf x]
    have bnd : ∀ (m : Measure (Vec d)) [IsFiniteMeasure m] (g : Vec d → ℝ) (hg : Measurable g)
        (Cg : ℝ) (_ : ∀ x, |g x| ≤ Cg), Integrable g m := fun m _ g hg Cg h =>
      integrable_of_bdd hg h
    have a1 : ∫ x, |f x * φ x| ∂μ₁ ≤ ∫ x, |f x| * B.indicator (1 : Vec d → ℝ) x ∂μ₁ +
        Cf * η := by
      calc ∫ x, |f x * φ x| ∂μ₁
          ≤ ∫ x, (|f x| * B.indicator (1 : Vec d → ℝ) x +
              Cf * |φ x - B.indicator (1 : Vec d → ℝ) x|) ∂μ₁ := by
            refine integral_mono (integrable_abs_of_bdd (hfm.mul hφm) (C := Cf * Cφ) fun x => ?_)
              ?_ fun x => pt_le_one B x (h01 x).1 (h01 x).2 (hCf x)
            · simp only [abs_mul]
              exact mul_le_mul (hCf x) (hCφ x) (abs_nonneg _) hCf0
            · exact hI1.add
                ((integrable_abs_of_bdd hd0 hdb).const_mul Cf)
        _ ≤ _ := by
            rw [integral_add hI1
              ((integrable_abs_of_bdd hd0 hdb).const_mul Cf), integral_const_mul]
            have := mul_le_mul_of_nonneg_left hd1 hCf0
            linarith
    have a2 : ∫ x, |f x * (1 - φ x)| ∂μ₂ ≤
        ∫ x, |f x| * Bᶜ.indicator (1 : Vec d → ℝ) x ∂μ₂ + Cf * η := by
      calc ∫ x, |f x * (1 - φ x)| ∂μ₂
          ≤ ∫ x, (|f x| * Bᶜ.indicator (1 : Vec d → ℝ) x +
              Cf * |φ x - B.indicator (1 : Vec d → ℝ) x|) ∂μ₂ := by
            refine integral_mono (integrable_abs_of_bdd
                (hfm.mul (measurable_const.sub hφm)) (C := Cf * (1 + Cφ)) fun x => ?_)
              ?_ fun x => pt_one_sub B x (h01 x).1 (h01 x).2 (hCf x)
            · simp only [abs_mul]
              refine mul_le_mul (hCf x) ?_ (abs_nonneg _) hCf0
              calc |1 - φ x| ≤ |1| + |φ x| := abs_sub _ _
                _ ≤ 1 + Cφ := by simpa using hCφ x
            · exact hI2.add
                ((integrable_abs_of_bdd hd0 hdb).const_mul Cf)
        _ ≤ _ := by
            rw [integral_add hI2
              ((integrable_abs_of_bdd hd0 hdb).const_mul Cf), integral_const_mul]
            have := mul_le_mul_of_nonneg_left hd2 hCf0
            linarith
    calc |T f π| ≤ |T (fun x => f x * φ x) π| + |T (fun x => f x * (1 - φ x)) π| := hMF
      _ ≤ P * ∫ x, |f x * φ x| ∂μ₁ + P * ∫ x, |f x * (1 - φ x)| ∂μ₂ := add_le_add e1 e2
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left a1 hP0, mul_le_mul_of_nonneg_left a2 hP0]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set a : ℝ := 2 * P * Cf with ha
  have ha0 : 0 ≤ a := by positivity
  have := key (ε / (a + 1)) (by positivity)
  refine this.trans ?_
  have hle : P * (2 * Cf * (ε / (a + 1))) ≤ ε := by
    have : P * (2 * Cf * (ε / (a + 1))) = ε * (a / (a + 1)) := by
      rw [ha]; field_simp
    rw [this]
    have : a / (a + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    nlinarith
  linarith

end AFree.MetricCurrents.AKMassAux
