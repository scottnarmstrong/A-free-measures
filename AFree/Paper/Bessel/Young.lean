module

public import AFree.Defs
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Young's inequality `L^p ⋆ L^1`

For `κ ∈ L^p` and `f ∈ L^1` we prove `‖κ ⋆ f‖_p ≤ ‖κ‖_p ‖f‖_1` by Minkowski's integral inequality
(a Jensen step against the finite measure `|f| dy`, then Tonelli and translation invariance),
and build the convolution operator `L^1 → L^p` as a continuous linear map.
-/

@[expose] public section

open MeasureTheory ENNReal
open scoped ENNReal

namespace AFree.Bessel

open PDE

variable {d : ℕ}

/-- Jensen's inequality for a convex power, in `ℝ≥0∞`: `(∫ g dν)^q ≤ ν(univ)^{q-1} ∫ g^q dν`. -/
theorem lintegral_rpow_le_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ≥0∞}
    (hg : AEMeasurable g ν) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ a, g a ∂ν) ^ q ≤ ν Set.univ ^ (q - 1) * ∫⁻ a, g a ^ q ∂ν := by
  rcases hq.eq_or_lt with rfl | hq1
  · simp
  have hq0 : 0 < q := by linarith
  set q' : ℝ := q / (q - 1) with hq'
  have hconj : q.HolderConjugate q' := by
    rw [Real.holderConjugate_iff]
    refine ⟨hq1, ?_⟩
    rw [hq']; field_simp; ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj hg (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h2 := ENNReal.rpow_le_rpow h hq0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : 1 / q * q = 1 := by field_simp
  have e2 : 1 / q' * q = q - 1 := by rw [hq']; field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  simp only [Pi.mul_apply, mul_one] at h2
  rwa [mul_comm] at h2

/-- The weighted form: `(∫ g w)^q ≤ (∫ w)^{q-1} ∫ g^q w`. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {g w : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) (hw : AEMeasurable w μ) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ a, g a * w a ∂μ) ^ q ≤ (∫⁻ a, w a ∂μ) ^ (q - 1) * ∫⁻ a, g a ^ q * w a ∂μ := by
  have hgν : AEMeasurable g (μ.withDensity w) := hg.mono_ac (withDensity_absolutelyContinuous μ w)
  have h := lintegral_rpow_le_mul hgν hq
  have e1 : ∫⁻ a, g a ∂(μ.withDensity w) = ∫⁻ a, w a * g a ∂μ :=
    lintegral_withDensity_eq_lintegral_mul₀ hw hg
  have hgq : AEMeasurable (fun a => g a ^ q) μ := hg.pow_const q
  have e2 : ∫⁻ a, g a ^ q ∂(μ.withDensity w) = ∫⁻ a, w a * g a ^ q ∂μ :=
    lintegral_withDensity_eq_lintegral_mul₀ hw hgq
  have e3 : (μ.withDensity w) Set.univ = ∫⁻ a, w a ∂μ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [e1, e2, e3] at h
  simpa only [mul_comm] using h

/-- The convolution `(κ ⋆ f)(x) = ∫ κ(x - y) f(y) dy`. -/
noncomputable def convFn (κ f : Vec d → ℝ) (x : Vec d) : ℝ := ∫ y, κ (x - y) * f y

/-- The majorant `∫ |κ(x - y)| |f(y)| dy`. -/
noncomputable def convG (κ f : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ∫⁻ y, ‖κ (x - y)‖ₑ * ‖f y‖ₑ

theorem enorm_convFn_le (κ f : Vec d → ℝ) (x : Vec d) : ‖convFn κ f x‖ₑ ≤ convG κ f x := by
  calc ‖convFn κ f x‖ₑ ≤ ∫⁻ y, ‖κ (x - y) * f y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = convG κ f x := by simp [convG, enorm_mul]

theorem aestronglyMeasurable_prod {κ f : Vec d → ℝ} (hκ : AEStronglyMeasurable κ volume)
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z : Vec d × Vec d => κ (z.1 - z.2) * f z.2)
      (volume.prod volume) := by
  have h1 : AEStronglyMeasurable (fun z : Vec d × Vec d => κ (z.1 - z.2)) (volume.prod volume) :=
    (hκ.comp_fst).comp_quasiMeasurePreserving
      (measurePreserving_sub_prod (volume : Measure (Vec d)) (volume : Measure (Vec d))).quasiMeasurePreserving
  exact h1.mul hf.comp_snd

theorem aestronglyMeasurable_convFn {κ f : Vec d → ℝ} (hκ : AEStronglyMeasurable κ volume)
    (hf : AEStronglyMeasurable f volume) : AEStronglyMeasurable (convFn κ f) volume :=
  (aestronglyMeasurable_prod hκ hf).integral_prod_right'

theorem aemeasurable_convG {κ f : Vec d → ℝ} (hκ : AEStronglyMeasurable κ volume)
    (hf : AEStronglyMeasurable f volume) : AEMeasurable (convG κ f) volume := by
  have h := (aestronglyMeasurable_prod hκ hf).enorm
  have h' : AEMeasurable (fun z : Vec d × Vec d => ‖κ (z.1 - z.2)‖ₑ * ‖f z.2‖ₑ)
      (volume.prod volume) := by
    simpa [enorm_mul] using h
  exact h'.lintegral_prod_right'

/-- The `L^q` bound on the majorant (Minkowski's integral inequality). -/
theorem lintegral_convG_rpow_le {κ f : Vec d → ℝ} (hκ : AEStronglyMeasurable κ volume)
    (hf : AEStronglyMeasurable f volume) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x, convG κ f x ^ q ≤ (∫⁻ x, ‖κ x‖ₑ ^ q) * (∫⁻ y, ‖f y‖ₑ) ^ q := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have hκm : AEMeasurable (fun z : Vec d × Vec d => ‖κ (z.1 - z.2)‖ₑ ^ q * ‖f z.2‖ₑ)
      (volume.prod volume) := by
    have h := (aestronglyMeasurable_prod hκ hf).enorm
    have h2 : AEMeasurable (fun z : Vec d × Vec d => ‖κ (z.1 - z.2)‖ₑ) (volume.prod volume) :=
      (hκ.comp_fst.comp_quasiMeasurePreserving
        (measurePreserving_sub_prod (volume : Measure (Vec d))
          (volume : Measure (Vec d))).quasiMeasurePreserving).enorm
    exact (h2.pow_const q).mul hf.enorm.comp_snd
  have step1 : ∀ x, convG κ f x ^ q ≤ (∫⁻ y, ‖f y‖ₑ) ^ (q - 1) *
      ∫⁻ y, ‖κ (x - y)‖ₑ ^ q * ‖f y‖ₑ := fun x => by
    refine lintegral_mul_rpow_le ?_ hf.enorm hq
    exact (hκ.enorm).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure (Vec d)) x)
  calc ∫⁻ x, convG κ f x ^ q
      ≤ ∫⁻ x, (∫⁻ y, ‖f y‖ₑ) ^ (q - 1) * ∫⁻ y, ‖κ (x - y)‖ₑ ^ q * ‖f y‖ₑ :=
        lintegral_mono step1
    _ = (∫⁻ y, ‖f y‖ₑ) ^ (q - 1) * ∫⁻ x, ∫⁻ y, ‖κ (x - y)‖ₑ ^ q * ‖f y‖ₑ := by
        rw [lintegral_const_mul'' _ (by
          simpa using (hκm.lintegral_prod_right'))]
    _ = (∫⁻ y, ‖f y‖ₑ) ^ (q - 1) * ∫⁻ y, ∫⁻ x, ‖κ (x - y)‖ₑ ^ q * ‖f y‖ₑ := by
        rw [lintegral_lintegral_swap hκm]
    _ = (∫⁻ y, ‖f y‖ₑ) ^ (q - 1) * ∫⁻ y, (∫⁻ x, ‖κ x‖ₑ ^ q) * ‖f y‖ₑ := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const'' _ ?_]
        · rw [lintegral_sub_right_eq_self (fun x => ‖κ x‖ₑ ^ q) y]
        · exact ((hκ.enorm.pow_const q).comp_quasiMeasurePreserving
            (measurePreserving_sub_right (volume : Measure (Vec d)) y).quasiMeasurePreserving)
    _ = (∫⁻ x, ‖κ x‖ₑ ^ q) * (∫⁻ y, ‖f y‖ₑ) ^ q := by
        rw [lintegral_const_mul'' _ hf.enorm]
        have : (∫⁻ y, ‖f y‖ₑ) ^ q = (∫⁻ y, ‖f y‖ₑ) ^ (q - 1) * ∫⁻ y, ‖f y‖ₑ := by
          conv_lhs => rw [show q = (q - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ hq0 zero_le_one, ENNReal.rpow_one]
        rw [this]; ring

/-- Minkowski's integral inequality in `eLpNorm` form. -/
theorem eLpNorm_convFn_le {κ f : Vec d → ℝ} (hκ : AEStronglyMeasurable κ volume)
    (hf : AEStronglyMeasurable f volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (convFn κ f) p volume ≤ eLpNorm κ p volume * eLpNorm f 1 volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp; simpa using this
  have hq0 : 0 < p.toReal := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (aestronglyMeasurable_convFn hκ hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hκ, eLpNorm_one_eq_lintegral_enorm hf]
  have h1 : ∫⁻ x, ‖convFn κ f x‖ₑ ^ p.toReal ≤ ∫⁻ x, convG κ f x ^ p.toReal :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_convFn_le κ f x) hq0.le
  have h2 := h1.trans (lintegral_convG_rpow_le hκ hf hq)
  calc (∫⁻ x, ‖convFn κ f x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ ((∫⁻ x, ‖κ x‖ₑ ^ p.toReal) * (∫⁻ y, ‖f y‖ₑ) ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h2 (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        rw [mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

theorem memLp_convFn {κ f : Vec d → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hκ : MemLp κ p volume) (hf : Integrable f) : MemLp (convFn κ f) p volume := by
  refine lt_of_le_of_lt (eLpNorm_convFn_le hκ.aestronglyMeasurable hf.1 hp hpt) ?_
  exact ENNReal.mul_lt_top hκ (by
    rw [eLpNorm_one_eq_lintegral_enorm hf.1]; exact hf.2)

/-- For a.e. `x`, the convolution integrand is integrable. -/
theorem ae_integrable_conv {κ f : Vec d → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hκ : MemLp κ p volume) (hf : Integrable f) :
    ∀ᵐ x, Integrable (fun y => κ (x - y) * f y) := by
  have hq : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp; simpa using this
  have hq0 : 0 < p.toReal := by linarith
  have hfin : ∫⁻ x, convG κ f x ^ p.toReal < ⊤ := by
    refine lt_of_le_of_lt (lintegral_convG_rpow_le hκ.aestronglyMeasurable hf.1 hq) ?_
    refine ENNReal.mul_lt_top ?_ (ENNReal.rpow_lt_top_of_nonneg hq0.le hf.2.ne)
    have := hκ
    rw [MemLp, eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le hp).ne' hpt
      hκ.aestronglyMeasurable] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 this |>.ne.lt_top
  have h1 : ∀ᵐ x, convG κ f x ^ p.toReal < ⊤ :=
    ae_lt_top' ((aemeasurable_convG hκ.aestronglyMeasurable hf.1).pow_const _) hfin.ne
  have h2 := (aestronglyMeasurable_prod hκ.aestronglyMeasurable hf.1).prodMk_left
  filter_upwards [h1, h2] with x hx1 hx2
  refine ⟨hx2, ?_⟩
  have : convG κ f x < ⊤ := by
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos hq0] at hx1
    exact lt_irrefl _ hx1
  simpa [HasFiniteIntegral, convG, enorm_mul] using this

section Operator

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem convFn_congr_right {κ f g : Vec d → ℝ} (h : f =ᵐ[volume] g) (x : Vec d) :
    convFn κ f x = convFn κ g x := by
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  simp [hy]

theorem convFn_add_right {κ f g : Vec d → ℝ} {x : Vec d}
    (hf : Integrable fun y => κ (x - y) * f y) (hg : Integrable fun y => κ (x - y) * g y) :
    convFn κ (f + g) x = convFn κ f x + convFn κ g x := by
  simp only [convFn, Pi.add_apply, mul_add]
  exact integral_add hf hg

theorem convFn_smul_right (κ f : Vec d → ℝ) (c : ℝ) (x : Vec d) :
    convFn κ (c • f) x = c * convFn κ f x := by
  simp only [convFn, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext y; ring

/-- The convolution `L¹ → L^p` with a kernel in `L^p`, as a linear map. -/
noncomputable def convLinear (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume) :
    Lp ℝ 1 (volume : Measure (Vec d)) →ₗ[ℝ] Lp ℝ p (volume : Measure (Vec d)) where
  toFun f := (memLp_convFn Fact.out hpt hκ (L1.integrable_coeFn f)).toLp (convFn κ f)
  map_add' f g := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [ae_integrable_conv Fact.out hpt hκ (L1.integrable_coeFn f),
      ae_integrable_conv Fact.out hpt hκ (L1.integrable_coeFn g)] with x h1 h2
    rw [Pi.add_apply, ← convFn_add_right h1 h2]
    exact convFn_congr_right (Lp.coeFn_add f g) x
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards with x
    rw [Pi.smul_apply, smul_eq_mul, ← convFn_smul_right]
    exact convFn_congr_right (Lp.coeFn_smul c f) x

theorem coeFn_convLinear (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume)
    (f : Lp ℝ 1 (volume : Measure (Vec d))) :
    ⇑(convLinear hpt hκ f) =ᵐ[volume] convFn κ f :=
  MemLp.coeFn_toLp (memLp_convFn Fact.out hpt hκ (L1.integrable_coeFn f))

theorem norm_convLinear_le (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume)
    (f : Lp ℝ 1 (volume : Measure (Vec d))) :
    ‖convLinear hpt hκ f‖ ≤ (eLpNorm κ p volume).toReal * ‖f‖ := by
  have h := eLpNorm_convFn_le hκ.aestronglyMeasurable (L1.integrable_coeFn f).1
    (Fact.out : 1 ≤ p) hpt
  have hA : eLpNorm κ p volume ≠ ⊤ := hκ.ne
  have hB : eLpNorm f 1 volume ≠ ⊤ := Lp.eLpNorm_ne_top f
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_convLinear hpt hκ f)]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hA hB) h
  rwa [ENNReal.toReal_mul] at this

/-- The convolution with a kernel in `L^p`, as a continuous linear map `L¹ → L^p`. -/
noncomputable def convLp (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume) :
    Lp ℝ 1 (volume : Measure (Vec d)) →L[ℝ] Lp ℝ p (volume : Measure (Vec d)) :=
  (convLinear hpt hκ).mkContinuous (eLpNorm κ p volume).toReal (norm_convLinear_le hpt hκ)

theorem coeFn_convLp (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume)
    (f : Lp ℝ 1 (volume : Measure (Vec d))) :
    ⇑(convLp hpt hκ f) =ᵐ[volume] convFn κ f :=
  coeFn_convLinear hpt hκ f

theorem norm_convLp_le (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume) :
    ‖convLp hpt hκ‖ ≤ (eLpNorm κ p volume).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

theorem convLp_sub (hpt : p ≠ ⊤) {κ β : Vec d → ℝ} (hκ : MemLp κ p volume)
    (hβ : MemLp β p volume) :
    convLp hpt (hκ.sub hβ) = convLp hpt hκ - convLp hpt hβ := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_convLp hpt (hκ.sub hβ) f, Lp.coeFn_sub (convLp hpt hκ f) (convLp hpt hβ f),
    coeFn_convLp hpt hκ f, coeFn_convLp hpt hβ f,
    ae_integrable_conv Fact.out hpt hκ (L1.integrable_coeFn f),
    ae_integrable_conv Fact.out hpt hβ (L1.integrable_coeFn f)] with x h1 h2 h3 h4 h5 h6
  rw [sub_apply, h2, Pi.sub_apply, h1, h3, h4]
  simp only [convFn, Pi.sub_apply, sub_mul]
  exact integral_sub h5 h6

end Operator

end AFree.Bessel
