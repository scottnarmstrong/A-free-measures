module

public import AFree.Paper.Bessel.Young
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Compactness of convolution with a `C_c` kernel

For `β ∈ C_c(ℝ^d)` the operator `f ↦ β ⋆ f` from `L¹_c(B₁)` to `L^p` is compact: the images of the
unit ball are uniformly bounded, uniformly equicontinuous and supported in a fixed compact set
`K`, hence totally bounded in `C(K)` by Arzelà–Ascoli, hence in `L^p`.
-/

@[expose] public section

open MeasureTheory ENNReal Topology Filter
open scoped BoundedContinuousFunction

namespace AFree.Bessel

open PDE

variable {d : ℕ}

section Estimates

variable {β f : Vec d → ℝ}

theorem integrable_kernel_mul {M : ℝ} (hβ : Continuous β) (hM : ∀ x, ‖β x‖ ≤ M)
    (hf : Integrable f) (x : Vec d) : Integrable fun y => β (x - y) * f y :=
  hf.bdd_mul (c := M) (hβ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => hM _)

theorem abs_convFn_le {M : ℝ} (hM : ∀ x, ‖β x‖ ≤ M) (hf : Integrable f)
    (x : Vec d) : |convFn β f x| ≤ M * ∫ y, ‖f y‖ := by
  have h := norm_integral_le_of_norm_le (hf.norm.const_mul M)
    (f := fun y => β (x - y) * f y) (Filter.Eventually.of_forall fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  rw [integral_const_mul] at h
  simpa [convFn] using h

theorem abs_convFn_sub_le {M ε : ℝ} (hβ : Continuous β) (hM : ∀ x, ‖β x‖ ≤ M)
    (hf : Integrable f) {x x' : Vec d} (hε : ∀ y, |β (x - y) - β (x' - y)| ≤ ε) :
    |convFn β f x - convFn β f x'| ≤ ε * ∫ y, ‖f y‖ := by
  have h1 := integrable_kernel_mul hβ hM hf x
  have h2 := integrable_kernel_mul hβ hM hf x'
  have h := norm_integral_le_of_norm_le (hf.norm.const_mul ε)
    (f := fun y => β (x - y) * f y - β (x' - y) * f y) (Filter.Eventually.of_forall fun y => by
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hε y) (norm_nonneg _))
  rw [integral_const_mul, integral_sub h1 h2] at h
  simpa [convFn] using h

end Estimates

section Compact

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The convolution operator `L¹_c(B₁) → L^p`, `f ↦ κ ⋆ f`. -/
noncomputable def convBall (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume) :
    L1Ball d →L[ℝ] Lp ℝ p (volume : Measure (Vec d)) :=
  (convLp hpt hκ).comp (L1Ball d).subtypeL

theorem convBall_apply (hpt : p ≠ ⊤) {κ : Vec d → ℝ} (hκ : MemLp κ p volume) (f : L1Ball d) :
    convBall hpt hκ f = convLp hpt hκ (f : Lp ℝ 1 (volume : Measure (Vec d))) := rfl

theorem integral_norm_coeFn_le {f : L1Ball d} (hf : f ∈ Metric.closedBall (0 : L1Ball d) 1) :
    ∫ y, ‖((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) y‖ ≤ 1 := by
  have : ‖f‖ ≤ 1 := by simpa using hf
  have h2 : ‖(f : Lp ℝ 1 (volume : Measure (Vec d)))‖ = ‖f‖ := rfl
  rw [← L1.norm_eq_integral_norm]
  exact h2 ▸ this

/-- Everything convolved with `β` of support in `closedBall 0 R` vanishes outside
`closedBall 0 (R + 1)` when `f` lives in `B₁`. -/
theorem convFn_eq_zero_of_not_mem {β : Vec d → ℝ} {R : ℝ}
    (hR : ∀ x, R < ‖x‖ → β x = 0) (f : L1Ball d) {x : Vec d} (hx : R + 1 < ‖x‖) :
    convFn β ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) x = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [f.2] with y hy
  by_cases hyb : y ∈ euclideanBall (0 : Vec d) 1
  · have h1 : ‖y‖ < 1 := by
      have := euclideanBall_subset_supBall (x₀ := (0 : Vec d)) (R := 1) one_pos hyb
      simpa using this
    have : R < ‖x - y‖ := by
      have := norm_sub_norm_le x y
      linarith
    simp [hR _ this]
  · simp [hy hyb]

theorem dist_convBall_le (hpt : p ≠ ⊤) {β : Vec d → ℝ} (hβ : MemLp β p volume)
    {K : Set (Vec d)} (hK : IsCompact K)
    (hvan : ∀ f : L1Ball d, ∀ x ∉ K,
      convFn β ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) x = 0)
    {c : ℝ} (hc0 : 0 ≤ c) (f f' : L1Ball d)
    (hc : ∀ x ∈ K, |convFn β ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) x -
      convFn β ((f' : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) x| ≤ c) :
    dist (convBall hpt hβ f) (convBall hpt hβ f') ≤ (volume K).toReal ^ p.toReal⁻¹ * c := by
  set g : Vec d → ℝ := fun x =>
    convFn β ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) x -
      convFn β ((f' : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ) x with hg
  have hgm : AEStronglyMeasurable g volume :=
    (aestronglyMeasurable_convFn hβ.aestronglyMeasurable (L1.integrable_coeFn _).1).sub
      (aestronglyMeasurable_convFn hβ.aestronglyMeasurable (L1.integrable_coeFn _).1)
  have hsupp : g.support ⊆ K := fun x hx => by
    by_contra hxK
    exact hx (by simp [hg, hvan f x hxK, hvan f' x hxK])
  have h1 : eLpNorm g p volume ≤ (volume K) ^ p.toReal⁻¹ * ENNReal.ofReal c := by
    rw [← eLpNorm_restrict_eq_of_support_subset hgm hsupp]
    have := eLpNorm_le_of_ae_bound (p := p) (μ := volume.restrict K) (f := g) (C := c)
      hgm.restrict (by
        refine (ae_restrict_iff' hK.measurableSet).2 (Filter.Eventually.of_forall fun x hx => ?_)
        simpa [hg] using hc x hx)
    rwa [Measure.restrict_apply_univ] at this
  rw [dist_eq_norm, Lp.norm_def,
    eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (by
      filter_upwards [coeFn_convLp hpt hβ (f : Lp ℝ 1 (volume : Measure (Vec d))),
        coeFn_convLp hpt hβ (f' : Lp ℝ 1 (volume : Measure (Vec d)))] with x h2 h3
      simp [convBall_apply, h2, h3, hg]) : _ =ᵐ[volume] g)]
  have hfin : (volume K) ^ p.toReal⁻¹ * ENNReal.ofReal c ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne)
      ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfin h1
  rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc0] at this

/-- The `L¹` representative of an element of `L¹_c(B₁)`. -/
noncomputable abbrev fnOf (f : L1Ball d) : Vec d → ℝ := ((f : Lp ℝ 1 (volume : Measure (Vec d))) : Vec d → ℝ)

/-- For `β ∈ C_c(ℝ^d)` and `1 ≤ p < ∞`, the convolution `f ↦ β ⋆ f` is a compact
operator `L¹_c(B₁) → L^p`. -/
theorem isCompactOperator_convBall (hpt : p ≠ ⊤) {β : Vec d → ℝ} (hβc : Continuous β)
    (hβs : HasCompactSupport β) :
    IsCompactOperator (convBall hpt (hβc.memLp_of_hasCompactSupport (p := p) hβs)) := by
  set hβ : MemLp β p volume := hβc.memLp_of_hasCompactSupport (p := p) hβs with hβdef
  obtain ⟨M, hM⟩ := hβc.bounded_above_of_compact_support hβs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R, hR⟩ := hβs.isCompact.isBounded.subset_closedBall (0 : Vec d)
  have hRβ : ∀ x, R < ‖x‖ → β x = 0 := fun x hx => by
    by_contra h
    have h1 := hR (subset_tsupport _ (Function.mem_support.2 h))
    rw [mem_closedBall_zero_iff] at h1
    linarith
  set K : Set (Vec d) := Metric.closedBall 0 (R + 1) with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hvan : ∀ f : L1Ball d, ∀ x ∉ K, convFn β (fnOf f) x = 0 := fun f x hx =>
    convFn_eq_zero_of_not_mem hRβ f (by simpa [hKdef] using hx)
  have hβu : UniformContinuous β := hβs.uniformContinuous_of_continuous hβc
  have hmod : ∀ ε > 0, ∃ δ > 0, ∀ x x' : Vec d, dist x x' < δ →
      ∀ f ∈ Metric.closedBall (0 : L1Ball d) 1, |convFn β (fnOf f) x - convFn β (fnOf f) x'| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 hβu ε hε
    refine ⟨δ, hδ, fun x x' hxx f hf => ?_⟩
    have := abs_convFn_sub_le (M := M) (ε := ε) hβc hM (L1.integrable_coeFn
      (f : Lp ℝ 1 (volume : Measure (Vec d)))) (x := x) (x' := x') (fun y => by
        have := hδ' (a := x - y) (b := x' - y) (by simpa [dist_eq_norm] using hxx)
        rw [Real.dist_eq] at this; exact this.le)
    exact this.trans (mul_le_of_le_one_right hε.le (integral_norm_coeFn_le hf))
  have hcont : ∀ f ∈ Metric.closedBall (0 : L1Ball d) 1, Continuous (convFn β (fnOf f)) := by
    intro f hf
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ, h⟩ := hmod (ε / 2) (half_pos hε)
    exact ⟨δ, hδ, fun a ha => by
      rw [Real.dist_eq]; linarith [h a b ha f hf]⟩
  let Φ : (Metric.closedBall (0 : L1Ball d) 1) → (K →ᵇ ℝ) := fun f =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => convFn β (fnOf f.1) x, (hcont f.1 f.2).comp continuous_subtype_val⟩
  have hΦ : ∀ f x, Φ f x = convFn β (fnOf f.1) x := fun f x => rfl
  have hequi : Equicontinuous ((↑) : Set.range Φ → K → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hmod (ε / 2) (half_pos hε)
    refine ⟨Metric.ball x₀ (δ / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
    rintro x hx x' hx' ⟨_, j, rfl⟩
    have hxx : dist (x : Vec d) x' < δ := by
      have := dist_triangle_right (x : Vec d) x' x₀
      rw [Metric.mem_ball] at hx hx'
      have h1 : dist (x : Vec d) x₀ < δ / 2 := hx
      have h2 : dist (x' : Vec d) x₀ < δ / 2 := hx'
      linarith
    rw [Real.dist_eq]
    have := hδ' x x' hxx j.1 j.2
    show |convFn β (fnOf j.1) x - convFn β (fnOf j.1) x'| < ε
    linarith
  have hbd : ∀ (g : K →ᵇ ℝ) (x : K), g ∈ Set.range Φ → g x ∈ Metric.closedBall (0 : ℝ) M := by
    rintro g x ⟨j, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, hΦ]
    exact (abs_convFn_le hM (L1.integrable_coeFn _) _).trans
      (mul_le_of_le_one_right hM0 (integral_norm_coeFn_le j.2))
  have hcpt := BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall _ _) (Set.range Φ)
    hbd hequi
  have hTB : TotallyBounded (Set.range Φ) := hcpt.totallyBounded.subset subset_closure
  set V : ℝ := (volume K).toReal ^ p.toReal⁻¹ with hV
  have hV0 : 0 ≤ V := by positivity
  have htb : TotallyBounded ((convBall hpt hβ) '' Metric.closedBall (0 : L1Ball d) 1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    have hc : 0 < ε / (2 * (V + 1)) := by positivity
    obtain ⟨t, hts, htf, hcov⟩ := hTB.exists_subset
      (U := {q | dist q.1 q.2 < ε / (2 * (V + 1))}) (Metric.dist_mem_uniformity hc)
    obtain ⟨J, -, hJf, hJ⟩ := (Set.exists_subset_image_finite_and (f := Φ) (s := Set.univ)
      (p := fun t => Set.range Φ ⊆ ⋃ y ∈ t,
        {x | (x, y) ∈ {q : (K →ᵇ ℝ) × (K →ᵇ ℝ) | dist q.1 q.2 < ε / (2 * (V + 1))}})).1
      ⟨t, by rwa [Set.image_univ], htf, hcov⟩
    refine ⟨(fun f : Metric.closedBall (0 : L1Ball d) 1 => convBall hpt hβ f.1) '' J,
      hJf.image _, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    have h1 := hJ ⟨⟨f, hf⟩, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h1
    obtain ⟨y, hy, hdist⟩ := h1
    obtain ⟨i, hi, rfl⟩ := hy
    simp only [Set.mem_iUnion, Metric.mem_ball]
    refine ⟨convBall hpt hβ i.1, ⟨i, hi, rfl⟩, ?_⟩
    have := dist_convBall_le hpt hβ hKc hvan (c := ε / (2 * (V + 1))) hc.le f i.1 (fun x hx => by
      have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := Φ ⟨f, hf⟩) (g := Φ i)
        (⟨x, hx⟩ : K)
      rw [Real.dist_eq, hΦ, hΦ] at h2
      exact h2.trans hdist.le)
    refine this.trans_lt ?_
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    (convBall hpt hβ : L1Ball d →ₗ[ℝ] Lp ℝ p (volume : Measure (Vec d))) one_pos).2
    (htb.closure.isCompact_of_isClosed isClosed_closure)

end Compact

end AFree.Bessel
