module

public import AFree.Defs
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Measures determined by smooth test functions

Smooth Urysohn functions with supports in
thin neighbourhoods of a compact set `K ⊂ Ω` give `∫_K f dσ = 0`; Mathlib's compact-set criterion
then gives `f = 0` a.e. on closed balls in `Ω`, which cover `Ω` countably.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set PDE

namespace AFree

noncomputable section

variable {d : ℕ}

section Aux

variable {Ω : Set (Vec d)} {σ : Measure (Vec d)} {f : Vec d → ℝ}

theorem exists_cthickening_subset (hΩ : IsOpen Ω) {K : Set (Vec d)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ cthickening δ K ⊆ Ω := hK.exists_cthickening_subset_open hΩ hKΩ

/-- `∫_K f dσ = 0` for compact `K ⊆ Ω`, together with integrability on `K`. -/
theorem integrableOn_and_setIntegral_eq_zero [IsFiniteMeasure σ] (hΩ : IsOpen Ω)
    (hf : ∀ U : Set (Vec d), IsOpen U → IsCompact (closure U) → closure U ⊆ Ω →
      IntegrableOn f U σ)
    (h : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∫ x, φ x * f x ∂σ = 0)
    {K : Set (Vec d)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IntegrableOn f K σ ∧ ∫ x in K, f x ∂σ = 0 := by
  obtain ⟨δ, hδ, hδΩ⟩ := exists_cthickening_subset hΩ hK hKΩ
  set U : Set (Vec d) := thickening δ K with hU
  have hUo : IsOpen U := isOpen_thickening
  have hUc : closure U ⊆ cthickening δ K := closure_thickening_subset_cthickening δ K
  have hUcomp : IsCompact (closure U) :=
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hUc
  have hfU : IntegrableOn f U σ := hf U hUo hUcomp (hUc.trans hδΩ)
  have hKU : K ⊆ U := self_subset_thickening hδ K
  refine ⟨hfU.mono_set hKU, ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  set g : Vec d → ℝ := U.indicator f with hg
  have hgi : Integrable g σ := hfU.integrable_indicator hUo.measurableSet
  -- smooth bumps
  have hbump : ∀ n : ℕ, ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      Function.support φ = thickening (δ / (n + 2)) K ∧ (∀ x, x ∈ K ↔ φ x = 1) := by
    intro n
    have hpos : 0 < δ / (n + 2) := by positivity
    obtain ⟨φ, h1, h2, h3, h4⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ / (n + 2)) (E := K)) hK.isClosed
      (self_subset_thickening hpos K)
    exact ⟨φ, by simpa using h1, fun x => h2 ⟨x, rfl⟩, h3, h4⟩
  choose φ hφs hφr hφsupp hφK using hbump
  have hφU : ∀ n x, x ∉ U → φ n x = 0 := by
    intro n x hx
    by_contra hne
    have : x ∈ Function.support (φ n) := hne
    rw [hφsupp n] at this
    exact hx (thickening_mono (by
      have : δ / (n + 2) ≤ δ := div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      exact this) K this)
  have hφtest : ∀ n, IsTestFunctionOn Ω (φ n) := by
    intro n
    have hts : tsupport (φ n) ⊆ cthickening δ K := by
      refine closure_minimal ?_ isClosed_cthickening
      rw [hφsupp n]
      exact (thickening_subset_cthickening _ _).trans (cthickening_mono (by
        have : δ / (n + 2) ≤ δ := div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
        exact this) K)
    exact ⟨hφs n, (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hts,
      hts.trans hδΩ⟩
  have hzero : ∀ n, ∫ x, φ n x * g x ∂σ = 0 := by
    intro n
    rw [← h (φ n) (hφtest n)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp [hg, Set.indicator_of_mem hx]
    · simp [hg, Set.indicator_of_notMem hx, hφU n x hx]
  have hlim : Tendsto (fun n => ∫ x, φ n x * g x ∂σ) atTop (𝓝 (∫ x, K.indicator g x ∂σ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun n => ((hφs n).continuous.aestronglyMeasurable).mul hgi.aestronglyMeasurable)
      hgi.norm (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [norm_mul]
      have := hφr n x
      rw [Real.norm_of_nonneg this.1]
      exact mul_le_of_le_one_left (norm_nonneg _) this.2
    · by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        exact tendsto_const_nhds.congr fun n => by rw [(hφK n x).1 hx, one_mul]
      · simp only [Set.indicator_of_notMem hx]
        have hd : 0 < infDist x K := (hK.isClosed.notMem_iff_infDist_pos hKne).1 hx
        obtain ⟨N, hN⟩ := exists_nat_gt (δ / infDist x K)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hnot : x ∉ thickening (δ / (n + 2)) K := by
          rw [mem_thickening_iff_infDist_lt hKne, not_lt]
          rw [div_le_iff₀ (by positivity)]
          have h1 : δ < N * infDist x K := by rwa [div_lt_iff₀ hd] at hN
          have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        have : φ n x = 0 := by
          by_contra hne
          exact hnot (hφsupp n ▸ (show x ∈ Function.support (φ n) from hne))
        simp [this]
  have hlim' : ∫ x, K.indicator g x ∂σ = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (hzero n).symm)
  rw [integral_indicator hK.measurableSet] at hlim'
  rw [← hlim']
  refine setIntegral_congr_fun hK.measurableSet fun x hx => ?_
  simp [hg, Set.indicator_of_mem (hKU hx)]

end Aux

/-- Let `σ` be a finite measure on `ℝ^d`, `Ω` open, `f` real valued and in
`L¹(σ⌞U)` for every open `U` with `closure U` compact in `Ω`, with `∫ φ f dσ = 0` for all test
functions `φ` in `Ω`. Then `f = 0` `σ`-a.e. on `Ω`. -/
theorem lem_measuniq {Ω : Set (Vec d)} (hΩ : IsOpen Ω) (σ : Measure (Vec d)) [IsFiniteMeasure σ]
    {f : Vec d → ℝ}
    (hf : ∀ U : Set (Vec d), IsOpen U → IsCompact (closure U) → closure U ⊆ Ω →
      IntegrableOn f U σ)
    (h : ∀ φ : Vec d → ℝ, IsTestFunctionOn Ω φ → ∫ x, φ x * f x ∂σ = 0) :
    ∀ᵐ x ∂σ, x ∈ Ω → f x = 0 := by
  have hr : ∀ x : Vec d, ∃ r : ℝ, 0 < r ∧ (x ∈ Ω → closedBall x r ⊆ Ω) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
      exact ⟨r / 2, half_pos hr, fun _ => (closedBall_subset_ball (half_lt_self hr)).trans hrΩ⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hr0 hrΩ using hr
  obtain ⟨T, hTΩ, hTc, hT⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := Ω)
    (f := fun x => ball x (r x)) (fun x _ => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x)))
  have hball : ∀ x ∈ T, ∀ᵐ y ∂σ, y ∈ closedBall x (r x) → f y = 0 := by
    intro x hxT
    have hx : x ∈ Ω := hTΩ hxT
    set B := closedBall x (r x) with hB
    have hBc : IsCompact B := isCompact_closedBall x (r x)
    have hBΩ : B ⊆ Ω := hrΩ x hx
    have hint : Integrable f (σ.restrict B) :=
      (integrableOn_and_setIntegral_eq_zero hΩ hf h hBc hBΩ).1
    have h0 := ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero (μ := σ.restrict B) hint
      (fun s hs => by
        rw [Measure.restrict_restrict hs.measurableSet]
        exact (integrableOn_and_setIntegral_eq_zero hΩ hf h (hs.inter_right hBc.isClosed)
          (fun y hy => hBΩ hy.2)).2)
    have h0' : ∀ᵐ y ∂σ.restrict B, f y = 0 := h0
    rw [ae_restrict_iff' hBc.measurableSet] at h0'
    exact h0'
  have hall : ∀ᵐ y ∂σ, ∀ x ∈ T, y ∈ closedBall x (r x) → f y = 0 := by
    rw [ae_ball_iff hTc]
    exact hball
  filter_upwards [hall] with y hy hyΩ
  have := hT hyΩ
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxT, hyb⟩ := this
  exact hy x hxT (ball_subset_closedBall hyb)

end

end AFree
