module

public import AFree.Rademacher.Chain.NondiffIter
public import AFree.Rademacher.Chain.NondiffChoice

/-!
# Non-differentiability off the decomposability bundle

A Lipschitz function that is not differentiable on a set of positive measure where `V ≠ ℝ^d`, following [AM, Section 4].
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- Steps 3 to 5 of the proof of non-differentiability, following [AM, Section 4]: from the iteration to a Lipschitz function that is not
differentiable on `limsup K_l`. -/
theorem nondiff_limit {μ : Measure (Vec d)} [IsFiniteMeasure μ] {V : Vec d → Submodule ℝ (Vec d)}
    {i : Fin d} {m : ℕ} {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (hS : Setting μ V i m δ E e) (hμE : 0 < μ E) :
    ∃ (K : ℝ≥0) (f : Vec d → ℝ), LipschitzWith K f ∧ ∃ Z : Set (Vec d), MeasurableSet Z ∧
      0 < μ Z ∧ ∀ x ∈ Z, ¬ DifferentiableAt ℝ f x := by
  obtain ⟨F, K, η, c, hF, hc, hcanti, hstep, hK, hη⟩ := nondiff_iteration hS
  have hD := hS.settingD_pos
  have hv := vecEuclideanNorm_basisVec i
  -- Step 3: the limit
  have hstep' : ∀ n y, dist (F n y) (F (n + 1) y) ≤ 4 / 2 / 2 ^ n := by
    intro n y
    rw [dist_comm, Real.dist_eq]
    refine (hstep n y).trans ?_
    have : c n ≤ 1 := (hc n).2
    have h2 : (0 : ℝ) < (1 / 2) ^ n := by positivity
    calc 2 * (1 / 2) ^ n * c n ≤ 2 * (1 / 2) ^ n * 1 := by gcongr
      _ = 4 / 2 / 2 ^ n := by rw [one_div, inv_pow]; ring
  have hcauchy : ∀ y, CauchySeq fun n => F n y := fun y =>
    cauchySeq_of_le_geometric_two (C := 4) fun n => hstep' n y
  choose f hf using fun y => cauchySeq_tendsto_of_complete (hcauchy y)
  have hlip : LipschitzWith (d : ℝ≥0) f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hlim : Tendsto (fun j => dist (F j x) (F j y)) atTop (𝓝 (dist (f x) (f y))) :=
      (hf x).dist (hf y)
    refine le_of_tendsto' hlim fun j => ?_
    simpa using ((X0_lipschitz hS.frame).2.2.1 _ (hF j)).dist_le_mul x y
  -- the tail estimate
  have htail : ∀ l k, l + 1 ≤ k → ∀ y,
      |F k y - F (l + 1) y| ≤ η l * (1 / 2 - 2 ^ l * (1 / 2) ^ k) := by
    intro l k hk y
    induction k, hk using Nat.le_induction with
    | base =>
      have h : (2 : ℝ) ^ l * (1 / 2) ^ (l + 1) = 1 / 2 := by
        rw [one_div, inv_pow, pow_succ]; field_simp
      rw [h]; simp
    | succ k hk ih =>
      have h1 : c k ≤ 2 ^ l / 4 * η l := by
        have := hcanti hk
        exact this.trans (hη l).2.1
      have h2 := hstep k y
      have hηl := (hη l).1
      have h3 : 2 * (1 / 2 : ℝ) ^ k * c k ≤ 2 * (1 / 2) ^ k * (2 ^ l / 4 * η l) := by gcongr
      have h4 : |F (k + 1) y - F (l + 1) y| ≤ |F (k + 1) y - F k y| + |F k y - F (l + 1) y| := by
        have := abs_add_le (F (k + 1) y - F k y) (F k y - F (l + 1) y)
        rwa [sub_add_sub_cancel] at this
      have h5 : 2 * (1 / 2 : ℝ) ^ k * (2 ^ l / 4 * η l) =
          η l * (2 ^ l * (1 / 2) ^ k / 2) := by ring
      calc |F (k + 1) y - F (l + 1) y|
          ≤ η l * (2 ^ l * (1 / 2) ^ k / 2) + η l * (1 / 2 - 2 ^ l * (1 / 2) ^ k) := by
            linarith
        _ = η l * (1 / 2 - 2 ^ l * (1 / 2) ^ (k + 1)) := by rw [pow_succ]; ring
  have hfclose : ∀ l y, |f y - F (l + 1) y| ≤ η l := by
    intro l y
    have hle : ∀ᶠ k in atTop, |F k y - F (l + 1) y| ≤ η l := by
      filter_upwards [eventually_ge_atTop (l + 1)] with k hk
      refine (htail l k hk y).trans ?_
      have hηl := (hη l).1
      have : 0 ≤ 2 ^ l * (1 / 2 : ℝ) ^ k := by positivity
      nlinarith
    have hlim : Tendsto (fun k => |F k y - F (l + 1) y|) atTop (𝓝 |f y - F (l + 1) y|) :=
      ((hf y).sub_const _).abs
    exact le_of_tendsto hlim hle
  -- the estimate for `f_j - f`
  have hflip : IsLipFun f := by
    refine ⟨(d : ℝ≥0), fun x y => ?_⟩
    have := hlip.dist_le_mul x y
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_le_vecEuclideanNorm _) (by positivity))
  have h53 : ∀ l, ∀ x ∈ K l, settingD δ m / 2 ≤ dirOsc f (basisVec i) (1 / ((l : ℝ) + 1)) 0 x :=
    fun l x hx => (hη l).2.2 f hflip (hfclose l) x hx
  -- Step 4: the set `Z`
  set Z : Set (Vec d) := ⋂ N : ℕ, ⋃ l ≥ N, K l with hZ
  have hKm : ∀ l, MeasurableSet (K l) := fun l => (hK l).2.1.isClosed.measurableSet
  have hAm : ∀ N, MeasurableSet (⋃ l ≥ N, K l) := fun N =>
    MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ => hKm l
  have hZm : MeasurableSet Z := MeasurableSet.iInter hAm
  have hAanti : Antitone fun N : ℕ => ⋃ l ≥ N, K l := by
    intro N N' h
    exact iUnion₂_mono' fun l hl => ⟨l, h.trans hl, subset_rfl⟩
  have hZpos : 0 < μ Z := by
    have hlim : Tendsto (fun N : ℕ => μ (⋃ l ≥ N, K l)) atTop (𝓝 (μ Z)) :=
      tendsto_measure_iInter_atTop (fun N => (hAm N).nullMeasurableSet) hAanti
        ⟨0, measure_ne_top μ _⟩
    have hge : μ E / (4 * (m : ℝ≥0∞)) ≤ μ Z := by
      refine ge_of_tendsto hlim (Eventually.of_forall fun N => ?_)
      exact (hK N).2.2.trans (measure_mono (subset_iUnion₂_of_subset N le_rfl subset_rfl))
    refine lt_of_lt_of_le ?_ hge
    refine ENNReal.div_pos hμE.ne' ?_
    have hm4 : (4 * (m : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
    exact hm4
  refine ⟨d, f, hlip, Z, hZm, hZpos, fun x hx hdiff => ?_⟩
  -- Step 5
  have hlimU := (lem_U hv).2.2.2.1 f hflip x hdiff
  have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), dirOsc f (basisVec i) σ 0 x < settingD δ m / 2 :=
    hlimU.eventually (gt_mem_nhds (by linarith))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hu
  have hxN := mem_iInter.1 hx N
  obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hxN
  have hσl : 1 / ((l : ℝ) + 1) ∈ Ioo (0 : ℝ) u := by
    refine ⟨by positivity, lt_of_le_of_lt ?_ hN⟩
    have : (N : ℝ) ≤ l := by exact_mod_cast hl
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h1 := hsub hσl
  have h2 := h53 l x hxl
  simp only [mem_ofPred_eq] at h1
  linarith

/-- Let `μ` be a finite measure and `V` with `IsDecompTestField μ V` (this is all
that is used of `IsDecompBundle μ V`). If `μ {x | V x ≠ ⊤} > 0`, there are `K` and `f` with
`LipschitzWith K f` and a Borel `Z` with `μ Z > 0` such that `f` is not differentiable at any point
of `Z`. -/
theorem thm_nondiff {μ : Measure (Vec d)} [IsFiniteMeasure μ] {V : Vec d → Submodule ℝ (Vec d)}
    (hV : IsDecompTestField μ V) (hpos : 0 < μ {x | V x ≠ ⊤}) :
    ∃ (K : ℝ≥0) (f : Vec d → ℝ), LipschitzWith K f ∧ ∃ Z : Set (Vec d), MeasurableSet Z ∧
      0 < μ Z ∧ ∀ x ∈ Z, ¬ DifferentiableAt ℝ f x := by
  obtain ⟨P, hP⟩ := isBorelSubspaceField_iff.1 hV.1
  obtain ⟨i, m, δ, G, hm1, hmd, hδ, hGm, hGpos, hrank, hproj⟩ := nondiff_choice hP hpos
  obtain ⟨E, hEG, hEc, hEpos, e, he, hE⟩ := lem_frame μ hP i hδ hGm hGpos hrank hproj
  have hS : Setting μ V i m δ E e :=
    ⟨inferInstance, hV, hm1, hmd, hδ, hEc, he, fun x hx k hk w hw => (hE x hx).1 k hk w hw,
      fun x hx => (hE x hx).2.2.2⟩
  exact nondiff_limit hS hEpos

end AFree.Rademacher
