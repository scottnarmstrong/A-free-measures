module

public import AFree.Curves.Rainwater
public import AFree.Curves.Dichotomy.LusinMain

/-!
# Countably many `C¹` arcs

A normalized `C`-curve `γ ∈ 𝒢(C)` is covered,
up to an `𝓗¹`-null set, by the images of countably many pieces `(g_j, J, S_j ∩ J)`, where `g_j` is
the `C¹` map of the Lusin-type approximation and `J` a rational interval on which `g_j' ⬝ e > cos α / 2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- The continuous linear functional `v ↦ v ⬝ e`. -/
private noncomputable def dotCLM (e : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, e i • ContinuousLinearMap.proj i

private lemma dotCLM_apply (e x : Vec d) : dotCLM e x = vecDot x e := by
  simp [dotCLM, vecDot, mul_comm]

/-- A `C¹` map whose derivative has `e`-component `> 0` on an open interval is an arc there. -/
private lemma isC1Arc_of_dot {g : ℝ → Vec d} (hg : ContDiff ℝ 1 g) {J : Set ℝ} (e : Vec d)
    {c : ℝ} (hc : 0 < c) (hJ : ∃ p r : ℝ, J = Ioo p r)
    (h : ∀ s ∈ J, c < vecDot (deriv g s) e) : IsC1Arc g J := by
  obtain ⟨p, r, rfl⟩ := hJ
  have hderiv : ∀ s, HasDerivAt (fun s => vecDot (g s) e) (vecDot (deriv g s) e) s := fun s => by
    have hd : HasDerivAt g (deriv g s) s := (hg.differentiable one_ne_zero s).hasDerivAt
    have := (dotCLM e).hasFDerivAt.comp_hasDerivAt s hd
    simpa only [Function.comp_def, dotCLM_apply] using this
  have hmono : StrictMonoOn (fun s => vecDot (g s) e) (Ioo p r) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo p r)
      (fun s _ => (hderiv s).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Ioo] at hx
    rw [(hderiv x).deriv]
    linarith [h x hx]
  refine ⟨⟨p, r, rfl⟩, hg.contDiffOn, fun s hs s' hs' hss' => hmono.injOn hs hs' ?_, fun s hs h0 => ?_⟩
  · simp only [hss']
  · have := h s hs
    rw [h0, vecDot_zero_left] at this
    linarith

/-- `ccurveExt γ` is `1`-Lipschitz for the Euclidean norm. -/
private lemma ccurveExt_eucl_lip {e : Vec d} {α : ℝ} {γ : C(I, Vec d)} (hγ : γ ∈ ccurveSpace e α)
    (x y : ℝ) :
    vecEuclideanNorm (ccurveExt γ x - ccurveExt γ y) ≤ ((1 : ℝ≥0) : ℝ) * |x - y| := by
  have h1 := ccurveSpace_dist_le hγ (Set.projIcc 0 1 zero_le_one y) (Set.projIcc 0 1 zero_le_one x)
  have h2 : |((Set.projIcc 0 1 zero_le_one x : I) : ℝ) - (Set.projIcc 0 1 zero_le_one y : I)| ≤
      |x - y| := Set.abs_projIcc_sub_projIcc zero_le_one
  simp only [ccurveExt, Set.IccExtend, Function.comp_apply, NNReal.coe_one, one_mul]
  exact h1.trans h2

/-- Let `γ ∈ 𝒢(C)`, `C = C(e, α)`. There are countably many triples
`(γ_n, J_n, S_n)` with `IsC1Arc γ_n J_n`, `S_n ⊆ J_n ∩ [0,1]`, `γ_n(s) = γ(s)` (the extension of
`γ` by constants) and `γ_n'(s) ∈ C` for `s ∈ S_n`, such that `𝓗¹(γ([0,1]) ∖ ⋃ γ_n(S_n)) = 0`. -/
theorem ccurve_arcs {e : Vec d} {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) {γ : C(I, Vec d)}
    (hγ : γ ∈ ccurveSpace e α) :
    ∃ (g : ℕ → ℝ → Vec d) (J S : ℕ → Set ℝ), (∀ n, IsC1Arc (g n) (J n)) ∧
      (∀ n, S n ⊆ J n ∩ Icc 0 1) ∧
      (∀ n, ∀ s ∈ S n, g n s = ccurveExt γ s ∧ deriv (g n) s ∈ cone e α) ∧
      euclideanHausdorffOne d (range γ \ ⋃ n, g n '' S n) = 0 := by
  classical
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  obtain ⟨-, -, hae, -, -⟩ := ccurveSpace_curve_properties hα hα2 hγ
  have hext := lipschitzWith_ccurveExt hγ
  have hlus : ∀ j : ℕ, ∃ S : Set ℝ, IsCompact S ∧ S ⊆ Icc 0 1 ∧
      volume (Icc (0 : ℝ) 1 \ S) < ENNReal.ofReal (1 / ((j : ℝ) + 1)) ∧
      (∀ s ∈ S, DifferentiableAt ℝ (ccurveExt γ) s) ∧
      ∃ g : ℝ → Vec d, ContDiff ℝ 1 g ∧
        ∀ s ∈ S, g s = ccurveExt γ s ∧ deriv g s = deriv (ccurveExt γ) s :=
    fun j => lusin_c1_approx hext zero_lt_one (by positivity)
  choose S _ hSsub hSmeas _ g hg hgS using hlus
  -- the exceptional sets
  set Z1 : Set ℝ := {s | ¬ (s ∈ Icc (0 : ℝ) 1 → Real.cos α ≤ vecDot (deriv (ccurveExt γ) s) e ∧
    deriv (ccurveExt γ) s ∈ cone e α)} with hZ1
  have hZ1null : volume Z1 = 0 := by
    have := (ae_restrict_iff' measurableSet_Icc).1 hae
    rw [ae_iff] at this
    refine measure_mono_null (fun s hs => ?_) this
    intro hs' 
    exact hs fun hI => (hs' hI).elim fun h1 h2 => ⟨h2.2.1, h2.2.2⟩
  set O : ℕ → Set ℝ := fun j => {s | Real.cos α / 2 < vecDot (deriv (g j) s) e} with hO
  have hOopen : ∀ j, IsOpen (O j) := fun j =>
    isOpen_lt continuous_const ((continuous_vecDot_left e).comp ((hg j).continuous_deriv le_rfl))
  set G : ℕ → Set ℝ := fun j => {s | s ∈ S j ∧ Real.cos α ≤ vecDot (deriv (ccurveExt γ) s) e ∧
    deriv (ccurveExt γ) s ∈ cone e α} with hG
  have hGO : ∀ j, G j ⊆ O j := fun j s hs => by
    change Real.cos α / 2 < vecDot (deriv (g j) s) e
    rw [(hgS j s hs.1).2]
    linarith [hs.2.1]
  obtain ⟨eqv⟩ : Nonempty (ℕ × ℚ × ℚ ≃ ℕ) := nonempty_equiv_of_countable
  let enc : ℕ → ℕ × ℚ × ℚ := eqv.symm
  let J : ℕ → Set ℝ := fun n =>
    if Ioo (((enc n).2.1 : ℚ) : ℝ) (((enc n).2.2 : ℚ) : ℝ) ⊆ O (enc n).1 then
      Ioo (((enc n).2.1 : ℚ) : ℝ) (((enc n).2.2 : ℚ) : ℝ) else Ioo 0 0
  have hJform : ∀ n, ∃ p r : ℝ, J n = Ioo p r := fun n => by
    by_cases h : Ioo (((enc n).2.1 : ℚ) : ℝ) (((enc n).2.2 : ℚ) : ℝ) ⊆ O (enc n).1
    · exact ⟨(((enc n).2.1 : ℚ) : ℝ), (((enc n).2.2 : ℚ) : ℝ), by simp [J, h]⟩
    · exact ⟨0, 0, by simp [J, h]⟩
  have hJO : ∀ n, J n ⊆ O (enc n).1 := fun n => by
    by_cases h : Ioo (((enc n).2.1 : ℚ) : ℝ) (((enc n).2.2 : ℚ) : ℝ) ⊆ O (enc n).1
    · simp [J, h]
    · simp [J, h]
  refine ⟨fun n => g (enc n).1, J, fun n => G (enc n).1 ∩ J n, fun n => ?_, fun n s hs => ?_,
    fun n s hs => ?_, ?_⟩
  · exact isC1Arc_of_dot (hg _) e (half_pos hc) (hJform n) fun s hs => hJO n hs
  · exact ⟨hs.2, (hSsub _ hs.1.1)⟩
  · exact ⟨(hgS _ s hs.1.1).1, by rw [(hgS _ s hs.1.1).2]; exact hs.1.2.2⟩
  · -- coverage
    have hS0 : volume (Icc (0 : ℝ) 1 \ ⋃ j, S j) = 0 := by
      have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine le_antisymm (ge_of_tendsto' hlim fun j => ?_) bot_le
      exact ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion S j))).trans (hSmeas j).le)
    set Z : Set ℝ := Z1 ∪ (Icc (0 : ℝ) 1 \ ⋃ j, S j) with hZ
    have hZnull : volume Z = 0 := measure_union_null hZ1null hS0
    have hsub : range γ \ ⋃ n, (fun n => g (enc n).1) n '' (G (enc n).1 ∩ J n) ⊆
        ccurveExt γ '' Z := by
      rintro x ⟨⟨s', rfl⟩, hx⟩
      refine ⟨(s' : ℝ), ?_, ccurveExt_coe γ s'⟩
      by_contra hsZ
      apply hx
      have hsI : (s' : ℝ) ∈ Icc (0 : ℝ) 1 := s'.2
      have hP : Real.cos α ≤ vecDot (deriv (ccurveExt γ) s') e ∧
          deriv (ccurveExt γ) s' ∈ cone e α := by
        by_contra hP
        exact hsZ (Or.inl fun h => hP (h hsI))
      have hS : ∃ j, (s' : ℝ) ∈ S j := by
        by_contra hS
        exact hsZ (Or.inr ⟨hsI, by simpa using hS⟩)
      obtain ⟨j, hj⟩ := hS
      have hGj : (s' : ℝ) ∈ G j := ⟨hj, hP⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hOopen j) _ (hGO j hGj)
      obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_btwn (show (s' : ℝ) - δ < s' by linarith)
      obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_btwn (show (s' : ℝ) < s' + δ by linarith)
      have hIO : Ioo (q₁ : ℝ) (q₂ : ℝ) ⊆ O j := fun x hx => hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hx.1, hx.2])
      set n := eqv (j, q₁, q₂) with hn
      have hen : enc n = (j, q₁, q₂) := by simp only [enc, hn, Equiv.symm_apply_apply]
      have hJn : J n = Ioo (q₁ : ℝ) (q₂ : ℝ) := by simp [J, hen, hIO]
      refine mem_iUnion.2 ⟨n, (s' : ℝ), ⟨?_, ?_⟩, ?_⟩
      · rw [hen]; exact hGj
      · rw [hJn]; exact ⟨hq₁', hq₂⟩
      · change g (enc n).1 (s' : ℝ) = γ s'
        rw [hen]
        exact ((hgS j _ hj).1).trans (ccurveExt_coe γ s')
    refine measure_mono_null hsub ?_
    have := hausdorffOne_image_le (fun x y => ccurveExt_eucl_lip hγ x y) Z
    rw [hZnull] at this
    simpa using this
end AFree
