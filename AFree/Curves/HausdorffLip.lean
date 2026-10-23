module

public import AFree.Curves.HausdorffPre

/-!
# `𝓗¹` and Lipschitz maps

Lipschitz images, projections, lower bounds by chord length, and lines.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- Cover form of the Lebesgue measure on `ℝ`: for `r, ε > 0` and `volume A < ⊤` there is a cover
with `ediam ≤ r` and `∑ ediam ≤ volume A + ε`. -/
lemma exists_real_cover {A : Set ℝ} (hA : volume A < ⊤) {r : ℝ≥0∞} (hr : 0 < r) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ t : ℕ → Set ℝ, A ⊆ ⋃ k, t k ∧ (∀ k, Metric.ediam (t k) ≤ r) ∧
      ∑' k, Metric.ediam (t k) ≤ volume A + ε := by
  have h1 : (⨅ (t : ℕ → Set ℝ) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1 : ℝ)) ≤ volume A := by
    rw [← hausdorffMeasure_real, Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le r hr le_rfl
  have h2 := lt_of_le_of_lt h1 (ENNReal.lt_add_right hA.ne hε.ne')
  simp only [iInf_lt_iff] at h2
  obtain ⟨t, hcov, hdiam, hsum⟩ := h2
  refine ⟨t, hcov, hdiam, lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) hsum |>.le⟩
  by_cases hne : (t k).Nonempty
  · simp [hne]
  · rw [not_nonempty_iff_eq_empty.mp hne]; simp

lemma ediam_image_le_euclideanDiam {π : Vec d → ℝ} (hπ : ∀ x y, |π x - π y| ≤ vecEuclideanNorm (x - y))
    (U : Set (Vec d)) : Metric.ediam (π '' U) ≤ euclideanDiam U := by
  refine Metric.ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [edist_dist, Real.dist_eq]
  exact (ENNReal.ofReal_le_ofReal (hπ x y)).trans
    (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl))

lemma euclideanDiam_image_le {B : Set ℝ} {γ : ℝ → Vec d} {L : ℝ≥0}
    (hγ : ∀ x ∈ B, ∀ y ∈ B, vecEuclideanNorm (γ x - γ y) ≤ L * |x - y|) (T : Set ℝ) :
    euclideanDiam (γ '' (T ∩ B)) ≤ L * Metric.ediam T := by
  rw [euclideanDiam_le_iff]
  rintro _ ⟨x, ⟨hxT, hxB⟩, rfl⟩ _ ⟨y, ⟨hyT, hyB⟩, rfl⟩
  calc ENNReal.ofReal (vecEuclideanNorm (γ x - γ y)) ≤ ENNReal.ofReal (L * |x - y|) :=
        ENNReal.ofReal_le_ofReal (hγ x hxB y hyB)
    _ = L * edist x y := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal, edist_dist, Real.dist_eq]
    _ ≤ L * Metric.ediam T := mul_le_mul_right (Metric.edist_le_ediam_of_mem hxT hyT) _

lemma euclideanHausdorffOne_singleton (x : Vec d) : euclideanHausdorffOne d {x} = 0 := by
  rw [(euclideanHausdorffOne_eq_iSup_pre {x}).1]
  refine le_antisymm (iSup_le fun n => ?_) bot_le
  have := (euclideanHausdorffOne_eq_iSup_pre ({x} : Set (Vec d))).2.1 ((n : ℝ≥0∞)⁻¹)
    (fun k => if k = 0 then {x} else ∅) (by
      intro y hy; exact mem_iUnion.mpr ⟨0, by simpa using hy⟩) (by
      intro k; split_ifs <;> simp)
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.tsum_eq_zero]
  intro k
  have h0 : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.mpr rfl
  split_ifs <;> simp [euclideanDiam, h0]

/-- Local form of the Lipschitz-image bound: only the values of `γ` on `B ⊇ A` are used, and `0 < L`. -/
lemma hausdorffOne_image_le_pos {B A : Set ℝ} (hAB : A ⊆ B) {γ : ℝ → Vec d} {L : ℝ≥0} (hL : 0 < L)
    (hγ : ∀ x ∈ B, ∀ y ∈ B, vecEuclideanNorm (γ x - γ y) ≤ L * |x - y|) :
    euclideanHausdorffOne d (γ '' A) ≤ L * volume A := by
  by_cases hA : volume A = ⊤
  · rw [hA, ENNReal.mul_top (by exact_mod_cast hL.ne')]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [(euclideanHausdorffOne_eq_iSup_pre (γ '' A)).1]
  refine iSup_le fun n => ?_
  set ρ : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹ with hρ
  have hLne : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL.ne'
  have hρ0 : ρ ≠ 0 := by simp [hρ]
  obtain ⟨t, hcov, hdiam, hsum⟩ := exists_real_cover (lt_top_iff_ne_top.mpr hA)
    (r := ρ / L) (ENNReal.div_pos hρ0 ENNReal.coe_ne_top) (ε := ((ε / L : ℝ≥0) : ℝ≥0∞))
    (by exact_mod_cast div_pos hε hL)
  have hcov' : γ '' A ⊆ ⋃ k, γ '' (t k ∩ B) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨k, x, ⟨hk, hAB hx⟩, rfl⟩
  have hdiam' : ∀ k, Metric.ediam (γ '' (t k ∩ B)) ≤ ρ := fun k =>
    (ediam_le_euclideanDiam_le _).1.trans <|
      (euclideanDiam_image_le hγ (t k)).trans <|
        (mul_le_mul_right (hdiam k) _).trans (ENNReal.mul_div_le)
  refine ((euclideanHausdorffOne_eq_iSup_pre (γ '' A)).2.1 ρ _ hcov' hdiam').trans ?_
  calc ∑' k, euclideanDiam (γ '' (t k ∩ B)) ≤ ∑' k, (L : ℝ≥0∞) * Metric.ediam (t k) :=
        ENNReal.tsum_le_tsum fun k => euclideanDiam_image_le hγ (t k)
    _ = L * ∑' k, Metric.ediam (t k) := ENNReal.tsum_mul_left
    _ ≤ L * (volume A + ((ε / L : ℝ≥0) : ℝ≥0∞)) := mul_le_mul_right hsum _
    _ = L * volume A + ε := by
        rw [mul_add, ← ENNReal.coe_mul, mul_div_cancel₀ _ hL.ne']

/-- If `|γ x - γ y| ≤ L |x - y|` (Euclidean norm), then
`𝓗¹(γ(A)) ≤ L · 𝓛¹(A)` for every `A ⊆ ℝ`. This includes the case `L = 0`. -/
theorem hausdorffOne_image_le {γ : ℝ → Vec d} {L : ℝ≥0}
    (hγ : ∀ x y, vecEuclideanNorm (γ x - γ y) ≤ L * |x - y|) (A : Set ℝ) :
    euclideanHausdorffOne d (γ '' A) ≤ L * volume A := by
  rcases eq_or_ne L 0 with rfl | hL
  · have hconst : ∀ x, γ x = γ 0 := fun x => by
      have := hγ x 0
      simpa using vecEuclideanNorm_eq_zero_iff.mp (le_antisymm (by simpa using this)
        (vecEuclideanNorm_nonneg _)) |> sub_eq_zero.mp
    have : γ '' A ⊆ {γ 0} := by rintro _ ⟨x, _, rfl⟩; exact hconst x
    simp [measure_mono_null this (euclideanHausdorffOne_singleton _)]
  · exact hausdorffOne_image_le_pos (B := univ) (subset_univ _) (pos_iff_ne_zero.mpr hL)
      fun x _ y _ => hγ x y

/-- For `π` `1`-Lipschitz for the Euclidean norm,
`𝓛¹(π(S)) ≤ 𝓗¹(S)` for every `S ⊆ ℝ^d`. -/
theorem volume_image_le_hausdorffOne {π : Vec d → ℝ}
    (hπ : ∀ x y, |π x - π y| ≤ vecEuclideanNorm (x - y)) (S : Set (Vec d)) :
    volume (π '' S) ≤ euclideanHausdorffOne d S := by
  by_cases hS : euclideanHausdorffOne d S = ⊤
  · rw [hS]; exact le_top
  rw [← hausdorffMeasure_real, Measure.hausdorffMeasure_apply]
  refine iSup₂_le fun r' hr' => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hsq : ENNReal.ofReal (Real.sqrt d) ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨U, hcov, hdiam, hsum⟩ := (euclideanHausdorffOne_eq_iSup_pre S).2.2 (lt_top_iff_ne_top.mpr hS)
    (r' / ENNReal.ofReal (Real.sqrt d)) (ENNReal.div_pos hr'.ne' hsq) ε (by exact_mod_cast hε)
  refine iInf_le_of_le (fun k => π '' U k) (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_))
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨k, x, hk, rfl⟩
  · intro k
    exact (ediam_image_le_euclideanDiam hπ _).trans <| (ediam_le_euclideanDiam_le _).2.trans <|
      (mul_le_mul_right (hdiam k) _).trans ENNReal.mul_div_le
  · refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) hsum
    refine iSup_le fun _ => ?_
    rw [ENNReal.rpow_one]
    exact ediam_image_le_euclideanDiam hπ _

/-- For `γ` continuous on `[a, b]`, `a ≤ b`,
`𝓗¹(γ([a, b])) ≥ |γ(b) - γ(a)|`. -/
theorem ofReal_norm_sub_le_hausdorffOne {γ : ℝ → Vec d} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) :
    ENNReal.ofReal (vecEuclideanNorm (γ b - γ a)) ≤ euclideanHausdorffOne d (γ '' Icc a b) := by
  let f : Vec d → ℝ := fun x => vecEuclideanNorm (x - γ a)
  have hf : ∀ x y, |f x - f y| ≤ vecEuclideanNorm (x - y) := by
    intro x y
    rw [abs_le]
    have h1 : vecEuclideanNorm (x - γ a) ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm (y - γ a) := by
      have e : x - γ a = (x - y) + (y - γ a) := by abel
      rw [e]; exact vecEuclideanNorm_add_le _ _
    have h2 : vecEuclideanNorm (y - γ a) ≤ vecEuclideanNorm (y - x) + vecEuclideanNorm (x - γ a) := by
      have e : y - γ a = (y - x) + (x - γ a) := by abel
      rw [e]; exact vecEuclideanNorm_add_le _ _
    rw [vecEuclideanNorm_sub_comm y x] at h2
    constructor <;> simp only [f] <;> linarith
  have hcont : ContinuousOn (fun s => f (γ s)) (Icc a b) :=
    (continuous_vecEuclideanNorm.comp_continuousOn
      (hγ.sub continuousOn_const))
  have hivt := intermediate_value_Icc hab hcont
  have hfa : f (γ a) = 0 := by simp [f, vecEuclideanNorm_eq_zero_iff]
  have hsub : Icc 0 (vecEuclideanNorm (γ b - γ a)) ⊆ f '' (γ '' Icc a b) := by
    intro y hy
    have := hivt (by simpa [hfa] using hy)
    obtain ⟨s, hs, hsy⟩ := this
    exact ⟨γ s, ⟨s, hs, rfl⟩, hsy⟩
  calc ENNReal.ofReal (vecEuclideanNorm (γ b - γ a))
      = volume (Icc 0 (vecEuclideanNorm (γ b - γ a))) := by simp
    _ ≤ volume (f '' (γ '' Icc a b)) := measure_mono hsub
    _ ≤ _ := volume_image_le_hausdorffOne hf _

/-- For `|u| = 1`, `𝓗¹({x₀ + s u : s ∈ A}) = 𝓛¹(A)`. -/
theorem hausdorffOne_line (x₀ u : Vec d) (hu : vecEuclideanNorm u = 1) (A : Set ℝ) :
    euclideanHausdorffOne d ((fun s : ℝ => x₀ + s • u) '' A) = volume A := by
  apply le_antisymm
  · have := hausdorffOne_image_le (γ := fun s : ℝ => x₀ + s • u) (L := 1) (fun x y => by
      have : x₀ + x • u - (x₀ + y • u) = (x - y) • u := by
        rw [sub_smul]; abel
      rw [this, vecEuclideanNorm_smul, hu]; simp) A
    simpa using this
  · have hπ : ∀ x y : Vec d, |vecDot (x - x₀) u - vecDot (y - x₀) u| ≤ vecEuclideanNorm (x - y) := by
      intro x y
      have : vecDot (x - x₀) u - vecDot (y - x₀) u = vecDot (x - y) u := by
        rw [← vecDot_sub_left]; congr 1; abel
      rw [this]
      simpa [hu] using abs_vecDot_le_vecEuclideanNorm_mul (x - y) u
    have himg : (fun x : Vec d => vecDot (x - x₀) u) '' ((fun s : ℝ => x₀ + s • u) '' A) = A := by
      ext s
      simp only [mem_image]
      constructor
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        have : vecDot (x₀ + t • u - x₀) u = t := by
          have hu2 : vecNormSq u = 1 := by
            have := vecEuclideanNorm_sq u; rw [hu] at this; linarith
          rw [add_sub_cancel_left, vecDot_smul_left, vecDot_self, hu2, mul_one]
        rwa [this]
      · intro hs
        refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
        have hu2 : vecNormSq u = 1 := by
          have := vecEuclideanNorm_sq u; rw [hu] at this; linarith
        rw [add_sub_cancel_left, vecDot_smul_left, vecDot_self, hu2, mul_one]
    have := volume_image_le_hausdorffOne hπ ((fun s : ℝ => x₀ + s • u) '' A)
    rwa [himg] at this

end AFree
