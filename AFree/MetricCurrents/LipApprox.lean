module

public import AFree.MetricCurrents.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Lipschitz approximation
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE

/-- The Euclidean distance `dist(x, C) = inf_{c ∈ C} |x - c|` (not Mathlib's `Metric.infDist`, which
is the maximum-metric distance on `Vec d`). -/
noncomputable def euclDist {d : ℕ} (C : Set (Vec d)) (x : Vec d) : ℝ :=
  ⨅ c : C, vecEuclideanNorm (x - (c : Vec d))

/-- `g_t^C(x) = max(0, 1 - dist(x, C) / t)`. -/
noncomputable def distCutoff {d : ℕ} (C : Set (Vec d)) (t : ℝ) (x : Vec d) : ℝ :=
  max 0 (1 - euclDist C x / t)

namespace MetricCurrents.LipApprox

lemma euclDist_le {d : ℕ} {C : Set (Vec d)} {x c : Vec d} (hc : c ∈ C) :
    euclDist C x ≤ vecEuclideanNorm (x - c) :=
  ciInf_le (f := fun c : C => vecEuclideanNorm (x - (c : Vec d)))
    ⟨0, by rintro _ ⟨c', rfl⟩; exact vecEuclideanNorm_nonneg _⟩ ⟨c, hc⟩

lemma le_euclDist {d : ℕ} {C : Set (Vec d)} (hne : C.Nonempty) {x : Vec d} {a : ℝ}
    (h : ∀ c ∈ C, a ≤ vecEuclideanNorm (x - c)) : a ≤ euclDist C x := by
  have : Nonempty C := hne.to_subtype
  exact le_ciInf fun c => h c c.2

lemma euclDist_nonneg {d : ℕ} {C : Set (Vec d)} (x : Vec d) : 0 ≤ euclDist C x := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp [euclDist]
  · exact le_euclDist hne fun c _ => vecEuclideanNorm_nonneg _

lemma euclDist_le_add {d : ℕ} {C : Set (Vec d)} (hne : C.Nonempty) (x y : Vec d) :
    euclDist C x ≤ vecEuclideanNorm (x - y) + euclDist C y := by
  have : euclDist C x - vecEuclideanNorm (x - y) ≤ euclDist C y := by
    refine le_euclDist hne fun c hc => ?_
    have h1 : euclDist C x ≤ vecEuclideanNorm (x - c) := euclDist_le hc
    have h2 : vecEuclideanNorm (x - c) ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm (y - c) := by
      have := vecEuclideanNorm_add_le (x - y) (y - c)
      simpa using this
    linarith
  linarith

lemma abs_euclDist_sub_le {d : ℕ} {C : Set (Vec d)} (hne : C.Nonempty) (x y : Vec d) :
    |euclDist C x - euclDist C y| ≤ vecEuclideanNorm (x - y) := by
  have h1 := euclDist_le_add hne x y
  have h2 := euclDist_le_add hne y x
  rw [vecEuclideanNorm_sub_comm y x] at h2
  rw [abs_le]; constructor <;> linarith

lemma euclDist_eq_zero_iff {d : ℕ} {C : Set (Vec d)} (hC : IsClosed C) (hne : C.Nonempty)
    (x : Vec d) : euclDist C x = 0 ↔ x ∈ C := by
  constructor
  · intro h0
    have : Metric.infDist x C ≤ euclDist C x := by
      refine le_euclDist (C := C) (a := Metric.infDist x C) hne fun c hc => ?_
      calc Metric.infDist x C ≤ dist x c := Metric.infDist_le_dist_of_mem hc
        _ = ‖x - c‖ := dist_eq_norm _ _
        _ ≤ _ := norm_le_vecEuclideanNorm _
    exact (hC.mem_iff_infDist_zero hne).2 (le_antisymm (h0 ▸ this) Metric.infDist_nonneg)
  · intro hx
    refine le_antisymm ?_ (euclDist_nonneg x)
    have := euclDist_le (C := C) (x := x) hx
    have h0 : vecEuclideanNorm (x - x) = 0 := vecEuclideanNorm_eq_zero_iff.2 (sub_self x)
    linarith

lemma continuous_of_eucl {d : ℕ} {K : ℝ≥0} {f : Vec d → ℝ} (hf : IsEuclLipschitzWith K f) :
    Continuous f := by
  have : LipschitzWith (K * ⟨Real.sqrt d, Real.sqrt_nonneg _⟩) f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    calc |f x - f y| ≤ K * vecEuclideanNorm (x - y) := hf x y
      _ ≤ K * (Real.sqrt d * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) K.2
      _ = _ := by
        show (K : ℝ) * (Real.sqrt d * ‖x - y‖) = (K : ℝ) * Real.sqrt d * ‖x - y‖
        ring
  exact this.continuous

lemma isBddLipFun_zero {d : ℕ} : IsBddLipFun (0 : Vec d → ℝ) :=
  ⟨⟨0, fun x y => by simp⟩, 0, fun x => by simp⟩

end MetricCurrents.LipApprox

open MetricCurrents.LipApprox in
/-- For `C` closed non-empty and `t > 0`: `x ↦ dist(x, C)` is
Euclidean `1`-Lipschitz and vanishes exactly on `C`; `g_t^C ∈ Lip_b`, `0 ≤ g_t^C ≤ 1`, `g_t^C = 1`
on `C`, `g_t^C = 0` where `dist(x, C) ≥ t`, `g_t^C` is Euclidean `(1/t)`-Lipschitz, and
`g_{1/(n+1)}^C → 1_C` pointwise. -/
theorem distCutoff_spec {d : ℕ} {C : Set (Vec d)} (hC : IsClosed C) (hne : C.Nonempty) {t : ℝ}
    (ht : 0 < t) :
    IsEuclLipschitzWith 1 (euclDist C) ∧ (∀ x, euclDist C x = 0 ↔ x ∈ C) ∧
    IsBddLipFun (distCutoff C t) ∧ (∀ x, 0 ≤ distCutoff C t x ∧ distCutoff C t x ≤ 1) ∧
    (∀ x ∈ C, distCutoff C t x = 1) ∧ (∀ x, t ≤ euclDist C x → distCutoff C t x = 0) ∧
    IsEuclLipschitzWith ⟨1 / t, by positivity⟩ (distCutoff C t) ∧
    (∀ x, Tendsto (fun n : ℕ => distCutoff C (1 / ((n : ℝ) + 1)) x) atTop (𝓝 (C.indicator 1 x))) := by
  have hL : IsEuclLipschitzWith ⟨1 / t, by positivity⟩ (distCutoff C t) := by
    intro x y
    have h1 : |distCutoff C t x - distCutoff C t y| ≤
        |(1 - euclDist C x / t) - (1 - euclDist C y / t)| := by
      unfold distCutoff
      rw [max_comm 0 (1 - euclDist C x / t), max_comm 0 (1 - euclDist C y / t)]
      exact abs_max_sub_max_le_abs _ _ _
    calc |distCutoff C t x - distCutoff C t y|
        ≤ |(1 - euclDist C x / t) - (1 - euclDist C y / t)| := h1
      _ = |euclDist C x - euclDist C y| / t := by
          rw [show (1 - euclDist C x / t) - (1 - euclDist C y / t)
            = -((euclDist C x - euclDist C y) / t) by ring, abs_neg, abs_div, abs_of_pos ht]
      _ ≤ vecEuclideanNorm (x - y) / t := by
          gcongr; exact abs_euclDist_sub_le hne x y
      _ = _ := by
          show vecEuclideanNorm (x - y) / t = 1 / t * vecEuclideanNorm (x - y)
          ring
  have hbd : ∀ x, 0 ≤ distCutoff C t x ∧ distCutoff C t x ≤ 1 := fun x => by
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    have : 0 ≤ euclDist C x / t := div_nonneg (euclDist_nonneg x) ht.le
    linarith
  have hone : ∀ x ∈ C, distCutoff C t x = 1 := fun x hx => by
    simp [distCutoff, (euclDist_eq_zero_iff hC hne x).2 hx]
  refine ⟨?_, euclDist_eq_zero_iff hC hne, ⟨⟨_, hL⟩, 1, fun x => ?_⟩, hbd, hone, ?_, hL, ?_⟩
  · intro x y
    simpa using abs_euclDist_sub_le hne x y
  · rw [abs_of_nonneg (hbd x).1]; exact (hbd x).2
  · intro x hx
    unfold distCutoff
    refine max_eq_left ?_
    have : 1 ≤ euclDist C x / t := (one_le_div ht).2 hx
    linarith
  · intro x
    by_cases hx : x ∈ C
    · have : (fun n : ℕ => distCutoff C (1 / ((n : ℝ) + 1)) x) = fun _ => 1 :=
        funext fun n => by
          simp [distCutoff, (euclDist_eq_zero_iff hC hne x).2 hx]
      rw [this, Set.indicator_of_mem hx]
      exact tendsto_const_nhds
    · have hpos : 0 < euclDist C x :=
        lt_of_le_of_ne (euclDist_nonneg x) (fun h => hx ((euclDist_eq_zero_iff hC hne x).1 h.symm))
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
      rw [Set.indicator_of_notMem hx]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have h2 : 1 / ((n : ℝ) + 1) ≤ euclDist C x := by linarith
      have hs : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have : 1 ≤ euclDist C x / (1 / ((n : ℝ) + 1)) := (one_le_div hs).2 h2
      show 0 = max 0 (1 - euclDist C x / (1 / ((n : ℝ) + 1)))
      exact (max_eq_left (by linarith)).symm

namespace MetricCurrents.LipApprox

lemma exists_sep_lip {d : ℕ} {F F' : Set (Vec d)} (hF : IsCompact F) (hF' : IsCompact F')
    (hd : Disjoint F F') :
    ∃ φ : Vec d → ℝ, IsBddLipFun φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ (∀ x ∈ F, φ x = 1) ∧
      ∀ x ∈ F', φ x = 0 := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, isBddLipFun_zero, fun x => by simp, by simp, fun x _ => rfl⟩
  have hcl := hF.isClosed
  have hpos : ∀ x ∈ F', 0 < euclDist F x := fun x hx =>
    lt_of_le_of_ne (euclDist_nonneg x) fun h => Set.disjoint_left.1 hd
      ((euclDist_eq_zero_iff hcl hne x).1 h.symm) hx
  have hcont : Continuous (euclDist F) := by
    refine continuous_of_eucl (K := 1) fun x y => ?_
    simpa using abs_euclDist_sub_le hne x y
  obtain ⟨s, hs, hsle⟩ := hF'.exists_forall_le' hcont.continuousOn hpos
  obtain ⟨-, -, hb, hbd, hone, hzero, -, -⟩ := distCutoff_spec hcl hne hs
  exact ⟨distCutoff F s, hb, hbd, hone, fun x hx => hzero x (hsle x hx)⟩

end MetricCurrents.LipApprox

open MetricCurrents.LipApprox in
/-- For a finite measure `m`, a Borel set `B` and
`η > 0` there are compact `F ⊆ B`, `F' ⊆ Bᶜ` and `φ ∈ Lip_b`, `0 ≤ φ ≤ 1`, `φ = 1` on `F`,
`φ = 0` on `F'`, with `m(B \ F) + m(Bᶜ \ F') < η` and `∫ |φ - 1_B| dm < η`. -/
theorem exists_lip_approx_indicator {d : ℕ} (m : Measure (Vec d)) [IsFiniteMeasure m]
    {B : Set (Vec d)} (hB : MeasurableSet B) {η : ℝ} (hη : 0 < η) :
    ∃ (F F' : Set (Vec d)) (φ : Vec d → ℝ), IsCompact F ∧ F ⊆ B ∧ IsCompact F' ∧ F' ⊆ Bᶜ ∧
      IsBddLipFun φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ (∀ x ∈ F, φ x = 1) ∧ (∀ x ∈ F', φ x = 0) ∧
      m (B \ F) + m (Bᶜ \ F') < ENNReal.ofReal η ∧ ∫ x, |φ x - B.indicator 1 x| ∂m < η := by
  have hε : ENNReal.ofReal (η / 2) ≠ 0 := by
    simpa using (half_pos hη)
  obtain ⟨F, hFB, hFc, hFm⟩ := hB.exists_isCompact_lt_add (measure_ne_top m B) hε
  obtain ⟨F', hF'B, hF'c, hF'm⟩ := hB.compl.exists_isCompact_lt_add (measure_ne_top m Bᶜ) hε
  obtain ⟨φ, hφ, hφ01, hφF, hφF'⟩ := exists_sep_lip hFc hF'c
    (Set.disjoint_of_subset hFB hF'B disjoint_compl_right)
  have hd1 : m (B \ F) < ENNReal.ofReal (η / 2) := by
    rw [measure_sdiff hFB hFc.measurableSet.nullMeasurableSet (measure_ne_top m F)]
    refine ENNReal.sub_lt_of_lt_add (measure_mono hFB) ?_
    rwa [add_comm]
  have hd2 : m (Bᶜ \ F') < ENNReal.ofReal (η / 2) := by
    rw [measure_sdiff hF'B hF'c.measurableSet.nullMeasurableSet (measure_ne_top m F')]
    refine ENNReal.sub_lt_of_lt_add (measure_mono hF'B) ?_
    rwa [add_comm]
  have hsum : m (B \ F) + m (Bᶜ \ F') < ENNReal.ofReal η := by
    calc _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := ENNReal.add_lt_add hd1 hd2
      _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  refine ⟨F, F', φ, hFc, hFB, hF'c, hF'B, hφ, hφ01, hφF, hφF', hsum, ?_⟩
  set S : Set (Vec d) := (B \ F) ∪ (Bᶜ \ F') with hS
  have hSm : MeasurableSet S :=
    (hB.diff hFc.measurableSet).union (hB.compl.diff hF'c.measurableSet)
  have hφm : Measurable φ := (continuous_of_eucl hφ.1.choose_spec).measurable
  have hpt : ∀ x, |φ x - B.indicator 1 x| ≤ S.indicator (1 : Vec d → ℝ) x := by
    intro x
    by_cases hxF : x ∈ F
    · have := hFB hxF
      simp [hφF x hxF, Set.indicator_of_mem this, Set.indicator_nonneg]
    by_cases hxF' : x ∈ F'
    · have := hF'B hxF'
      simp [hφF' x hxF', Set.indicator_of_notMem (show x ∉ B from this), Set.indicator_nonneg]
    have hxS : x ∈ S := by
      by_cases hxB : x ∈ B
      · exact Or.inl ⟨hxB, hxF⟩
      · exact Or.inr ⟨hxB, hxF'⟩
    rw [Set.indicator_of_mem hxS]
    have h1 := hφ01 x
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB]; simp; rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hxB]; simp; rw [abs_le]; constructor <;> linarith
  have hint : Integrable (S.indicator (1 : Vec d → ℝ)) m :=
    (integrable_indicator_iff hSm).2 (integrable_const _).integrableOn
  calc ∫ x, |φ x - B.indicator 1 x| ∂m ≤ ∫ x, S.indicator (1 : Vec d → ℝ) x ∂m :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = (m S).toReal := by simp [integral_indicator hSm, Measure.real]
    _ < η := by
        refine ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt ?_ hsum)
        exact measure_union_le _ _

namespace MetricCurrents.LipApprox

lemma isBddLipFun_smul {d : ℕ} (c : ℝ) {f : Vec d → ℝ} (hf : IsBddLipFun f) :
    IsBddLipFun (c • f) := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  refine ⟨⟨‖c‖₊ * K, fun x y => ?_⟩, |c| * C, fun x => ?_⟩
  · have := hK x y
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma isBddLipFun_add {d : ℕ} {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g) :
    IsBddLipFun (f + g) := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  obtain ⟨⟨K', hK'⟩, C', hC'⟩ := hg
  refine ⟨⟨K + K', fun x y => ?_⟩, C + C', fun x => ?_⟩
  · have h1 := hK x y
    have h2 := hK' x y
    simp only [Pi.add_apply, NNReal.coe_add]
    calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ _ := by linarith
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hC x) (hC' x))

lemma integrable_of_bddLip {d : ℕ} (m : Measure (Vec d)) [IsFiniteMeasure m] {f : Vec d → ℝ}
    (hf : IsBddLipFun f) : Integrable f m := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  exact Integrable.of_bound (continuous_of_eucl hK).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa using hC x)

lemma integrable_abs_sub_simple {d : ℕ} (m : Measure (Vec d)) [IsFiniteMeasure m] {f : Vec d → ℝ}
    (hf : IsBddLipFun f) (s : SimpleFunc (Vec d) ℝ) :
    Integrable (fun x => |f x - s x|) m :=
  ((integrable_of_bddLip m hf).sub (SimpleFunc.integrable_of_isFiniteMeasure s)).abs

lemma exists_lip_approx_simple {d : ℕ} (m : Measure (Vec d)) [IsFiniteMeasure m]
    (s : SimpleFunc (Vec d) ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ f : Vec d → ℝ, IsBddLipFun f ∧ ∫ x, |f x - s x| ∂m < ε := by
  refine SimpleFunc.induction (motive := fun s : SimpleFunc (Vec d) ℝ =>
    ∀ ε : ℝ, 0 < ε → ∃ f : Vec d → ℝ, IsBddLipFun f ∧ ∫ x, |f x - s x| ∂m < ε) ?_ ?_ s
  · intro c B hB ε hε
    have hc : 0 < |c| + 1 := by positivity
    obtain ⟨F, F', φ, -, -, -, -, hφ, -, -, -, -, hI⟩ :=
      exists_lip_approx_indicator m hB (div_pos hε hc)
    refine ⟨c • φ, isBddLipFun_smul c hφ, ?_⟩
    have hs : ∀ x, (SimpleFunc.piecewise B hB (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) x
        = c * B.indicator 1 x := by
      intro x
      by_cases hx : x ∈ B <;> simp [SimpleFunc.piecewise_apply, hx]
    have : ∀ x, |(c • φ) x - (SimpleFunc.piecewise B hB (SimpleFunc.const _ c)
        (SimpleFunc.const _ 0)) x| = |c| * |φ x - B.indicator 1 x| := by
      intro x
      rw [hs x, Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul]
    simp_rw [this]
    rw [integral_const_mul]
    calc |c| * ∫ x, |φ x - B.indicator 1 x| ∂m ≤ |c| * (ε / (|c| + 1)) :=
          mul_le_mul_of_nonneg_left hI.le (abs_nonneg _)
      _ = ε * (|c| / (|c| + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one hc).2 (by linarith)) hε
      _ = ε := mul_one ε
  · intro f g _ hf hg ε hε
    obtain ⟨f', hf', hIf⟩ := hf (ε / 2) (half_pos hε)
    obtain ⟨g', hg', hIg⟩ := hg (ε / 2) (half_pos hε)
    refine ⟨f' + g', isBddLipFun_add hf' hg', ?_⟩
    calc ∫ x, |(f' + g') x - (f + g) x| ∂m
        ≤ ∫ x, (|f' x - f x| + |g' x - g x|) ∂m := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            ((integrable_abs_sub_simple m hf' f).add (integrable_abs_sub_simple m hg' g))
            (Eventually.of_forall fun x => ?_)
          simp only [Pi.add_apply, SimpleFunc.coe_add]
          calc |f' x + g' x - (f x + g x)| = |(f' x - f x) + (g' x - g x)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ = ∫ x, |f' x - f x| ∂m + ∫ x, |g' x - g x| ∂m :=
          integral_add (integrable_abs_sub_simple m hf' f) (integrable_abs_sub_simple m hg' g)
      _ < ε := by linarith

end MetricCurrents.LipApprox

open MetricCurrents.LipApprox in
/-- `Lip_b` is `L¹(m)`-dense in `B^∞` for a finite measure `m`. -/
theorem exists_lip_approx_borelBdd {d : ℕ} (m : Measure (Vec d)) [IsFiniteMeasure m]
    {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    ∃ f : ℕ → Vec d → ℝ, (∀ n, IsBddLipFun (f n)) ∧
      Tendsto (fun n => ∫ x, |f n x - h x| ∂m) atTop (𝓝 0) := by
  obtain ⟨hm, C, hC⟩ := hh
  let sn : ℕ → SimpleFunc (Vec d) ℝ := fun n =>
    SimpleFunc.approxOn h hm Set.univ 0 (Set.mem_univ _) n
  have hch : ∀ n, ∃ f : Vec d → ℝ, IsBddLipFun f ∧ ∫ x, |f x - sn n x| ∂m < 1 / ((n : ℝ) + 1) :=
    fun n => exists_lip_approx_simple m (sn n) _ (by positivity)
  choose f hf hfI using hch
  have hhint : Integrable h m :=
    Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun x => by simpa using hC x)
  have hsint : ∀ n, Integrable (fun x => |sn n x - h x|) m := fun n =>
    ((SimpleFunc.integrable_of_isFiniteMeasure (sn n)).sub hhint).abs
  have hlim : Tendsto (fun n => ∫ x, |sn n x - h x| ∂m) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := m)
      (F := fun n x => |sn n x - h x|) (f := fun _ => (0 : ℝ)) (fun _ => 3 * C)
      (fun n => (hsint n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        have h1 := SimpleFunc.norm_approxOn_zero_le hm (Set.mem_univ (0 : ℝ)) x n
        have h2 := hC x
        have h3 : |sn n x| ≤ |h x| + |h x| := by simpa using h1
        have h4 : |h x| ≤ C := h2
        rw [Real.norm_eq_abs, abs_abs]
        calc |sn n x - h x| ≤ |sn n x| + |h x| := abs_sub _ _
          _ ≤ 3 * C := by linarith)
      (Eventually.of_forall fun x => by
        have := (SimpleFunc.tendsto_approxOn hm (Set.mem_univ (0 : ℝ))
          (x := x) (by simp)).sub_const (h x) |>.abs
        simpa using this)
    simpa using this
  refine ⟨f, hf, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add hlim) (fun n => ?_)
    (fun n => ?_)
  · exact integral_nonneg fun x => abs_nonneg _
  · have hfi : Integrable (fun x => |f n x - h x|) m :=
      ((integrable_of_bddLip m (hf n)).sub hhint).abs
    calc ∫ x, |f n x - h x| ∂m ≤ ∫ x, (|f n x - sn n x| + |sn n x - h x|) ∂m :=
          integral_mono hfi ((integrable_abs_sub_simple m (hf n) (sn n)).add (hsint n))
            fun x => abs_sub_le _ _ _
      _ = ∫ x, |f n x - sn n x| ∂m + ∫ x, |sn n x - h x| ∂m :=
          integral_add (integrable_abs_sub_simple m (hf n) (sn n)) (hsint n)
      _ ≤ _ := by have := hfI n; rw [one_div] at this; linarith

open MetricCurrents.LipApprox in
/-- Two finite signed measures with the same integrals
against all of `Lip_b` are equal. -/
theorem signedMeasure_eq_of_integral_lip {d : ℕ} (ν₁ ν₂ : SignedMeasure (Vec d))
    (h : ∀ f : Vec d → ℝ, IsBddLipFun f → ∫ᵛ x, f x ∂•ν₁ = ∫ᵛ x, f x ∂•ν₂) : ν₁ = ν₂ := by
  have hfin : ∀ ν : SignedMeasure (Vec d), IsFiniteMeasure ν.variation := fun ν => by
    rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance
  have hone : IsBddLipFun (fun _ : Vec d => (1 : ℝ)) := ⟨⟨0, fun x y => by simp⟩, 1, fun x => by simp⟩
  have hclosed : ∀ C : Set (Vec d), IsClosed C → ν₁ C = ν₂ C := by
    intro C hC
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    have key : ∀ ν : SignedMeasure (Vec d), Tendsto
        (fun n : ℕ => ∫ᵛ x, distCutoff C (1 / ((n : ℝ) + 1)) x ∂•ν) atTop (𝓝 (ν C)) := by
      intro ν
      have := hfin ν
      have hind : ∫ᵛ x, C.indicator (1 : Vec d → ℝ) x ∂•ν = ν C := by
        have := VectorMeasure.integral_indicator_const (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℝ) (1 : ℝ)
          hC.measurableSet
        simpa [Set.indicator, Pi.one_def] using this
      rw [← hind]
      refine VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrable_const _) ?_ ?_
      · intro n
        obtain ⟨-, -, ⟨⟨K, hK⟩, -⟩, -⟩ := distCutoff_spec hC hne
          (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
        exact (continuous_of_eucl hK).aestronglyMeasurable
      · intro n
        refine Eventually.of_forall fun x => ?_
        obtain ⟨-, -, -, hbd, -⟩ := distCutoff_spec hC hne
          (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd x).1]; exact (hbd x).2
      · refine Eventually.of_forall fun x => ?_
        obtain ⟨-, -, -, -, -, -, -, hlim⟩ := distCutoff_spec hC hne (t := 1) one_pos
        exact hlim x
    have hseq : ∀ n : ℕ, ∫ᵛ x, distCutoff C (1 / ((n : ℝ) + 1)) x ∂•ν₁ =
        ∫ᵛ x, distCutoff C (1 / ((n : ℝ) + 1)) x ∂•ν₂ := fun n => by
      obtain ⟨-, -, hb, -⟩ := distCutoff_spec hC hne
        (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
      exact h _ hb
    exact tendsto_nhds_unique (key ν₁) (by simp_rw [hseq]; exact key ν₂)
  refine VectorMeasure.ext_of_generateFrom {s : Set (Vec d) | IsClosed s}
    (fun s hs => hclosed s hs) (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed)
    isPiSystem_isClosed ?_
  have := hfin ν₁
  have := hfin ν₂
  have h1 := h _ hone
  rw [VectorMeasure.integral_const, VectorMeasure.integral_const] at h1
  simpa using h1

end AFree
