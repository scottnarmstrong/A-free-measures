module

public import AFree.Curves.BundleTop.Borel
public import AFree.Curves.Arc
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# `W` passes the `C¹`-arc test
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ} {w : ℕ → Vec d} {M : ℕ → ℕ → Set (Vec d)}

private lemma vecNormSq_sub_eq (a b : Vec d) :
    vecNormSq (a - b) = vecNormSq a - 2 * vecDot a b + vecNormSq b := by
  have h := vecDot_self (a - b)
  rw [vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_self, vecDot_self] at h
  have hc : vecDot b a = vecDot a b := vecDot_comm b a
  rw [hc] at h
  linarith

/-- `cos(1/N) < u ⬝ e` for unit vectors with `|e - u| < 1/(2N)` and `N ≥ 2`. -/
private lemma cos_lt_dot {u e : Vec d} (hu : vecEuclideanNorm u = 1) (he : vecEuclideanNorm e = 1)
    {N : ℝ} (hN : 2 ≤ N) (h : vecEuclideanNorm (e - u) < 1 / (2 * N)) :
    Real.cos (1 / N) < vecDot u e := by
  have hN0 : 0 < N := by linarith
  set y : ℝ := 1 / N with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 / 2 := by
    rw [hy, div_le_div_iff₀ hN0 (by norm_num)]; linarith
  have hcos := Real.cos_bound (x := y) (by rw [abs_of_pos hy0]; linarith)
  rw [abs_of_pos hy0] at hcos
  have hc : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
    have := (abs_le.1 hcos).2; linarith
  set t := vecEuclideanNorm (e - u) with ht
  have ht0 : 0 ≤ t := vecEuclideanNorm_nonneg _
  have ht2 : t ^ 2 < y ^ 2 / 4 := by
    have h2 : t < y / 2 := by
      have : 1 / (2 * N) = y / 2 := by rw [hy]; field_simp
      linarith
    nlinarith
  have hdot : vecDot u e = 1 - t ^ 2 / 2 := by
    have h1 := vecNormSq_sub_eq e u
    rw [← vecEuclideanNorm_sq] at h1
    rw [← vecEuclideanNorm_sq, ← vecEuclideanNorm_sq, he, hu, vecDot_comm] at h1
    rw [ht]; linarith
  rw [hdot]
  have : y ^ 4 * (5 / 96) < y ^ 2 * (3 / 8) := by
    have : y ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [sq_nonneg y, pow_pos hy0 2]
  nlinarith

/-- A unit vector `v̂` that is `1/(2(n+2))`-approximated by the axis `wᵢ` lies in `int C(wᵢ, 1/(n+2))`. -/
private lemma mem_intCone_of_near {v u e : Vec d} (hv : v ≠ 0) (hu : vecEuclideanNorm u = 1)
    (he : vecEuclideanNorm e = 1) (hvu : v = vecEuclideanNorm v • u) {N : ℝ} (hN : 2 ≤ N)
    (h : vecEuclideanNorm (e - u) < 1 / (2 * N)) : v ∈ intCone e (1 / N) := by
  have hpos : 0 < vecEuclideanNorm v := vecEuclideanNorm_pos_iff.2 hv
  have := cos_lt_dot hu he hN h
  show Real.cos (1 / N) * vecEuclideanNorm v < vecDot v e
  conv_rhs => rw [hvu, vecDot_smul_left]
  nlinarith

/-- The key step: if the unit direction `u` of `v` is approximated by axes
`wᵢ ∈ A_n(x)` for every `n`, then `v ∈ W(x)`. -/
private lemma mem_selW_of_axes {x v u : Vec d} (hvu : v = vecEuclideanNorm v • u)
    (hax : ∀ n : ℕ, ∃ i, x ∈ M i n ∧ vecEuclideanNorm (w i - u) < 1 / (2 * ((n : ℝ) + 2))) :
    v ∈ selW w M x := by
  have hu : u ∈ selK w M x := by
    refine mem_selK.2 fun m => Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    obtain ⟨i, hx, hlt⟩ := hax (max m N)
    refine ⟨w i, mem_selA ⟨max m N, le_max_left _ _, hx⟩, ?_⟩
    rw [dist_eq_norm]
    have h1 : ‖u - w i‖ ≤ vecEuclideanNorm (w i - u) := by
      rw [← norm_neg, neg_sub]; exact norm_le_vecEuclideanNorm _
    have h2 : 1 / (2 * (((max m N : ℕ) : ℝ) + 2)) < ε := by
      have hNN : (N : ℝ) ≤ ((max m N : ℕ) : ℝ) := by exact_mod_cast le_max_right m N
      have hε1 : 1 / ε < ((max m N : ℕ) : ℝ) + 2 := by linarith
      rw [div_lt_iff₀ hε] at hε1
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hvu]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hu)

/-- For every `C¹` arc, `γ'(s) ∈ W(γ s)` at `𝓗¹`-a.e. point, hence `W` passes
the `C¹`-arc test and `W ∈ 𝒢_μ` for every measure `μ`. The axes `wᵢ` are unit and dense in the
sphere, and `M i n` are measurable with `(M i n)ᶜ` a `C(wᵢ, 1/(n+2))`-null set. -/
theorem opt_test (hw : ∀ i, vecEuclideanNorm (w i) = 1)
    (hdense : ∀ v, vecEuclideanNorm v = 1 → ∀ ε > 0, ∃ i, vecEuclideanNorm (w i - v) < ε)
    (hM : ∀ i n, MeasurableSet (M i n))
    (hN : ∀ i n : ℕ, IsCNull (cone (w i) (1 / ((n : ℝ) + 2))) (M i n)ᶜ) :
    (∀ (γ : ℝ → Vec d) (J : Set ℝ), IsC1Arc γ J →
      ∀ᵐ x ∂(euclideanHausdorffOne d), ∀ s ∈ J, γ s = x → deriv γ s ∈ selW w M x) ∧
    ∀ μ : Measure (Vec d), IsDecompTestField μ (selW w M) := by
  have harc : ∀ (γ : ℝ → Vec d) (J : Set ℝ), IsC1Arc γ J →
      ∀ᵐ x ∂(euclideanHausdorffOne d), ∀ s ∈ J, γ s = x → deriv γ s ∈ selW w M x := by
    intro γ J hγ
    obtain ⟨⟨a, b, rfl⟩, hC1, -, hne⟩ := hγ
    set X0 : Set (Vec d) := ⋃ i, ⋃ n : ℕ, (M i n)ᶜ ∩
      γ '' (Ioo a b ∩ deriv γ ⁻¹' intCone (w i) (1 / ((n : ℝ) + 2))) with hX0
    have hX0null : euclideanHausdorffOne d X0 = 0 :=
      measure_iUnion_null fun i => measure_iUnion_null fun n =>
        (arc_ccurve (e := w i) (α := 1 / ((n : ℝ) + 2)) isOpen_Ioo hC1).2.2.2 _ (hN i n)
    refine measure_mono_null (fun x hx => ?_) hX0null
    by_contra hxX
    apply hx
    intro s hs hsx
    have hv : deriv γ s ≠ 0 := hne s hs
    set v := deriv γ s with hvdef
    have hpos : 0 < vecEuclideanNorm v := vecEuclideanNorm_pos_iff.2 hv
    set u : Vec d := (vecEuclideanNorm v)⁻¹ • v with hu
    have hu1 : vecEuclideanNorm u = 1 := by
      rw [hu, vecEuclideanNorm_smul, abs_inv, abs_of_pos hpos]
      exact inv_mul_cancel₀ hpos.ne'
    have hvu : v = vecEuclideanNorm v • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    refine mem_selW_of_axes (u := u) hvu fun n => ?_
    have hn : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 2)) := by positivity
    obtain ⟨i, hi⟩ := hdense u hu1 _ hn
    refine ⟨i, ?_, hi⟩
    have hcone : v ∈ intCone (w i) (1 / ((n : ℝ) + 2)) :=
      mem_intCone_of_near hv hu1 (hw i) hvu (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hi
    by_contra hxM
    apply hxX
    refine mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨n, hxM, s, ⟨hs, hcone⟩, hsx⟩⟩
  refine ⟨harc, fun μ => ⟨opt_borel hw hM, fun E _ => Eventually.of_forall fun t γ J hγ => ?_⟩⟩
  exact ae_restrict_of_ae (harc γ J hγ)

end AFree.BundleTop
