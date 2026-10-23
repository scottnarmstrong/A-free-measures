module

public import AFree.Curves.Dichotomy.LusinDiff
public import AFree.Curves.Dichotomy.LusinWhitney
public import AFree.Curves.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The Lusin-type `C¹` approximation of Lipschitz paths

A one-dimensional Whitney extension theorem
(`whitney_ext_1d`) gives, with the uniformly differentiable compact set of
`egorov_whitney`, the `C¹` function `g`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open PDE

namespace AFree

namespace Lusin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set ℝ} {φ ψ : ℝ → E} {L : ℝ}

/-- A point outside `S` and strictly between `min S` and `max S` lies in a gap of `S`. -/
lemma exists_gap (hS : IsCompact S) {x : ℝ} (hxS : x ∉ S) (h1 : sInf S ≤ x) (h2 : x ≤ sSup S)
    (hne : S.Nonempty) : ∃ p q, p ∈ S ∧ q ∈ S ∧ p < x ∧ x < q ∧ ∀ s ∈ S, s ∉ Ioo p q := by
  have hK1 : IsCompact (S ∩ Iic x) := hS.inter_right isClosed_Iic
  have hK2 : IsCompact (S ∩ Ici x) := hS.inter_right isClosed_Ici
  have hp := hK1.sSup_mem ⟨sInf S, hS.sInf_mem hne, h1⟩
  have hq := hK2.sInf_mem ⟨sSup S, hS.sSup_mem hne, h2⟩
  refine ⟨sSup (S ∩ Iic x), sInf (S ∩ Ici x), hp.1, hq.1,
    lt_of_le_of_ne hp.2 fun h => hxS (h ▸ hp.1), lt_of_le_of_ne hq.2 fun h => hxS (h ▸ hq.1), ?_⟩
  intro s hs hsm
  by_cases hsx : s ≤ x
  · exact (not_le.2 hsm.1) (le_csSup hK1.bddAbove ⟨hs, hsx⟩)
  · exact (not_le.2 hsm.2) (csInf_le hK2.bddBelow ⟨hs, (not_le.1 hsx).le⟩)

/-- The extension is `C¹` near a point outside `S`. -/
lemma ext_off (hS : IsCompact S) (hne : S.Nonempty) {x : ℝ} (hxS : x ∉ S) :
    DifferentiableAt ℝ (ext S φ ψ) x ∧ ContinuousAt (deriv (ext S φ ψ)) x := by
  by_cases hl : x < sInf S
  · have hev : ∀ᶠ y in 𝓝 x, ext S φ ψ y = φ (sInf S) + (y - sInf S) • ψ (sInf S) := by
      filter_upwards [Iio_mem_nhds hl] with y hy using ext_left hS hne (le_of_lt hy)
    have hd : ∀ᶠ y in 𝓝 x, HasDerivAt (ext S φ ψ) (ψ (sInf S)) y := by
      filter_upwards [hev.eventually_nhds] with y hy
      have : HasDerivAt (fun y : ℝ => φ (sInf S) + (y - sInf S) • ψ (sInf S)) (ψ (sInf S)) y := by
        simpa using (((hasDerivAt_id y).sub_const (sInf S)).smul_const (ψ (sInf S))).const_add
          (φ (sInf S))
      exact this.congr_of_eventuallyEq hy
    refine ⟨hd.self_of_nhds.differentiableAt, ?_⟩
    exact continuousAt_const.congr (hd.mono fun y hy => (hy.deriv).symm)
  by_cases hr : sSup S < x
  · have hev : ∀ᶠ y in 𝓝 x, ext S φ ψ y = φ (sSup S) + (y - sSup S) • ψ (sSup S) := by
      filter_upwards [Ioi_mem_nhds hr] with y hy using ext_right hS hne (le_of_lt hy)
    have hd : ∀ᶠ y in 𝓝 x, HasDerivAt (ext S φ ψ) (ψ (sSup S)) y := by
      filter_upwards [hev.eventually_nhds] with y hy
      have : HasDerivAt (fun y : ℝ => φ (sSup S) + (y - sSup S) • ψ (sSup S)) (ψ (sSup S)) y := by
        simpa using (((hasDerivAt_id y).sub_const (sSup S)).smul_const (ψ (sSup S))).const_add
          (φ (sSup S))
      exact this.congr_of_eventuallyEq hy
    refine ⟨hd.self_of_nhds.differentiableAt, ?_⟩
    exact continuousAt_const.congr (hd.mono fun y hy => (hy.deriv).symm)
  obtain ⟨p, q, hp, hq, hpx, hxq, hgap⟩ := exists_gap hS hxS (not_lt.1 hl) (not_lt.1 hr) hne
  have hpq : p < q := hpx.trans hxq
  have hd : ∀ y ∈ Ioo p q, HasDerivAt (ext S φ ψ)
      (hermD p q (φ p) (φ q) (ψ p) (ψ q) y) y := fun y hy => by
    refine (herm_hasDerivAt hpq (φ p) (φ q) (ψ p) (ψ q) y).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz using
      ext_gap hS hp hq hpq hgap (Ioo_subset_Icc_self hz)
  have hmem : Ioo p q ∈ 𝓝 x := Ioo_mem_nhds hpx hxq
  refine ⟨(hd x ⟨hpx, hxq⟩).differentiableAt, ?_⟩
  have hc : ContinuousAt (hermD p q (φ p) (φ q) (ψ p) (ψ q)) x := by
    unfold hermD hermW
    fun_prop
  exact hc.congr (by filter_upwards [hmem] with y hy using ((hd y hy).deriv).symm)

/-- One-dimensional Whitney extension: data `(φ, ψ)` on a compact `S ⊆ ℝ`
satisfying the uniform Whitney condition are the value and derivative on `S` of a `C¹` function. -/
theorem whitney_ext_1d (hS : IsCompact S)
    (hlip : ∀ s ∈ S, ∀ s' ∈ S, ‖φ s' - φ s‖ ≤ L * |s' - s|) (hbdd : ∀ s ∈ S, ‖ψ s‖ ≤ L)
    (hW : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S, |s' - s| < δ →
      ‖φ s' - φ s - (s' - s) • ψ s‖ ≤ η * |s' - s|) :
    ∃ g : ℝ → E, ContDiff ℝ 1 g ∧ ∀ s ∈ S, g s = φ s ∧ deriv g s = ψ s := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, contDiff_const, by simp⟩
  set g := ext S φ ψ with hg
  have hstrict : ∀ x₀ ∈ S, ∀ η' : ℝ, 0 < η' → ∃ δ : ℝ, 0 < δ ∧ ∀ y z : ℝ, |y - x₀| < δ →
      |z - x₀| < δ → ‖(g y - g z) - (y - z) • ψ x₀‖ ≤ η' * |y - z| := by
    intro x₀ hx₀ η' hη'
    obtain ⟨δW, hδW, hw⟩ := hW (η' / 18) (by positivity)
    have hL : 0 ≤ L := (norm_nonneg _).trans (hbdd x₀ hx₀)
    have hpar : Pars S φ ψ L (η' / 18) δW := ⟨hlip, hbdd, hw, by positivity, hδW⟩
    refine ⟨min (δW / 2) (η' / 18 * δW / (16 * L + 1)), by positivity, fun y z hy hz => ?_⟩
    have hδ1 : 2 * min (δW / 2) (η' / 18 * δW / (16 * L + 1)) ≤ δW := by
      have := min_le_left (δW / 2) (η' / 18 * δW / (16 * L + 1)); linarith
    have hδ2 : 16 * L * min (δW / 2) (η' / 18 * δW / (16 * L + 1)) ≤ η' / 18 * δW := by
      have h1 := min_le_right (δW / 2) (η' / 18 * δW / (16 * L + 1))
      rw [le_div_iff₀ (by positivity)] at h1
      have h2 : 0 ≤ min (δW / 2) (η' / 18 * δW / (16 * L + 1)) := by positivity
      nlinarith
    have key : ∀ y z : ℝ, y ≤ z → |y - x₀| < min (δW / 2) (η' / 18 * δW / (16 * L + 1)) →
        |z - x₀| < min (δW / 2) (η' / 18 * δW / (16 * L + 1)) →
        ‖(g z - g y) - (z - y) • ψ x₀‖ ≤ η' * (z - y) := by
      intro y z hyz hy hz
      have := errF_chain hS hpar hx₀ hδ1 hδ2 hyz hy hz
      have e : errF S φ ψ (ψ x₀) z - errF S φ ψ (ψ x₀) y = (g z - g y) - (z - y) • ψ x₀ := by
        simp only [errF, hg]; module
      rw [e] at this
      linarith
    rcases le_total y z with hyz | hzy
    · have := key y z hyz hy hz
      rw [abs_of_nonpos (sub_nonpos.2 hyz), ← norm_neg]
      have e : -((g y - g z) - (y - z) • ψ x₀) = (g z - g y) - (z - y) • ψ x₀ := by module
      rw [e]; linarith
    · have := key z y hzy hz hy
      rwa [abs_of_nonneg (sub_nonneg.2 hzy)]
  have hdiffS : ∀ x₀ ∈ S, HasDerivAt g (ψ x₀) x₀ := by
    intro x₀ hx₀
    refine hasDerivAt_iff_isLittleO.2 (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
    obtain ⟨δ, hδ, hs⟩ := hstrict x₀ hx₀ c hc
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with y hy
    have := hs y x₀ (by simpa [Real.dist_eq] using hy) (by simpa using hδ)
    have e : g x₀ = φ x₀ := ext_of_mem hx₀
    simpa [Real.norm_eq_abs] using this
  have hdiff : ∀ x, DifferentiableAt ℝ g x := fun x => by
    by_cases hx : x ∈ S
    · exact (hdiffS x hx).differentiableAt
    · exact (ext_off hS hne hx).1
  have hcont : ∀ x, ContinuousAt (deriv g) x := fun x => by
    by_cases hx : x ∈ S
    · refine Metric.continuousAt_iff.2 fun ε hε => ?_
      obtain ⟨δ, hδ, hs⟩ := hstrict x hx (ε / 2) (by positivity)
      refine ⟨δ, hδ, fun y hy => ?_⟩
      rw [Real.dist_eq] at hy
      have hd : HasDerivAt (fun z => g z - z • ψ x) (deriv g y - ψ x) y := by
        exact ((hdiff y).hasDerivAt.sub ((hasDerivAt_id y).smul_const (ψ x))).congr_deriv (by simp)
      have hn := hd.le_of_lip' (by positivity : (0 : ℝ) ≤ ε / 2) (by
        filter_upwards [(isOpen_lt (by fun_prop) continuous_const :
          IsOpen {z : ℝ | |z - x| < δ}).mem_nhds hy] with z hz
        have := hs z y hz hy
        have e : (g z - z • ψ x) - (g y - y • ψ x) = (g z - g y) - (z - y) • ψ x := by module
        rw [e, Real.norm_eq_abs]
        simpa [Real.norm_eq_abs] using this)
      rw [dist_eq_norm, (hdiffS x hx).deriv]
      linarith
    · exact (ext_off hS hne hx).2
  refine ⟨g, contDiff_one_iff_deriv.2 ⟨hdiff, continuous_iff_continuousAt.2 hcont⟩, fun s hs => ?_⟩
  exact ⟨ext_of_mem hs, (hdiffS s hs).deriv⟩

end Lusin

/-- Lusin-type `C¹` approximation of a Lipschitz path `f : ℝ → ℝ^m`: for `a < b` and
`ε > 0` there are a compact `S ⊆ [a, b]` with `𝓛¹([a, b] \ S) < ε` on which `f` is differentiable, and
`g ∈ C¹(ℝ; ℝ^m)` with `g = f` and `g' = f'` on `S`. -/
theorem lusin_c1_approx {m : ℕ} {f : ℝ → Vec m} {L : ℝ≥0} (hf : LipschitzWith L f) {a b : ℝ}
    (_hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set ℝ, IsCompact S ∧ S ⊆ Set.Icc a b ∧
      MeasureTheory.volume (Set.Icc a b \ S) < ENNReal.ofReal ε ∧
      (∀ s ∈ S, DifferentiableAt ℝ f s) ∧
      ∃ g : ℝ → Vec m, ContDiff ℝ 1 g ∧ ∀ s ∈ S, g s = f s ∧ deriv g s = deriv f s := by
  obtain ⟨S, hSc, hSab, hSvol, hSd, hW⟩ := Lusin.egorov_whitney hf a b hε
  refine ⟨S, hSc, hSab, hSvol, hSd, ?_⟩
  refine Lusin.whitney_ext_1d (L := (L : ℝ)) hSc (fun s _ s' _ => ?_) (fun s _ => ?_) hW
  · have := hf.dist_le_mul s' s
    rwa [dist_eq_norm, Real.dist_eq] at this
  · exact norm_deriv_le_of_lipschitz hf

end AFree
