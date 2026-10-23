module

public import AFree.Curves.Dichotomy.LusinPieces
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strict differentiability of the extension at points of `S`

The two-point estimate
`‖(g y - g z) - (y - z) ψ(x₀)‖ ≤ 18 η |y - z|` near `x₀` is proved, by three cases
(`s ∈ S`, ray, gap) with a `θ`-weighted gap bound, chained through the points of `S` in
`[y, z]`. It gives both differentiability at `x₀` and continuity of the derivative there.
-/

@[expose] public section

open Set

namespace AFree

namespace Lusin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set ℝ} {φ ψ : ℝ → E} {L η δW δ x₀ : ℝ}

/-- The error `g(y) - y ψ(x₀)` of the extension against the tangent at `x₀`. -/
noncomputable def errF (S : Set ℝ) (φ ψ : ℝ → E) (c : E) (y : ℝ) : E := ext S φ ψ y - y • c

/-- Estimate on a piece with no point of `S` in the open interval `(u, v)`. -/
lemma errF_piece (hS : IsCompact S) (h : Pars S φ ψ L η δW) (hx : x₀ ∈ S) (hδ1 : δ ≤ δW)
    (hδ2 : 16 * L * δ ≤ η * δW) {u v : ℝ} (huv : u < v) (hu : |u - x₀| < δ) (hv : |v - x₀| < δ)
    (hgap : ∀ s ∈ S, s ∉ Ioo u v) :
    ‖errF S φ ψ (ψ x₀) v - errF S φ ψ (ψ x₀) u‖ ≤ 18 * η * (v - u) := by
  have hne : S.Nonempty := ⟨x₀, hx⟩
  have hη := h.hη
  rw [abs_lt] at hu hv
  have hvu : 0 ≤ v - u := (sub_pos.2 huv).le
  by_cases hA : ∀ s ∈ S, u < s
  · -- left ray
    have ha : sInf S ∈ S := hS.sInf_mem hne
    have hvle : v ≤ sInf S := by
      by_contra hlt
      exact hgap _ ha ⟨hA _ ha, not_le.1 hlt⟩
    have hax : sInf S ≤ x₀ := csInf_le hS.bddBelow hx
    have hc : ‖ψ (sInf S) - ψ x₀‖ ≤ 2 * η := h.psi_close hx ha (by
      rw [abs_lt]; constructor <;> linarith)
    have e : errF S φ ψ (ψ x₀) v - errF S φ ψ (ψ x₀) u = (v - u) • (ψ (sInf S) - ψ x₀) := by
      simp only [errF, ext_left hS hne hvle, ext_left hS hne (huv.le.trans hvle)]
      module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hvu]
    nlinarith
  by_cases hB : ∀ s ∈ S, s < v
  · -- right ray
    have hb : sSup S ∈ S := hS.sSup_mem hne
    have hule : sSup S ≤ u := by
      by_contra hlt
      exact hgap _ hb ⟨not_le.1 hlt, hB _ hb⟩
    have hbx : x₀ ≤ sSup S := le_csSup hS.bddAbove hx
    have hc : ‖ψ (sSup S) - ψ x₀‖ ≤ 2 * η := h.psi_close hx hb (by
      rw [abs_lt]; constructor <;> linarith)
    have e : errF S φ ψ (ψ x₀) v - errF S φ ψ (ψ x₀) u = (v - u) • (ψ (sSup S) - ψ x₀) := by
      simp only [errF, ext_right hS hne hule, ext_right hS hne (hule.trans huv.le)]
      module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hvu]
    nlinarith
  · -- a gap
    push Not at hA hB
    obtain ⟨s₁, hs₁, hs₁u⟩ := hA
    obtain ⟨s₂, hs₂, hvs₂⟩ := hB
    have hK1 : IsCompact (S ∩ Iic u) := hS.inter_right isClosed_Iic
    have hK2 : IsCompact (S ∩ Ici v) := hS.inter_right isClosed_Ici
    have hp := hK1.sSup_mem ⟨s₁, hs₁, hs₁u⟩
    have hq := hK2.sInf_mem ⟨s₂, hs₂, hvs₂⟩
    set p := sSup (S ∩ Iic u) with hpdef
    set q := sInf (S ∩ Ici v) with hqdef
    have hpu : p ≤ u := csSup_le ⟨s₁, hs₁, hs₁u⟩ fun s hs => hs.2
    have hvq : v ≤ q := le_csInf ⟨s₂, hs₂, hvs₂⟩ fun s hs => hs.2
    have hpq : p < q := lt_of_le_of_lt hpu (huv.trans_le hvq)
    have hgap' : ∀ s ∈ S, s ∉ Ioo p q := by
      intro s hs hsm
      by_cases h1 : s ≤ u
      · exact (not_le.2 hsm.1) (le_csSup hK1.bddAbove ⟨hs, h1⟩)
      by_cases h2 : v ≤ s
      · exact (not_le.2 hsm.2) (csInf_le hK2.bddBelow ⟨hs, h2⟩)
      exact hgap s hs ⟨not_le.1 h1, not_le.1 h2⟩
    have hsub : Icc u v ⊆ Icc p q := Icc_subset_Icc hpu hvq
    have hbound : ∀ t ∈ Icc u v,
        ‖hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ x₀‖ ≤ 18 * η := by
      intro t ht
      have hnot := hgap' x₀ hx
      rcases le_or_gt x₀ p with hxp | hxp
      · refine h.gap_left hp.1 hq.1 hpq (hsub ht) ?_ hδ2 (by linarith [ht.2])
        exact h.psi_close hx hp.1 (by rw [abs_lt]; constructor <;> linarith)
      · have hxq : q ≤ x₀ := by
          by_contra hlt
          exact hnot ⟨hxp, not_le.1 hlt⟩
        refine h.gap_right hp.1 hq.1 hpq (hsub ht) ?_ hδ2 (by linarith [ht.1])
        exact h.psi_close hx hq.1 (by rw [abs_lt]; constructor <;> linarith)
    have hd : ∀ t ∈ Icc u v, HasDerivWithinAt
        (fun t => herm p q (φ p) (φ q) (ψ p) (ψ q) t - t • ψ x₀)
        (hermD p q (φ p) (φ q) (ψ p) (ψ q) t - ψ x₀) (Icc u v) t := fun t _ => by
      have := (herm_hasDerivAt hpq (φ p) (φ q) (ψ p) (ψ q) t).sub
        ((hasDerivAt_id t).smul_const (ψ x₀))
      exact this.hasDerivWithinAt.congr_deriv (by simp)
    have mv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Icc u v)
      (left_mem_Icc.2 huv.le) (right_mem_Icc.2 huv.le)
    have e1 : errF S φ ψ (ψ x₀) v = herm p q (φ p) (φ q) (ψ p) (ψ q) v - v • ψ x₀ := by
      simp only [errF, ext_gap hS hp.1 hq.1 hpq hgap' (hsub (right_mem_Icc.2 huv.le))]
    have e2 : errF S φ ψ (ψ x₀) u = herm p q (φ p) (φ q) (ψ p) (ψ q) u - u • ψ x₀ := by
      simp only [errF, ext_gap hS hp.1 hq.1 hpq hgap' (hsub (left_mem_Icc.2 huv.le))]
    rw [e1, e2]
    rw [Real.norm_eq_abs, abs_of_nonneg hvu] at mv
    exact mv

/-- Two-point estimate at `x₀ ∈ S`: for `y ≤ z` within `δ` of
`x₀`, `‖(g z - g y) - (z - y) ψ(x₀)‖ ≤ 18 η (z - y)`, where `g = ext S φ ψ`. -/
theorem errF_chain (hS : IsCompact S) (h : Pars S φ ψ L η δW) (hx : x₀ ∈ S) (hδ1 : 2 * δ ≤ δW)
    (hδ2 : 16 * L * δ ≤ η * δW) {y z : ℝ} (hyz : y ≤ z) (hy : |y - x₀| < δ) (hz : |z - x₀| < δ) :
    ‖errF S φ ψ (ψ x₀) z - errF S φ ψ (ψ x₀) y‖ ≤ 18 * η * (z - y) := by
  have hδ0 : 0 < δ := (abs_nonneg _).trans_lt hy
  have hη := h.hη
  have piece : ∀ u v : ℝ, u ≤ v → |u - x₀| < δ → |v - x₀| < δ → (∀ s ∈ S, s ∉ Ioo u v) →
      ‖errF S φ ψ (ψ x₀) v - errF S φ ψ (ψ x₀) u‖ ≤ 18 * η * (v - u) := by
    intro u v huv hu hv hg
    rcases huv.eq_or_lt with rfl | hlt
    · simp
    · exact errF_piece hS h hx (by linarith) hδ2 hlt hu hv hg
  by_cases hK : ∃ s ∈ S, s ∈ Icc y z
  · have hK1 : IsCompact (S ∩ Icc y z) := hS.inter_right isClosed_Icc
    obtain ⟨s₀, hs₀S, hs₀⟩ := hK
    have hw := hK1.sInf_mem ⟨s₀, hs₀S, hs₀⟩
    have hw' := hK1.sSup_mem ⟨s₀, hs₀S, hs₀⟩
    set w := sInf (S ∩ Icc y z) with hwdef
    set w' := sSup (S ∩ Icc y z) with hw'def
    have hyw : y ≤ w := hw.2.1
    have hwz : w ≤ z := hw.2.2
    have hyw' : y ≤ w' := hw'.2.1
    have hw'z : w' ≤ z := hw'.2.2
    have hww' : w ≤ w' := (csInf_le hK1.bddBelow ⟨hs₀S, hs₀⟩).trans
      (le_csSup hK1.bddAbove ⟨hs₀S, hs₀⟩)
    rw [abs_lt] at hy hz
    have hwx : |w - x₀| < δ := abs_lt.2 ⟨by linarith, by linarith⟩
    have hw'x : |w' - x₀| < δ := abs_lt.2 ⟨by linarith, by linarith⟩
    have t1 := piece y w hyw (abs_lt.2 hy) hwx fun s hs hsm =>
      (not_le.2 hsm.2) (csInf_le hK1.bddBelow ⟨hs, hsm.1.le, hsm.2.le.trans hwz⟩)
    have t3 := piece w' z hw'z hw'x (abs_lt.2 hz) fun s hs hsm =>
      (not_le.2 hsm.1) (le_csSup hK1.bddAbove ⟨hs, hyw'.trans hsm.1.le, hsm.2.le⟩)
    have hdw : |w' - w| < δW := by
      rw [abs_lt] at hwx hw'x; rw [abs_lt]; constructor <;> linarith
    have hψ1 : ‖ψ w - ψ x₀‖ ≤ 2 * η := h.psi_close hx hw.1 (by
      rw [abs_lt] at hwx; rw [abs_lt]; constructor <;> linarith [hwx.1, hwx.2])
    have t2 : ‖errF S φ ψ (ψ x₀) w' - errF S φ ψ (ψ x₀) w‖ ≤ 18 * η * (w' - w) := by
      have e : errF S φ ψ (ψ x₀) w' - errF S φ ψ (ψ x₀) w =
          (φ w' - φ w - (w' - w) • ψ w) + (w' - w) • (ψ w - ψ x₀) := by
        simp only [errF, ext_of_mem hw.1, ext_of_mem hw'.1]
        module
      have hw1 := h.whit w hw.1 w' hw'.1 hdw
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hww')]
      rw [abs_of_nonneg (sub_nonneg.2 hww')] at hw1
      nlinarith [sub_nonneg.2 hww']
    calc _ = ‖(errF S φ ψ (ψ x₀) z - errF S φ ψ (ψ x₀) w') +
          (errF S φ ψ (ψ x₀) w' - errF S φ ψ (ψ x₀) w) +
          (errF S φ ψ (ψ x₀) w - errF S φ ψ (ψ x₀) y)‖ := by congr 1; abel
      _ ≤ ‖errF S φ ψ (ψ x₀) z - errF S φ ψ (ψ x₀) w'‖ +
          ‖errF S φ ψ (ψ x₀) w' - errF S φ ψ (ψ x₀) w‖ +
          ‖errF S φ ψ (ψ x₀) w - errF S φ ψ (ψ x₀) y‖ :=
        (norm_add₃_le)
      _ ≤ 18 * η * (z - y) := by nlinarith
  · push Not at hK
    exact piece y z hyz hy hz fun s hs hsm => hK s hs (Ioo_subset_Icc_self hsm)

end Lusin

end AFree
