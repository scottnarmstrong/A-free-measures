module

public import AFree.Curves.Perturb.GMono

/-!
# The function `g` is `1/tan α`-Lipschitz along `W = e^⊥`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ} {A : Set (Vec d)} {ε : ℝ}

private lemma perturbG_aux_W (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (x : Vec d) {v : Vec d} (hv : vecDot v e = 0) :
    perturbG e α A x ≤ perturbG e α A (x + v) + vecEuclideanNorm v / Real.tan α := by
  have htpos : 0 < Real.tan α := Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2
  have hne : (perturbVals e α A x).Nonempty := ⟨0, perturbVals_nonempty he htpos.le A x⟩
  have hbdd := perturbVals_bddAbove hε hA (x + v)
  have hn0 : 0 ≤ vecEuclideanNorm v := vecEuclideanNorm_nonneg v
  refine csSup_le hne ?_
  rintro r ⟨a, b, η, hab, hxb, hη, hηb, rfl⟩
  have key : (perturbMeas e A a b η).toReal - (b - vecDot x e) -
      vecEuclideanNorm v / Real.tan α ≤ perturbG e α A (x + v) := by
    rcases hn0.eq_or_lt with h0 | hpos
    · have hv0 : v = 0 := vecEuclideanNorm_eq_zero_iff.mp h0.symm
      subst hv0
      have hm : (perturbMeas e A a b η).toReal - (b - vecDot x e) ∈
          perturbVals e α A (x + 0) :=
        ⟨a, b, η, hab, by simpa using hxb, hη, by simpa using hηb, by simp⟩
      have := le_csSup (perturbVals_bddAbove hε hA (x + 0)) hm
      rw [← h0, zero_div, sub_zero]
      exact this
    · set n := vecEuclideanNorm v with hn
      set ζ : ℝ → Vec d := fun u => (x - vecDot x e • e) + ((u - b) * (Real.tan α / n)) • v
        with hζ
      have hζc : IsConeGraphFn e α b (b + n / Real.tan α) ζ := by
        refine ⟨fun u _ => ?_, fun u _ u' _ => ?_⟩
        · rw [hζ]; simp only
          rw [vecDot_add_left, vecDot_smul_left, hv, perturb_wPart_perp he, mul_zero, add_zero]
        · have : ζ u - ζ u' = ((u - u') * (Real.tan α / n)) • v := by
            simp only [hζ]; rw [add_sub_add_left_eq_sub, ← sub_smul]; ring_nf
          rw [this, vecEuclideanNorm_smul, ← hn, abs_mul, abs_of_pos (div_pos htpos hpos)]
          field_simp
          exact le_rfl
      have hbb : b ≤ b + n / Real.tan α := by
        have := div_pos hpos htpos; linarith
      have hζb : η b = ζ b := by simp [hζ, hηb]
      have hext := IsConeGraphFn.extend hη hζc hζb
      set η' : ℝ → Vec d := fun u => if u ≤ b then η u else ζ u with hη'
      have hmem : (perturbMeas e A a (b + n / Real.tan α) η').toReal -
          (b + n / Real.tan α - vecDot (x + v) e) ∈ perturbVals e α A (x + v) := by
        refine ⟨a, b + n / Real.tan α, η', hab.trans hbb, ?_, hext, ?_, rfl⟩
        · rw [perturb_dot_add_perp hv]; exact hxb.trans hbb
        · have hnot : ¬ (b + n / Real.tan α ≤ b) := by
            have := div_pos hpos htpos; linarith
          rw [perturb_wPart_add_perp hv]
          simp only [hη', hnot, ite_false, hζ]
          have : (b + n / Real.tan α - b) * (Real.tan α / n) = 1 := by
            field_simp
            ring
          rw [this, one_smul]
      have hmeas : perturbMeas e A a b η ≤ perturbMeas e A a (b + n / Real.tan α) η' := by
        refine measure_mono fun u ⟨hu, hP⟩ => ⟨⟨hu.1, hu.2.trans hbb⟩, ?_⟩
        have : graphCurve e η u = graphCurve e η' u := by simp [graphCurve, hη', hu.2]
        have h' : graphCurve e η u ∈ A := hP
        rw [this] at h'; exact h'
      have h1 := ENNReal.toReal_mono (perturbMeas_lt_top e A a (b + n / Real.tan α) η').ne hmeas
      have := le_csSup hbdd hmem
      rw [perturb_dot_add_perp hv] at this
      unfold perturbG
      linarith
  linarith

/-- `|g(x + v) - g(x)| ≤ |v| / tan α` for `v ∈ W = e^⊥`. -/
theorem perturbG_lipschitz_W (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (x : Vec d) {v : Vec d} (hv : vecDot v e = 0) :
    |perturbG e α A (x + v) - perturbG e α A x| ≤ vecEuclideanNorm v / Real.tan α := by
  have h1 := perturbG_aux_W he hα hα2 hε hA x hv
  have hv' : vecDot (-v) e = 0 := by rw [← neg_one_smul ℝ v, vecDot_smul_left, hv, mul_zero]
  have h2 := perturbG_aux_W he hα hα2 hε hA (x + v) hv'
  rw [vecEuclideanNorm_neg, add_neg_cancel_right] at h2
  rw [abs_le]; constructor <;> linarith

end AFree
