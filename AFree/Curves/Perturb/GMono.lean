module

public import AFree.Curves.Perturb.GDef

/-!
# The function `g`: bounds and monotonicity in the direction `e`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace AFree

open PDE AFree.Curves

variable {d : ℕ} {e : Vec d} {α : ℝ} {A : Set (Vec d)} {ε : ℝ}

/-- `0 ≤ g ≤ ε` (under the smallness hypothesis). -/
theorem perturbG_bounds (he : vecEuclideanNorm e = 1) {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (x : Vec d) : 0 ≤ perturbG e α A x ∧ perturbG e α A x ≤ ε := by
  have htan : 0 ≤ Real.tan α := (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le
  refine ⟨le_csSup (perturbVals_bddAbove hε hA x) (perturbVals_nonempty he htan A x),
    csSup_le ⟨0, perturbVals_nonempty he htan A x⟩ ?_⟩
  rintro r ⟨a, b, η, hab, hxb, hη, -, rfl⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hA a b η hη)
  rw [ENNReal.toReal_ofReal hε] at this
  linarith

private lemma perturbMeas_mono_agree {a b b' : ℝ} {η η' : ℝ → Vec d} (hbb : b ≤ b')
    (h : ∀ u ∈ Icc a b, η u = η' u) :
    perturbMeas e A a b η ≤ perturbMeas e A a b' η' := by
  refine measure_mono fun u ⟨hu, hP⟩ => ⟨⟨hu.1, hu.2.trans hbb⟩, ?_⟩
  have : graphCurve e η u = graphCurve e η' u := by simp [graphCurve, h u hu]
  simpa [this] using hP

private lemma perturbG_aux_ge (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (x : Vec d) {s : ℝ} (hs : 0 ≤ s) {r : ℝ} (hr : r ∈ perturbVals e α A x) :
    r ≤ perturbG e α A (x + s • e) ∧
      ((∀ σ ∈ Icc 0 s, x + σ • e ∈ A) → r + s ≤ perturbG e α A (x + s • e)) := by
  have htan : 0 ≤ Real.tan α := (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le
  have hbdd := perturbVals_bddAbove hε hA (x + s • e)
  obtain ⟨a, b, η, hab, hxb, hη, hηb, rfl⟩ := hr
  unfold perturbG
  by_cases hb : vecDot x e + s ≤ b
  · have hmem : (perturbMeas e A a b η).toReal - (b - vecDot x e) + s ∈
        perturbVals e α A (x + s • e) :=
      ⟨a, b, η, hab, by rw [perturb_dot_add_smul he]; exact hb, hη,
        by rw [perturb_wPart_add_smul he]; exact hηb, by rw [perturb_dot_add_smul he]; ring⟩
    have := le_csSup hbdd hmem
    exact ⟨by linarith, fun _ => this⟩
  · push Not at hb
    set b' := vecDot x e + s with hb'
    have hbb' : b ≤ b' := hb.le
    have hconst : IsConeGraphFn e α b b' (fun _ => η b) :=
      isConeGraphFn_const htan _ _ (hη.1 b ⟨hab, le_rfl⟩)
    have hext := IsConeGraphFn.extend hη hconst rfl
    have hmem : (perturbMeas e A a b' (fun u => if u ≤ b then η u else η b)).toReal -
        (b' - vecDot x e - s) ∈ perturbVals e α A (x + s • e) := by
      refine ⟨a, b', _, hab.trans hbb', by rw [perturb_dot_add_smul he], hext, ?_, ?_⟩
      · rw [perturb_wPart_add_smul he]; simpa [not_le.mpr hb] using hηb
      · rw [perturb_dot_add_smul he]; ring
    have hmeas : perturbMeas e A a b η ≤
        perturbMeas e A a b' (fun u => if u ≤ b then η u else η b) :=
      perturbMeas_mono_agree hbb' fun u hu => by simp [hu.2]
    have hfin := (perturbMeas_lt_top e A a b' (fun u => if u ≤ b then η u else η b)).ne
    have h1 := ENNReal.toReal_mono hfin hmeas
    refine ⟨?_, fun hseg => ?_⟩
    · have := le_csSup hbdd hmem
      have h2 : b' - vecDot x e - s = 0 := by rw [hb']; ring
      rw [h2] at this
      linarith
    · -- the segment lies in `A`
      set η' : ℝ → Vec d := fun u => if u ≤ b then η u else η b with hη'
      have hsub : (Icc a b ∩ {u | graphCurve e η u ∈ A}) ∪ Ioc b b' ⊆
          Icc a b' ∩ {u | graphCurve e η' u ∈ A} := by
        rintro u (⟨hu, hP⟩ | ⟨hu1, hu2⟩)
        · refine ⟨⟨hu.1, hu.2.trans hbb'⟩, ?_⟩
          have : graphCurve e η' u = graphCurve e η u := by simp [graphCurve, hη', hu.2]
          simpa [this] using hP
        · have hσ : u - vecDot x e ∈ Icc 0 s := ⟨by linarith [hxb, hu1], by rw [hb'] at hu2; linarith⟩
          refine ⟨⟨by linarith [hu1], hu2⟩, ?_⟩
          have hηu : η' u = x - vecDot x e • e := by
            simpa [hη', not_le.mpr hu1] using hηb
          have : graphCurve e η' u = x + (u - vecDot x e) • e := by
            rw [graphCurve, hηu, sub_smul]; abel
          show graphCurve e η' u ∈ A
          rw [this]; exact hseg _ hσ
      have hvol : volume ((Icc a b ∩ {u | graphCurve e η u ∈ A}) ∪ Ioc b b') =
          perturbMeas e A a b η + ENNReal.ofReal (b' - b) := by
        rw [measure_union _ measurableSet_Ioc, Real.volume_Ioc]; rfl
        rw [disjoint_left]
        rintro u ⟨hu, -⟩ hu'
        linarith [hu.2, hu'.1]
      have h3 := measure_mono (μ := volume) hsub
      rw [hvol] at h3
      have h4 := ENNReal.toReal_mono hfin h3
      rw [ENNReal.toReal_add (perturbMeas_lt_top e A a b η).ne ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith)] at h4
      have := le_csSup hbdd hmem
      have h2 : b' - vecDot x e - s = 0 := by rw [hb']; ring
      rw [h2] at this
      linarith

/-- `g(x) ≤ g(x + s e) ≤ g(x) + s` for `s ≥ 0`, with equality
`g(x + s e) = g(x) + s` if the segment `[x, x + s e]` lies in `A`. -/
theorem perturbG_monotone (he : vecEuclideanNorm e = 1) (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (hε : 0 ≤ ε)
    (hA : ∀ a b η, IsConeGraphFn e α a b η → perturbMeas e A a b η ≤ ENNReal.ofReal ε)
    (x : Vec d) {s : ℝ} (hs : 0 ≤ s) :
    perturbG e α A x ≤ perturbG e α A (x + s • e) ∧
      perturbG e α A (x + s • e) ≤ perturbG e α A x + s ∧
      ((∀ σ ∈ Icc 0 s, x + σ • e ∈ A) →
        perturbG e α A (x + s • e) = perturbG e α A x + s) := by
  have htan : 0 ≤ Real.tan α := (Real.tan_pos_of_pos_of_lt_pi_div_two hα hα2).le
  have hne : (perturbVals e α A x).Nonempty := ⟨0, perturbVals_nonempty he htan A x⟩
  have hbdd := perturbVals_bddAbove hε hA x
  have hup : perturbG e α A (x + s • e) ≤ perturbG e α A x + s := by
    refine csSup_le ⟨0, perturbVals_nonempty he htan A _⟩ ?_
    rintro r ⟨a, b, η, hab, hxb, hη, hηb, rfl⟩
    rw [perturb_dot_add_smul he] at hxb ⊢
    rw [perturb_wPart_add_smul he] at hηb
    have hmem : (perturbMeas e A a b η).toReal - (b - vecDot x e) ∈ perturbVals e α A x :=
      ⟨a, b, η, hab, by linarith, hη, hηb, rfl⟩
    have := le_csSup hbdd hmem
    unfold perturbG
    linarith
  refine ⟨csSup_le hne fun r hr => (perturbG_aux_ge he hα hα2 hε hA x hs hr).1, hup,
    fun hseg => le_antisymm hup ?_⟩
  have : perturbG e α A x ≤ perturbG e α A (x + s • e) - s :=
    csSup_le hne fun r hr => by linarith [(perturbG_aux_ge he hα hα2 hε hA x hs hr).2 hseg]
  linarith

end AFree
