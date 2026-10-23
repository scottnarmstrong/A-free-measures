module

public import AFree.Curves.Dichotomy.CurveMeasLambda

/-!
# Concatenating partitions (the `≤` half of the length formula)

`Λ_γ(U; [0,p]) + Var(γ; [p,q]) ≤ Λ_γ(U; [0,q])` when `γ([p,q]) ⊆ U`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace AFree

open PDE

variable {d : ℕ}

lemma curveLambda_mono_set (γ : C(I, Vec d)) (U : Set (Vec d)) {s t : Set ℝ} (h : s ⊆ t) :
    curveLambda γ U s ≤ curveLambda γ U t :=
  iSup_le fun ⟨n, u, hum, hu⟩ =>
    le_iSup (fun p : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ t } =>
      ∑ i ∈ Finset.range p.1, curveGap γ U (p.2.1 i) (p.2.1 (i + 1)))
      ⟨n, u, hum, fun i => h (hu i)⟩

lemma curveGap_of_subset {γ : C(I, Vec d)} {U : Set (Vec d)} {a b : ℝ}
    (h : ccurveExt γ '' Icc a b ⊆ U) :
    curveGap γ U a b = ENNReal.ofReal (vecEuclideanNorm (ccurveExt γ b - ccurveExt γ a)) := by
  unfold curveGap
  simp only [h, ↓reduceIte]

/-- Concatenation of a partition of `[0,p]` with a partition of the cell `[p,q] ` mapped into `U`. -/
theorem curveLambda_add_variation_le (γ : C(I, Vec d)) (U : Set (Vec d)) {p q : ℝ} (hp0 : 0 ≤ p)
    (hpq : p ≤ q) (hU : ccurveExt γ '' Icc p q ⊆ U) :
    curveLambda γ U (Icc 0 p) + euclideanCurveVariation (ccurveExt γ) (Icc p q) ≤
      curveLambda γ U (Icc 0 q) := by
  unfold curveLambda euclideanCurveVariation
  have : Nonempty (ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 p }) :=
    ⟨(0, ⟨fun _ => 0, monotone_const, fun _ => ⟨le_rfl, hp0⟩⟩)⟩
  have : Nonempty (ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc p q }) :=
    ⟨(0, ⟨fun _ => p, monotone_const, fun _ => ⟨le_rfl, hpq⟩⟩)⟩
  refine ENNReal.iSup_add_iSup_le fun ⟨n, u, hum, hu⟩ ⟨m, v, hvm, hv⟩ => ?_
  classical
  set w : ℕ → ℝ := fun i => if i ≤ n then u i else v (i - (n + 1)) with hwdef
  have hw1 : ∀ i, i ≤ n → w i = u i := fun i hi => by simp [hwdef, hi]
  have hw2 : ∀ x, w (n + 1 + x) = v x := fun x => by
    simp [hwdef, show ¬ (n + 1 + x ≤ n) by omega]
  have hwm : Monotone w := by
    refine monotone_nat_of_le_succ fun i => ?_
    rcases lt_trichotomy i n with h | h | h
    · rw [hw1 i h.le, hw1 (i + 1) h]; exact hum (Nat.le_succ i)
    · subst h
      have := hw2 0
      rw [add_zero] at this
      rw [hw1 i le_rfl, this]
      exact (hu i).2.trans (hv 0).1
    · obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_lt h
      have e1 : n + x + 1 + 1 = n + 1 + (x + 1) := by omega
      have e2 : n + x + 1 = n + 1 + x := by omega
      rw [e1, e2, hw2, hw2]
      exact hvm (Nat.le_succ x)
  have hwmem : ∀ i, w i ∈ Icc 0 q := fun i => by
    by_cases h : i ≤ n
    · rw [hw1 i h]; exact ⟨(hu i).1, (hu i).2.trans hpq⟩
    · have : w i = v (i - (n + 1)) := by simp [hwdef, h]
      rw [this]; exact ⟨hp0.trans (hv _).1, (hv _).2⟩
  refine le_trans ?_ (le_iSup (fun r : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 q } =>
    ∑ i ∈ Finset.range r.1, curveGap γ U (r.2.1 i) (r.2.1 (i + 1)))
    ⟨n + 1 + m, w, hwm, hwmem⟩)
  dsimp only
  rw [Finset.sum_range_add, Finset.sum_range_succ]
  have hA : ∑ i ∈ Finset.range n, curveGap γ U (u i) (u (i + 1)) =
      ∑ i ∈ Finset.range n, curveGap γ U (w i) (w (i + 1)) :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [hw1 i this.le, hw1 (i + 1) this]
  have hB : ∑ x ∈ Finset.range m,
      ENNReal.ofReal (vecEuclideanNorm (ccurveExt γ (v (x + 1)) - ccurveExt γ (v x))) =
      ∑ x ∈ Finset.range m, curveGap γ U (w (n + 1 + x)) (w (n + 1 + x + 1)) :=
    Finset.sum_congr rfl fun x _ => by
      have e : n + 1 + x + 1 = n + 1 + (x + 1) := by omega
      rw [e, hw2, hw2]
      exact (curveGap_of_subset (hU.trans' (image_mono (Icc_subset_Icc (hv x).1 (hv (x + 1)).2)))).symm
  rw [hA, hB]
  exact add_le_add le_self_add le_rfl

end AFree
