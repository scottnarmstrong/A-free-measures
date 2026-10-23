module

public import AFree.Rademacher.Frame
public import AFree.Rademacher.Setting
public import Mathlib.LinearAlgebra.Trace

/-!
# Non-differentiability: the choice of `v, δ, m, G`

Step 1 of the proof of non-differentiability (off the bundle), following [AM, Section 4].
-/

@[expose] public section

open PDE MeasureTheory Set Matrix
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- For an idempotent matrix, the rank is the trace. -/
theorem rank_cast_eq_trace (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q * Q = Q) :
    ((Q.rank : ℕ) : ℝ) = Q.trace := by
  have hid : IsIdempotentElem (Matrix.toLin' Q) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQ]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [Matrix.trace_toLin'_eq] at h
  rw [h]
  rfl

theorem measurable_trace_one_sub {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hP : ∀ i j, Measurable fun x => P x i j) :
    Measurable fun x => (1 - P x).trace := by
  unfold Matrix.trace Matrix.diag
  refine Finset.measurable_sum _ fun i _ => ?_
  simp only [Matrix.sub_apply]
  exact measurable_const.sub (hP i i)

theorem measurableSet_rank_eq {V : Vec d → Submodule ℝ (Vec d)} {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hP : IsBorelProj V P) (m : ℕ) : MeasurableSet {x | (1 - P x).rank = m} := by
  have hidem : ∀ x, (1 - P x) * (1 - P x) = 1 - P x := by
    intro x
    have := (hP.2 x).2.1
    simp only [mul_sub, sub_mul, one_mul, mul_one, this]
    abel
  have : {x | (1 - P x).rank = m} = {x | (1 - P x).trace = (m : ℝ)} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [← rank_cast_eq_trace _ (hidem x)]
    exact_mod_cast Iff.rfl
  rw [this]
  exact measurableSet_eq_fun (measurable_trace_one_sub hP.1) measurable_const

theorem measurable_one_sub_mulVec_basis {V : Vec d → Submodule ℝ (Vec d)}
    {P : Vec d → Matrix (Fin d) (Fin d) ℝ} (hP : IsBorelProj V P) (i : Fin d) :
    Measurable fun x => vecEuclideanNorm ((1 - P x) *ᵥ basisVec i) := by
  have : Measurable fun x => (1 - P x) *ᵥ basisVec i := by
    refine measurable_pi_iff.2 fun a => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
    refine Finset.measurable_sum _ fun b _ => ?_
    exact (measurable_const.sub (hP.1 a b)).mul measurable_const
  exact continuous_vecEuclideanNorm.measurable.comp this

/-- `V x ≠ ⊤` forces `(1 - P x) ε_i ≠ 0` for some `i`. -/
theorem exists_basis_ne {V : Vec d → Submodule ℝ (Vec d)} {P : Vec d → Matrix (Fin d) (Fin d) ℝ}
    (hP : IsBorelProj V P) {x : Vec d} (hx : V x ≠ ⊤) : ∃ i, (1 - P x) *ᵥ basisVec i ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hx
  rw [eq_top_iff]
  intro u _
  have hb : ∀ i, basisVec i ∈ V x := by
    intro i
    have h1 := hall i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
    rw [← (hP.2 x).2.2]
    exact ⟨basisVec i, by simpa [Matrix.toLin'_apply] using h1.symm⟩
  rw [← sum_smul_basisVec u]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)

/-- Step 1: choice of a coordinate direction `v`, a threshold `δ`, a rank `m` and a Borel set `G`. -/
theorem nondiff_choice {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)}
    {P : Vec d → Matrix (Fin d) (Fin d) ℝ} (hP : IsBorelProj V P)
    (hpos : 0 < μ {x | V x ≠ ⊤}) :
    ∃ (i : Fin d) (m : ℕ) (δ : ℝ) (G : Set (Vec d)), 1 ≤ m ∧ m ≤ d ∧ 0 < δ ∧ MeasurableSet G ∧
      0 < μ G ∧ (∀ x ∈ G, (1 - P x).rank = m) ∧
      ∀ x ∈ G, δ ≤ vecEuclideanNorm ((1 - P x) *ᵥ basisVec i) := by
  -- the index `i`
  have hcov : {x | V x ≠ ⊤} ⊆ ⋃ i : Fin d, {x | 0 < vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)} := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_basis_ne hP hx
    exact mem_iUnion.2 ⟨i, vecEuclideanNorm_pos_iff.2 hi⟩
  have hex1 : ∃ i : Fin d, 0 < μ {x | 0 < vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)} := by
    by_contra hno
    push Not at hno
    have : μ (⋃ i : Fin d, {x | 0 < vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)}) = 0 :=
      measure_iUnion_null fun i => le_antisymm (hno i) bot_le
    exact hpos.ne' (measure_mono_null hcov this)
  obtain ⟨i, hi⟩ := hex1
  -- the threshold `δ`
  have hcov2 : {x | 0 < vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)} ⊆
      ⋃ n : ℕ, {x | 1 / ((n : ℝ) + 1) ≤ vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)} := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < vecEuclideanNorm ((1 - P x) *ᵥ basisVec i) from hx)
    exact mem_iUnion.2 ⟨n, hn.le⟩
  have hex2 : ∃ n : ℕ, 0 < μ {x | 1 / ((n : ℝ) + 1) ≤ vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)} := by
    by_contra hno
    push Not at hno
    have : μ (⋃ n : ℕ, {x | 1 / ((n : ℝ) + 1) ≤ vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)}) = 0 :=
      measure_iUnion_null fun n => le_antisymm (hno n) bot_le
    exact hi.ne' (measure_mono_null hcov2 this)
  obtain ⟨n, hn⟩ := hex2
  set G' : Set (Vec d) := {x | 1 / ((n : ℝ) + 1) ≤ vecEuclideanNorm ((1 - P x) *ᵥ basisVec i)} with hG'
  have hG'm : MeasurableSet G' :=
    measurableSet_le measurable_const (measurable_one_sub_mulVec_basis hP i)
  -- the rank `m`
  have hcov3 : G' ⊆ ⋃ m ∈ Finset.range (d + 1), (G' ∩ {x | (1 - P x).rank = m}) := by
    intro x hx
    have hr : (1 - P x).rank ≤ d := by
      refine (Matrix.rank_le_card_width _).trans (by simp)
    exact mem_iUnion₂.2 ⟨(1 - P x).rank, Finset.mem_range.2 (Nat.lt_succ_of_le hr), hx, rfl⟩
  have hex3 : ∃ m ∈ Finset.range (d + 1), 0 < μ (G' ∩ {x | (1 - P x).rank = m}) := by
    by_contra hno
    push Not at hno
    have : μ (⋃ m ∈ Finset.range (d + 1), (G' ∩ {x | (1 - P x).rank = m})) = 0 :=
      (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun m hm =>
        le_antisymm (hno m hm) bot_le
    exact hn.ne' (measure_mono_null hcov3 this)
  obtain ⟨m, hm, hμm⟩ := hex3
  have hmd : m ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hne : (G' ∩ {x | (1 - P x).rank = m}).Nonempty := nonempty_of_measure_ne_zero hμm.ne'
  obtain ⟨x0, hx0, hx0r⟩ := hne
  have hm1 : 1 ≤ m := by
    rw [← hx0r]
    have hnz : (1 - P x0) *ᵥ basisVec i ≠ 0 := by
      intro h
      have hx0' : (1 : ℝ) / ((n : ℝ) + 1) ≤ vecEuclideanNorm ((1 - P x0) *ᵥ basisVec i) := hx0
      rw [h, vecEuclideanNorm_eq_zero_iff.2 rfl] at hx0'
      linarith
    have hmem : (1 - P x0) *ᵥ basisVec i ∈ LinearMap.range (1 - P x0).mulVecLin :=
      ⟨basisVec i, rfl⟩
    rw [Matrix.rank]
    exact Submodule.one_le_finrank_iff.2 fun hbot => hnz (by
      have := hbot ▸ hmem
      simpa using this)
  exact ⟨i, m, 1 / ((n : ℝ) + 1), G' ∩ {x | (1 - P x).rank = m}, hm1, hmd, hδ,
    hG'm.inter (measurableSet_rank_eq hP m), hμm, fun x hx => hx.2, fun x hx => hx.1⟩

end AFree.Rademacher
