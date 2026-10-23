module

public import AFree.Rademacher.Chain.PertSetup

/-!
# Steps 1 and 2 of the single-stage perturbation: shrinking and the pieces `E'_k`

Steps 1 and 2 of the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AFree.Rademacher

variable {d : ℕ}

/-- Step 1: for `f ∈ X₀`, `ε > 0` there is `s ∈ (0, 1/2]` such that
`f' = (1 - s) f ∈ X₀`, `‖f' - f‖_sup ≤ ε` and `|D_j f'| ≤ 1 - s`. -/
theorem pert_shrinking {e : Vec d → Fin d → Vec d} {f : Vec d → ℝ} (hf : f ∈ X0 e) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ (fun x => (1 - s) * f x) ∈ X0 e ∧
      (∀ x, |(1 - s) * f x - f x| ≤ ε) ∧
      ∀ x j, |fderiv ℝ (fun y => (1 - s) * f y) x (e x j)| ≤ 1 - s := by
  obtain ⟨hsm, ⟨C, hC⟩, hD⟩ := X0_iff_fderiv.1 hf
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  set s := min (1 / 2) (ε / (2 * (1 + max C 0))) with hs
  have hspos : 0 < s := lt_min (by norm_num) (by positivity)
  have hs2 : s ≤ 1 / 2 := min_le_left _ _
  have hsε : s * max C 0 ≤ ε := by
    have h1 : s ≤ ε / (2 * (1 + max C 0)) := min_le_right _ _
    have h2 : s * (2 * (1 + max C 0)) ≤ ε := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hdf : ∀ x, DifferentiableAt ℝ f x := fun x => hsm.differentiable (by simp) x
  have hder : ∀ x j, |fderiv ℝ (fun y => (1 - s) * f y) x (e x j)| ≤ 1 - s := by
    intro x j
    rw [fderiv_const_mul (hdf x)]
    simp only [smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    calc (1 - s) * |fderiv ℝ f x (e x j)| ≤ (1 - s) * 1 :=
          mul_le_mul_of_nonneg_left (hD x j) (by linarith)
      _ = 1 - s := mul_one _
  refine ⟨s, hspos, hs2, ?_, fun x => ?_, hder⟩
  · rw [X0_iff_fderiv]
    refine ⟨contDiff_const.mul hsm, ⟨C, fun x => ?_⟩, fun x j => (hder x j).trans (by linarith)⟩
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    calc (1 - s) * |f x| ≤ 1 * C := by
          have := hC x
          have h1 : 0 ≤ |f x| := abs_nonneg _
          nlinarith
      _ = C := one_mul _
  · have : (1 - s) * f x - f x = -(s * f x) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos hspos]
    calc s * |f x| ≤ s * max C 0 :=
          mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) hspos.le
      _ ≤ ε := hsε

/-- Step 2: for measurable `E' ⊆ E` there is `k < m` with `E'_k`
measurable and `μ E' ≤ m μ(E'_k)`, where `E'_k = {x ∈ E' : |v · e_k(x)| ≥ δ/√m}`. -/
theorem pert_pieces {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)} {i : Fin d}
    {m : ℕ} {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (hS : Setting μ V i m δ E e) {E' : Set (Vec d)} (hEE : E' ⊆ E) (hE' : MeasurableSet E') :
    ∃ k : Fin d, (k : ℕ) < m ∧
      MeasurableSet {x ∈ E' | δ / Real.sqrt m ≤ |vecDot (basisVec i) (e x k)|} ∧
      μ E' ≤ (m : ℝ≥0∞) * μ {x ∈ E' | δ / Real.sqrt m ≤ |vecDot (basisVec i) (e x k)|} := by
  set F : Finset (Fin d) := Finset.univ.filter fun k : Fin d => (k : ℕ) < m with hF
  set q := δ / Real.sqrt m with hq
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hS.m_pos
  have hqpos : 0 < q := by have := hS.delta_pos; positivity
  have hcard : F.card ≤ m := by
    have : F.card ≤ (Finset.range m).card :=
      Finset.card_le_card_of_injOn (fun k : Fin d => (k : ℕ))
        (fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2)
        (fun a _ b _ h => Fin.ext h)
    simpa using this
  have hFne : F.Nonempty := ⟨⟨0, Nat.lt_of_lt_of_le hS.m_pos hS.m_le⟩, by
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]; exact hS.m_pos⟩
  set A : Fin d → Set (Vec d) := fun k => {x ∈ E' | q ≤ |vecDot (basisVec i) (e x k)|} with hA
  have hAm : ∀ k, MeasurableSet (A k) := by
    intro k
    show MeasurableSet (E' ∩ {x | q ≤ |vecDot (basisVec i) (e x k)|})
    refine hE'.inter (measurableSet_le measurable_const ?_)
    have hc : Continuous fun x => vecDot (basisVec i) (e x k) :=
      continuous_vecDot.comp (continuous_const.prodMk ((continuous_apply k).comp hS.frame.1))
    exact hc.abs.measurable
  have hcover : E' ⊆ ⋃ k ∈ F, A k := by
    intro x hx
    by_contra hnot
    simp only [mem_iUnion, not_exists] at hnot
    have hlt : ∀ k ∈ F, vecDot (basisVec i) (e x k) ^ 2 < q ^ 2 := by
      intro k hk
      have := hnot k hk
      have hlt' : |vecDot (basisVec i) (e x k)| < q := by
        by_contra hge
        exact this ⟨hx, not_lt.1 hge⟩
      exact sq_lt_sq' (by linarith [abs_lt.1 hlt']) (abs_lt.1 hlt').2
    have hsum := Finset.sum_lt_sum_of_nonempty hFne hlt
    have h1 := hS.sum_sq x (hEE hx)
    have h2 : (F.card : ℝ) * q ^ 2 ≤ m * q ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    have h3 : (m : ℝ) * q ^ 2 = δ ^ 2 := by
      rw [hq, div_pow, Real.sq_sqrt hm0.le]; field_simp
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    linarith
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image F (fun k => μ (A k)) hFne
  refine ⟨k₀, (Finset.mem_filter.1 hk₀).2, hAm k₀, ?_⟩
  calc μ E' ≤ μ (⋃ k ∈ F, A k) := measure_mono hcover
    _ ≤ ∑ k ∈ F, μ (A k) := measure_biUnion_finset_le _ _
    _ ≤ F.card • μ (A k₀) := Finset.sum_le_card_nsmul _ _ _ hmax
    _ ≤ m • μ (A k₀) := by gcongr
    _ = (m : ℝ≥0∞) * μ (A k₀) := nsmul_eq_mul _ _

/-- A positive number below finitely many positive numbers and below a given one. -/
theorem exists_pos_le_finset (T : Finset (Vec d)) (φ : Vec d → ℝ) (hφ : ∀ p ∈ T, 0 < φ p)
    {a : ℝ} (ha : 0 < a) : ∃ c : ℝ, 0 < c ∧ c ≤ a ∧ ∀ p ∈ T, c ≤ φ p := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨a, ha, le_rfl, by simp⟩
  | insert p T hp ih =>
    obtain ⟨c, hc, hca, hcT⟩ := ih fun q hq => hφ q (Finset.mem_insert_of_mem hq)
    refine ⟨min c (φ p), lt_min hc (hφ p (Finset.mem_insert_self _ _)),
      (min_le_left _ _).trans hca, fun q hq => ?_⟩
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcT q hq)

end AFree.Rademacher
