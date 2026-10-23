module

public import AFree.Paper.Counterexample.Props
public import AFree.Algebra.KVec.Plucker

/-!
# Remark 1.11: the counterexample in `ℝ⁵`

[DPR, Remark 1.11]: a locally normal `2`-current in `ℝ⁵`, `T = (e₀∧e₁ + e₂∧e₃) ℋ⁴ ⌞ {x₄ = 0}`, whose orienting
`2`-vector is not simple, showing that the simplicity statement for `(d-2)`-currents fails for
`1 < k < d - 2`.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

theorem sum_pluckerP0_sq : ∑ I : KIdx 5 2, pluckerP0 I * pluckerP0 I = 1 := by
  have h : ∀ I : KIdx 5 2, pluckerP0 I * pluckerP0 I
      = if I.1 = {0, 1} ∨ I.1 = {2, 3} then (1 / 2 : ℝ) else 0 := by
    intro I
    unfold pluckerP0
    split_ifs
    · rw [← sq, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
    · simp
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hc : (Finset.univ.filter fun I : KIdx 5 2 => I.1 = {0, 1} ∨ I.1 = {2, 3}).card = 2 := by
    decide +kernel
  rw [hc]; norm_num

/-- Local finiteness, Borel measurability and unit norm. -/
theorem counterex_locnormal_clauses :
    IsLocallyFiniteMeasure ceTau ∧ Measurable (fun _ : Vec 5 => pluckerP0) ∧
      ∀ᵐ x ∂ceTau, piEuclideanNorm ((fun _ : Vec 5 => pluckerP0) x) = 1 := by
  refine ⟨ceTau_basic.1, measurable_const, Filter.Eventually.of_forall fun x => ?_⟩
  simp only [piEuclideanNorm, sum_pluckerP0_sq, Real.sqrt_one]

/-- The boundary identity with `τ' = 0`, `P' = 0`. -/
theorem counterex_boundary_clause :
    ∃ (τ' : Measure (Vec 5)) (P' : Vec 5 → KVec 5 (2 - 1)), IsLocallyFiniteMeasure τ' ∧
      Measurable P' ∧ LocallyIntegrable P' τ' ∧
      ∀ φ : Vec 5 → ℝ, IsTestFunctionOn Set.univ φ → ∀ J : KIdx 5 (2 - 1),
        ∫ x, φ x * P' x J ∂τ' = ∑ j ∈ Finset.univ.filter (· ∉ J.1),
          if h : (insert j J.1).card = 2 then
            insertSign j J.1 * ∫ x, euclideanCoordDeriv j φ x *
              (fun _ : Vec 5 => pluckerP0) x ⟨insert j J.1, h⟩ ∂ceTau else 0 := by
  refine ⟨0, fun _ _ => 0, inferInstance, measurable_const, fun _ => ⟨Set.univ, Filter.univ_mem, by simp [IntegrableOn]⟩, ?_⟩
  intro φ hφ J
  symm
  refine (Finset.sum_eq_zero fun j _ => ?_).trans (by simp)
  split_ifs with h
  · by_cases h0 : pluckerP0 ⟨insert j J.1, h⟩ = 0
    · simp [h0]
    · have hI : insert j J.1 = {0, 1} ∨ insert j J.1 = {2, 3} := by
        by_contra hn; exact h0 (by simp [pluckerP0, hn])
      have hj : j.1 < 4 := by
        have hm : j ∈ insert j J.1 := Finset.mem_insert_self _ _
        rcases hI with e | e <;> rw [e] at hm <;> simp at hm <;> rcases hm with rfl | rfl <;> decide
      have := integral_coordDeriv_ceTau hφ.1 hφ.2.1 ⟨j.1, hj⟩
      have hj' : Fin.castSucc (⟨j.1, hj⟩ : Fin 4) = j := Fin.ext rfl
      rw [hj'] at this
      simp only [integral_mul_const, this, zero_mul, mul_zero]
  · rfl

/-- `P₀` is not simple `τˢ`-a.e. -/
theorem counterex_not_ae_simple :
    ¬ ∀ᵐ x ∂ceTau.singularPart volume, IsSimpleKVec ((fun _ : Vec 5 => pluckerP0) x) := by
  rw [ceTau_basic.2.2.2.2]
  intro h
  have : (MeasureTheory.ae ceTau).NeBot := ae_neBot.2 ceTau_ne_zero
  exact pluckerP0_not_isSimpleKVec (Filter.eventually_const.1 h)

/-- [DPR, Remark 1.11]: the counterexample in `ℝ⁵`. -/
theorem counterex :
    ∃ P : Vec 5 → KVec 5 2,
      (∀ x, P x = fun I => if I.1 = {0, 1} ∨ I.1 = {2, 3} then (Real.sqrt 2)⁻¹ else 0) ∧
      IsLocNormalCurrent ceTau P ∧
      ¬ ∀ᵐ x ∂ceTau.singularPart volume, IsSimpleKVec (P x) :=
  ⟨fun _ => pluckerP0, fun _ => rfl,
    ⟨counterex_locnormal_clauses.1, counterex_locnormal_clauses.2.1,
      counterex_locnormal_clauses.2.2, counterex_boundary_clause⟩, counterex_not_ae_simple⟩

end AFree
