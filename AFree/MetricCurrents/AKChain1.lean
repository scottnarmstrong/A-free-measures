module

public import AFree.MetricCurrents.AKTaylor
public import AFree.MetricCurrents.AKChainAux

/-!
# The one-slot chain rule [AK, (3.3)]
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree

open PDE AKChainAux

/-- Slot scaling by a constant: `T(f, π[i ↦ c π_i]) = c T(f, π)` (linearity of `IsMetricCurrent` in slot `i`, with `b = 0`). -/
private lemma T_update_scale {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f) {τ : Fin k → Vec d → ℝ}
    (hτ : IsLipTuple τ) (j : Fin k) (c : ℝ) :
    T f (Function.update τ j (fun x => c * τ j x)) = c * T f τ := by
  have key := hT.2.2.2.1 f hf τ hτ j (τ j) (hτ j) c 0
  simp only [zero_smul, add_zero, zero_mul] at key
  have e : (c • τ j) = fun x => c * τ j x := by funext x; simp
  rw [e] at key
  exact key

private lemma T_diag_scale {d k : ℕ} {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) {f : Vec d → ℝ} (hf : IsBddLipFun f) {π : Fin k → Vec d → ℝ}
    (hπ : IsLipTuple π) (a : Fin k → ℝ) (s : Finset (Fin k)) :
    T f (fun l x => if l ∈ s then a l * π l x else π l x) = (∏ l ∈ s, a l) * T f π := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hτ : IsLipTuple (fun l x => if l ∈ s then a l * π l x else π l x) := by
      intro l
      by_cases h : l ∈ s
      · simpa [h] using isLipFun_const_mul (a l) (hπ l)
      · simpa [h] using hπ l
    have e : (fun l x => if l ∈ insert j s then a l * π l x else π l x) =
        Function.update (fun l x => if l ∈ s then a l * π l x else π l x) j
          (fun x => a j * (if j ∈ s then a j * π j x else π j x)) := by
      funext l x
      by_cases hl : l = j
      · subst hl; simp [hj]
      · simp [hl]
    rw [e, show (fun x => a j * (if j ∈ s then a j * π j x else π j x)) =
      fun x => a j * (fun l x => if l ∈ s then a l * π l x else π l x) j x from rfl,
      T_update_scale hT hf hτ j (a j), ih, Finset.prod_insert hj]
    ring

/-- [AK, (3.3)] For `k ≥ 1`, `i`, `φ ∈ C¹(ℝ)` with `|φ'| ≤ M₀`, `π ∈ Lip^k`,
`h ∈ B^∞`: `π[i ↦ φ ∘ π_i] ∈ Lip^k` and `T(h, π[i ↦ φ ∘ π_i]) = T(h φ'(π_i), π)`. -/
theorem akchain1 {d k : ℕ} (hk : 1 ≤ k) {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}
    (hT : IsMetricCurrent k T) (i : Fin k) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hM : ∃ M : ℝ, ∀ s, |deriv φ s| ≤ M) {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    IsLipTuple (Function.update π i (fun x => φ (π i x))) ∧
      akExt T h (Function.update π i (fun x => φ (π i x))) =
        akExt T (fun x => h x * deriv φ (π i x)) π := by
  classical
  refine ⟨isLipTuple_update hπ (isLipFun_comp_real hφ hM (hπ i)) i, ?_⟩
  obtain ⟨M, hM'⟩ := hM
  let c : Fin k → Vec k → ℝ := fun l y => if l = i then deriv φ (y i) else 1
  let ψ : Fin k → Vec k → ℝ := fun l y => if l = i then φ (y i) else y l
  have hder : ∀ l y, HasFDerivAt (ψ l)
      (c l y • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l) y := by
    intro l y
    by_cases hl : l = i
    · subst hl
      have e : ψ l = fun y => φ (y l) := by funext y; simp [ψ]
      rw [e]
      have h2 : HasFDerivAt (fun y : Vec k => y l) (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin k => ℝ) l) y := hasFDerivAt_apply l y
      have := ((hφ.differentiable one_ne_zero (y l)).hasDerivAt).comp_hasFDerivAt y h2
      rw [show c l y = deriv φ (y l) by simp [c]]
      exact this
    · have e : ψ l = fun y => y l := by funext y; simp [ψ, hl]
      rw [e]
      simpa [c, hl] using hasFDerivAt_apply l y
  have hψ : ∀ l, ContDiff ℝ 1 (ψ l) := by
    intro l
    by_cases hl : l = i
    · subst hl
      have e : ψ l = fun y => φ (y l) := by funext y; simp [ψ]
      rw [e]
      exact hφ.comp (contDiff_apply ℝ ℝ l)
    · have e : ψ l = fun y => y l := by funext y; simp [ψ, hl]
      rw [e]
      exact contDiff_apply ℝ ℝ l
  have hbd : ∀ l y, ‖fderiv ℝ (ψ l) y‖ ≤ max 1 M := by
    intro l y
    rw [(hder l y).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _)) fun v => ?_
    have h1 : |c l y| ≤ max 1 M := by
      by_cases hl : l = i
      · simp only [c, hl, ite_true]; exact (hM' _).trans (le_max_right _ _)
      · simp [c, hl]
    have h2 : |v l| ≤ ‖v‖ := by simpa using norm_le_pi_norm v l
    simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hjac : ∀ y, jacMat ψ y = Matrix.diagonal (c · y) := by
    intro y
    ext a b
    simp [jacMat, (hder a y).fderiv, Matrix.diagonal_apply, Pi.single_apply]
  have hlin : ∀ f, IsBddLipFun f → ∀ A ∈ {A : Matrix (Fin k) (Fin k) ℝ |
      ∃ a : Fin k → ℝ, A = Matrix.diagonal a}, T f (matAct A π) = A.det * T f π := by
    rintro f hf A ⟨a, rfl⟩
    have := T_diag_scale hT hf hπ a Finset.univ
    simp only [Finset.mem_univ, ite_true] at this
    rw [Matrix.det_diagonal, ← this]
    congr 1
    funext l x
    simp [matAct, Matrix.diagonal_apply]
  have key := aktaylor hk hT hπ hψ ⟨max 1 M, hbd⟩ {A | ∃ a : Fin k → ℝ, A = Matrix.diagonal a}
    (fun y => ⟨_, hjac y⟩) hlin hh
  have e1 : (fun l x => ψ l (evalTuple π x)) =
      Function.update π i (fun x => φ (π i x)) := by
    funext l x
    by_cases hl : l = i
    · subst hl; simp [ψ, evalTuple]
    · simp [ψ, evalTuple, hl]
  have e2 : (fun x => h x * jacDet ψ (evalTuple π x)) = fun x => h x * deriv φ (π i x) := by
    funext x
    simp [jacDet, hjac, Matrix.det_diagonal, c, evalTuple]
  rw [e1, e2] at key
  exact key

end AFree
