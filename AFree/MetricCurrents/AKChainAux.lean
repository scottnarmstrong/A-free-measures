module

public import AFree.MetricCurrents.AKTaylor

/-!
# Helpers for the chain rule files

Lipschitz calculus for `IsLipFun` / `IsEuclLipschitzWith` and slotwise additivity and homogeneity
of the extension `akExt T` (from the extension property (E3) of `IsAKExtension`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.AKChainAux

open PDE AFree

variable {d k : ℕ}

lemma lip_mono {K K' : ℝ≥0} {f : Vec d → ℝ} (h : IsEuclLipschitzWith K f) (hK : K ≤ K') :
    IsEuclLipschitzWith K' f := fun x y =>
  (h x y).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (vecEuclideanNorm_nonneg _))

lemma lip_add {K₁ K₂ : ℝ≥0} {f g : Vec d → ℝ} (h₁ : IsEuclLipschitzWith K₁ f)
    (h₂ : IsEuclLipschitzWith K₂ g) : IsEuclLipschitzWith (K₁ + K₂) (fun x => f x + g x) :=
  fun x y => by
    have a := h₁ x y
    have b := h₂ x y
    calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ _ := by push_cast; linarith

lemma lip_const_mul (c : ℝ) {K : ℝ≥0} {f : Vec d → ℝ} (h : IsEuclLipschitzWith K f) :
    IsEuclLipschitzWith (Real.toNNReal |c| * K) (fun x => c * f x) := fun x y => by
  have a := h x y
  calc |c * f x - c * f y| = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
    _ ≤ |c| * (K * vecEuclideanNorm (x - y)) := mul_le_mul_of_nonneg_left a (abs_nonneg c)
    _ = _ := by rw [NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg c)]; ring

lemma lip_comp {L K : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith L φ) {g : Vec d → ℝ}
    (hg : IsEuclLipschitzWith K g) : IsEuclLipschitzWith (L * K) (fun x => φ (g x)) :=
  fun x y => by
    have a := hg x y
    have b : |φ (g x) - φ (g y)| ≤ L * |g x - g y| := by
      simpa [Real.dist_eq] using hφ.dist_le_mul (g x) (g y)
    calc |φ (g x) - φ (g y)| ≤ L * |g x - g y| := b
      _ ≤ L * (K * vecEuclideanNorm (x - y)) := mul_le_mul_of_nonneg_left a (by positivity)
      _ = _ := by push_cast; ring

lemma isLipFun_zero : IsLipFun (fun _ : Vec d => (0 : ℝ)) :=
  ⟨0, fun x y => by simp⟩

lemma isLipFun_add {f g : Vec d → ℝ} (hf : IsLipFun f) (hg : IsLipFun g) :
    IsLipFun (fun x => f x + g x) := by
  obtain ⟨K₁, h₁⟩ := hf
  obtain ⟨K₂, h₂⟩ := hg
  exact ⟨_, lip_add h₁ h₂⟩

lemma isLipFun_const_mul (c : ℝ) {f : Vec d → ℝ} (hf : IsLipFun f) :
    IsLipFun (fun x => c * f x) := by
  obtain ⟨K, h⟩ := hf
  exact ⟨_, lip_const_mul c h⟩

lemma isLipFun_sum {ι : Type*} (s : Finset ι) (f : ι → Vec d → ℝ) (h : ∀ l ∈ s, IsLipFun (f l)) :
    IsLipFun (fun x => ∑ l ∈ s, f l x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLipFun_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact isLipFun_add (h a (Finset.mem_insert_self _ _))
      (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

lemma lipschitzWith_of_deriv_bdd {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {M : ℝ}
    (hM : ∀ s, |deriv φ s| ≤ M) : LipschitzWith (Real.toNNReal M) φ := by
  refine lipschitzWith_of_nnnorm_deriv_le (hφ.differentiable one_ne_zero) fun s => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ ((abs_nonneg _).trans (hM 0))]
  simpa using hM s

lemma isLipFun_comp_real {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hM : ∃ M : ℝ, ∀ s, |deriv φ s| ≤ M)
    {g : Vec d → ℝ} (hg : IsLipFun g) : IsLipFun (fun x => φ (g x)) := by
  obtain ⟨M, hM⟩ := hM
  obtain ⟨K, hK⟩ := hg
  exact ⟨_, lip_comp (lipschitzWith_of_deriv_bdd hφ hM) hK⟩

lemma isLipTuple_update {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) {ψ : Vec d → ℝ}
    (hψ : IsLipFun ψ) (i : Fin k) : IsLipTuple (Function.update π i ψ) := by
  intro l
  by_cases h : l = i
  · subst h; simpa using hψ
  · simpa [Function.update_of_ne h] using hπ l

lemma isLipTuple_matAct {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π)
    (A : Matrix (Fin k) (Fin k) ℝ) : IsLipTuple (matAct A π) :=
  fun _ => isLipFun_sum _ _ fun l _ => isLipFun_const_mul _ (hπ l)


lemma continuous_of_lip {K : ℝ≥0} {f : Vec d → ℝ} (h : IsEuclLipschitzWith K f) :
    Continuous f := by
  have : LipschitzWith (K * Real.toNNReal (Real.sqrt d)) f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := h x y
    have h2 := vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y)
    rw [Real.dist_eq, dist_eq_norm]
    push_cast
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    calc |f x - f y| ≤ K * vecEuclideanNorm (x - y) := h1
      _ ≤ K * (Real.sqrt d * ‖x - y‖) := mul_le_mul_of_nonneg_left h2 K.2
      _ = _ := by ring
  exact this.continuous

lemma continuous_of_isLipFun {f : Vec d → ℝ} (h : IsLipFun f) : Continuous f := by
  obtain ⟨K, hK⟩ := h
  exact continuous_of_lip hK

lemma isBorelBdd_of_isBddLipFun {f : Vec d → ℝ} (h : IsBddLipFun f) : IsBorelBdd f :=
  ⟨(continuous_of_isLipFun h.1).measurable, h.2⟩

lemma isBorelBdd_mul {a w : Vec d → ℝ} (ha : IsBorelBdd a) (hw : Measurable w) {B : ℝ}
    (hB : ∀ x, |w x| ≤ B) : IsBorelBdd (fun x => a x * w x) := by
  obtain ⟨hm, C, hC⟩ := ha
  refine ⟨hm.mul hw, |C| * |B|, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC x).trans (le_abs_self _)) ((hB x).trans (le_abs_self _)) (abs_nonneg _)
    (abs_nonneg _)

variable {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ}

lemma akExt_update_add (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h)
    {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) (i : Fin k) {ψ₁ ψ₂ : Vec d → ℝ}
    (h₁ : IsLipFun ψ₁) (h₂ : IsLipFun ψ₂) :
    akExt T h (Function.update π i (fun x => ψ₁ x + ψ₂ x)) =
      akExt T h (Function.update π i ψ₁) + akExt T h (Function.update π i ψ₂) := by
  have key := (akext hT).1.2.2.1 h hh (Function.update π i ψ₁) (isLipTuple_update hπ h₁ i) i ψ₂
    h₂ 1 1
  simp only [Function.update_idem, Function.update_self, one_smul, one_mul] at key
  exact key

lemma akExt_update_smul (hT : IsMetricCurrent k T) {h : Vec d → ℝ} (hh : IsBorelBdd h)
    {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) (i : Fin k) {ψ : Vec d → ℝ}
    (hψ : IsLipFun ψ) (c : ℝ) :
    akExt T h (Function.update π i (fun x => c * ψ x)) = c * akExt T h (Function.update π i ψ) := by
  have key := (akext hT).1.2.2.1 h hh (Function.update π i ψ) (isLipTuple_update hπ hψ i) i ψ
    hψ c 0
  simp only [Function.update_idem, Function.update_self, zero_smul, add_zero, zero_mul] at key
  exact key

end AFree.AKChainAux
