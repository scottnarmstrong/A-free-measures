module

public import AFree.MetricCurrents.AKMass

/-!
# Auxiliary closure lemmas for `Lip`, `Lip_b`, `B^∞` (helpers for the elementary properties and the extension)
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace AFree.MetricCurrents.AKExt

open PDE AFree

variable {d : ℕ}

theorem eucl_add {K L : ℝ≥0} {f g : Vec d → ℝ} (hf : IsEuclLipschitzWith K f)
    (hg : IsEuclLipschitzWith L g) : IsEuclLipschitzWith (K + L) (f + g) := by
  intro x y
  have h1 := hf x y
  have h2 := hg x y
  have : |(f + g) x - (f + g) y| ≤ |f x - f y| + |g x - g y| := by
    simp only [Pi.add_apply]
    calc _ = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  push_cast
  nlinarith

theorem eucl_smul {K : ℝ≥0} {f : Vec d → ℝ} (hf : IsEuclLipschitzWith K f) (a : ℝ) :
    IsEuclLipschitzWith (‖a‖₊ * K) (a • f) := by
  intro x y
  have h1 := hf x y
  simp only [Pi.smul_apply, smul_eq_mul]
  calc |a * f x - a * f y| = |a| * |f x - f y| := by rw [← mul_sub, abs_mul]
    _ ≤ |a| * (K * vecEuclideanNorm (x - y)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
    _ = _ := by push_cast; simp [Real.norm_eq_abs]; ring

theorem eucl_const (c : ℝ) : IsEuclLipschitzWith 0 (fun _ : Vec d => c) := by
  intro x y; simp

theorem lip_add {f g : Vec d → ℝ} (hf : IsLipFun f) (hg : IsLipFun g) : IsLipFun (f + g) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨L, hL⟩ := hg
  exact ⟨K + L, eucl_add hK hL⟩

theorem lip_smul {f : Vec d → ℝ} (hf : IsLipFun f) (a : ℝ) : IsLipFun (a • f) := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨_, eucl_smul hK a⟩

theorem lip_const (c : ℝ) : IsLipFun (fun _ : Vec d => c) := ⟨0, eucl_const c⟩

theorem lip_zero : IsLipFun (0 : Vec d → ℝ) := lip_const 0

theorem lip_sub {f g : Vec d → ℝ} (hf : IsLipFun f) (hg : IsLipFun g) :
    IsLipFun (fun x => f x - g x) := by
  have := lip_add hf (lip_smul hg (-1))
  convert this using 1
  funext x; simp [sub_eq_add_neg]

theorem lip_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (ψ : ι → Vec d → ℝ)
    (h : ∀ l ∈ s, IsLipFun (ψ l)) : IsLipFun (∑ l ∈ s, c l • ψ l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lip_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lip_add (lip_smul (h a (Finset.mem_insert_self _ _)) _)
      (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem lipFun_continuous {f : Vec d → ℝ} (hf : IsLipFun f) : Continuous f := by
  obtain ⟨K, hK⟩ := hf
  have : LipschitzWith (K * (Real.sqrt d).toNNReal) f := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    calc |f x - f y| ≤ K * vecEuclideanNorm (x - y) := hK x y
      _ ≤ K * (Real.sqrt d * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) K.2
      _ = _ := by rw [NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]; ring
  exact this.continuous

theorem bddLip_add {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g) :
    IsBddLipFun (f + g) := by
  obtain ⟨hf1, C, hC⟩ := hf
  obtain ⟨hg1, D, hD⟩ := hg
  refine ⟨lip_add hf1 hg1, C + D, fun x => ?_⟩
  simp only [Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hC x) (hD x))

theorem bddLip_smul {f : Vec d → ℝ} (hf : IsBddLipFun f) (a : ℝ) : IsBddLipFun (a • f) := by
  obtain ⟨hf1, C, hC⟩ := hf
  refine ⟨lip_smul hf1 a, |a| * C, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg a)

theorem bddLip_sub {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g) :
    IsBddLipFun (fun x => f x - g x) := by
  have := bddLip_add hf (bddLip_smul hg (-1))
  convert this using 1
  funext x; simp [sub_eq_add_neg]

theorem borelBdd_of_bddLip {f : Vec d → ℝ} (hf : IsBddLipFun f) : IsBorelBdd f :=
  ⟨(lipFun_continuous hf.1).measurable, hf.2⟩

theorem borelBdd_add {f g : Vec d → ℝ} (hf : IsBorelBdd f) (hg : IsBorelBdd g) :
    IsBorelBdd (f + g) := by
  obtain ⟨hf1, C, hC⟩ := hf
  obtain ⟨hg1, D, hD⟩ := hg
  refine ⟨hf1.add hg1, C + D, fun x => ?_⟩
  simp only [Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hC x) (hD x))

theorem borelBdd_smul {f : Vec d → ℝ} (hf : IsBorelBdd f) (a : ℝ) : IsBorelBdd (a • f) := by
  obtain ⟨hf1, C, hC⟩ := hf
  refine ⟨hf1.const_smul a, |a| * C, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg a)

theorem borelBdd_sub {f g : Vec d → ℝ} (hf : IsBorelBdd f) (hg : IsBorelBdd g) :
    IsBorelBdd (fun x => f x - g x) := by
  have := borelBdd_add hf (borelBdd_smul hg (-1))
  convert this using 1
  funext x; simp [sub_eq_add_neg]

theorem integrable_of_borelBdd {f : Vec d → ℝ} (hf : IsBorelBdd f) (μ : Measure (Vec d))
    [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨h1, C, hC⟩ := hf
  exact Integrable.of_bound h1.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem lipTuple_update {k : ℕ} {π : Fin k → Vec d → ℝ} (hπ : IsLipTuple π) (i : Fin k)
    {ψ : Vec d → ℝ} (hψ : IsLipFun ψ) : IsLipTuple (Function.update π i ψ) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hψ
  · simpa [Function.update_of_ne hj] using hπ j

end AFree.MetricCurrents.AKExt
