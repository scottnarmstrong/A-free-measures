module

public import AFree.MetricCurrents.AKExt
public import AFree.MetricCurrents.Hadamard

/-!
# Taylor lemma: shared context and Lipschitz bookkeeping

Helpers for `AFree/MetricCurrents/AKTaylor*.lean` (proof of the chain rule).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AFree.MetricCurrents.AKTaylor

open PDE AFree

variable {d k : ℕ}

/-- The standing assumptions of the Taylor lemma, with explicit constants: `Λ` bounds the Euclidean
Lipschitz constants of `π_l` and `M` the sup-operator norms of `Dψ_i`; `μ` is the mass of `T`. -/
structure Ctx (T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ) (π : Fin k → Vec d → ℝ)
    (ψ : Fin k → Vec k → ℝ) (Λ M : ℝ≥0) (μ : Measure (Vec d)) : Prop where
  hT : IsMetricCurrent k T
  hμ : IsAKMass T μ
  hπ : ∀ l, IsEuclLipschitzWith Λ (π l)
  hψ : ∀ i, ContDiff ℝ 1 (ψ i)
  hM : ∀ i y, ‖fderiv ℝ (ψ i) y‖ ≤ M

/-- The tuple `ψ ∘ π = (ψ_i ∘ π)_i`. -/
abbrev psiPi {d k : ℕ} (ψ : Fin k → Vec k → ℝ) (π : Fin k → Vec d → ℝ) : Fin k → Vec d → ℝ :=
  fun i x => ψ i (evalTuple π x)

/-- The weight `h · det Dψ(π)`. -/
noncomputable abbrev jacW {d k : ℕ} (ψ : Fin k → Vec k → ℝ) (π : Fin k → Vec d → ℝ) (h : Vec d → ℝ) :
    Vec d → ℝ :=
  fun x => h x * jacDet ψ (evalTuple π x)

lemma Ctx.isLipTuple {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
    {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)} (c : Ctx T π ψ Λ M μ) :
    IsLipTuple π := fun l => ⟨Λ, c.hπ l⟩

/-! ### Closure properties of `Lip_b` -/

lemma lipb_add {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g) :
    IsBddLipFun (f + g) := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  obtain ⟨⟨K', hK'⟩, C', hC'⟩ := hg
  refine ⟨⟨K + K', fun x y => ?_⟩, C + C', fun x => ?_⟩
  · have h1 := hK x y
    have h2 := hK' x y
    simp only [Pi.add_apply, NNReal.coe_add]
    calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
      _ ≤ _ := by linarith
  · simpa using (abs_add_le (f x) (g x)).trans (add_le_add (hC x) (hC' x))

lemma lipb_smul (c : ℝ) {f : Vec d → ℝ} (hf : IsBddLipFun f) : IsBddLipFun (c • f) := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  refine ⟨⟨‖c‖₊ * K, fun x y => ?_⟩, |c| * C, fun x => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
    rw [← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK x y) (abs_nonneg _)
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma lipb_mul {f g : Vec d → ℝ} (hf : IsBddLipFun f) (hg : IsBddLipFun g) :
    IsBddLipFun (fun x => f x * g x) := by
  obtain ⟨⟨K, hK⟩, C, hC⟩ := hf
  obtain ⟨⟨K', hK'⟩, C', hC'⟩ := hg
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hC0' : 0 ≤ C' := (abs_nonneg _).trans (hC' 0)
  refine ⟨⟨(C.toNNReal * K' + C'.toNNReal * K), fun x y => ?_⟩, C * C', fun x => ?_⟩
  · have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul (hC x) (hK' x y) (abs_nonneg _) hC0
    have h2 := mul_le_mul (hC' y) (hK x y) (abs_nonneg _) hC0'
    push_cast
    rw [Real.coe_toNNReal _ hC0, Real.coe_toNNReal _ hC0']
    nlinarith
  · rw [abs_mul]; exact mul_le_mul (hC x) (hC' x) (abs_nonneg _) hC0

lemma lipb_const (c : ℝ) : IsBddLipFun (fun _ : Vec d => c) :=
  ⟨⟨0, fun x y => by simp⟩, |c|, fun _ => le_rfl⟩

lemma lipb_sum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ} (hf : ∀ i ∈ s, IsBddLipFun (f i)) :
    IsBddLipFun (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lipb_const (d := d) 0
  | insert a s ha ih =>
    have := lipb_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have e : (fun x => ∑ i ∈ insert a s, f i x) = f a + fun x => ∑ i ∈ s, f i x := by
      funext x; simp [Finset.sum_insert ha]
    rw [e]; exact this

/-! ### Tuples -/

section ctx

variable {T : (Vec d → ℝ) → (Fin k → Vec d → ℝ) → ℝ} {π : Fin k → Vec d → ℝ}
  {ψ : Fin k → Vec k → ℝ} {Λ M : ℝ≥0} {μ : Measure (Vec d)}

lemma norm_evalTuple_sub_le (hπ : ∀ l, IsEuclLipschitzWith Λ (π l)) (x x' : Vec d) :
    ‖evalTuple π x - evalTuple π x'‖ ≤ Λ * vecEuclideanNorm (x - x') := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg Λ.coe_nonneg (vecEuclideanNorm_nonneg _))).2 fun l => ?_
  simpa [evalTuple] using hπ l x x'

/-- Composition of a sup-Lipschitz function on `ℝ^k` with the tuple map is Euclidean Lipschitz. -/
lemma lip_comp (hπ : ∀ l, IsEuclLipschitzWith Λ (π l)) (u : Vec k → ℝ) (C : ℝ≥0)
    (hu : ∀ y y', |u y - u y'| ≤ C * ‖y - y'‖) :
    IsEuclLipschitzWith (C * Λ) (fun x => u (evalTuple π x)) := by
  intro x x'
  have h1 := hu (evalTuple π x) (evalTuple π x')
  have h2 := mul_le_mul_of_nonneg_left (norm_evalTuple_sub_le hπ x x') C.coe_nonneg
  push_cast
  linarith

lemma continuous_of_eucl {K : ℝ≥0} {f : Vec d → ℝ} (hf : IsEuclLipschitzWith K f) :
    Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := K * (Real.sqrt d).toNNReal)
    fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  have h1 := hf x y
  have h2 : vecEuclideanNorm (x - y) ≤ √d * ‖x - y‖ := vecEuclideanNorm_le_sqrt_natCast_mul_norm _
  have h3 := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  linarith [mul_assoc (K : ℝ) (√d) ‖x - y‖]

lemma continuous_evalTuple (hπ : ∀ l, IsEuclLipschitzWith Λ (π l)) :
    Continuous (evalTuple π) :=
  continuous_pi fun l => continuous_of_eucl (hπ l)

/-- The partial derivatives determine the derivative of a function on `ℝ^k`. -/
lemma fderiv_apply_eq_sum (f : Vec k → ℝ) (y v : Vec k) :
    fderiv ℝ f y v = ∑ l, v l * fderiv ℝ f y (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : (Pi.single l (v l) : Vec k) = v l • (Pi.single l 1 : Vec k) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul, smul_eq_mul]

lemma matAct_jacMat (A : Fin k → Vec k → ℝ) (c : Vec k) (i : Fin k) (x : Vec d) :
    matAct (jacMat A c) π i x = fderiv ℝ (A i) c (evalTuple π x) := by
  rw [fderiv_apply_eq_sum]
  simp only [matAct, jacMat, Matrix.of_apply, evalTuple]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma psi_lip (c : Ctx T π ψ Λ M μ) (i : Fin k) (y y' : Vec k) :
    |ψ i y - ψ i y'| ≤ M * ‖y - y'‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ψ i) (s := Set.univ) (C := (M : ℝ))
    (fun x _ => ((c.hψ i).differentiable one_ne_zero) x) (fun x _ => c.hM i x) convex_univ
    (Set.mem_univ y') (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using this

lemma isLipTuple_psi (c : Ctx T π ψ Λ M μ) :
    IsLipTuple (psiPi ψ π) := fun i =>
  ⟨_, lip_comp c.hπ (ψ i) M (psi_lip c i)⟩

lemma piEuclideanNorm_le_of_abs_le (v : Fin k → ℝ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, |v i| ≤ c) :
    piEuclideanNorm v ≤ Real.sqrt k * c := by
  unfold piEuclideanNorm
  calc Real.sqrt (∑ i, v i * v i) ≤ Real.sqrt (k * c ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc ∑ i, v i * v i ≤ ∑ _i : Fin k, c ^ 2 := Finset.sum_le_sum fun i _ => by
              have := hv i
              nlinarith [abs_nonneg (v i), sq_abs (v i)]
          _ = k * c ^ 2 := by simp
    _ = Real.sqrt k * c := by
        rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq hc]

lemma abs_jacMat_le (c : Ctx T π ψ Λ M μ) (y : Vec k) (i l : Fin k) :
    |jacMat ψ y i l| ≤ M := by
  have h1 : |fderiv ℝ (ψ i) y (Pi.single l 1)| ≤ ‖fderiv ℝ (ψ i) y‖ * ‖(Pi.single l 1 : Vec k)‖ := by
    simpa [Real.norm_eq_abs] using (fderiv ℝ (ψ i) y).le_opNorm (Pi.single l 1)
  have h2 : ‖(Pi.single l 1 : Vec k)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j; by_cases hj : j = l <;> simp [hj]
  have := mul_le_mul (c.hM i y) h2 (norm_nonneg _) M.coe_nonneg
  simp only [jacMat, Matrix.of_apply]
  linarith

lemma piEuclideanNorm_jacMat_le (c : Ctx T π ψ Λ M μ) (y : Vec k) (i : Fin k) :
    piEuclideanNorm (jacMat ψ y i) ≤ Real.sqrt k * M :=
  piEuclideanNorm_le_of_abs_le _ M.coe_nonneg (abs_jacMat_le c y i)

lemma abs_jacDet_le (c : Ctx T π ψ Λ M μ) (y : Vec k) :
    |jacDet ψ y| ≤ (Real.sqrt k * M) ^ k :=
  hadamard_abs_det_le_pow _ (piEuclideanNorm_jacMat_le c y)

lemma continuous_jacDet (c : Ctx T π ψ Λ M μ) : Continuous (jacDet ψ) := by
  unfold jacDet
  refine (Continuous.matrix_det ?_)
  refine continuous_matrix fun i j => ?_
  simp only [jacMat, Matrix.of_apply]
  have h : Continuous (fderiv ℝ (ψ i)) := (c.hψ i).continuous_fderiv one_ne_zero
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Vec k)).continuous.comp h

lemma borelBdd_of_lipb {f : Vec d → ℝ} (hf : IsBddLipFun f) : IsBorelBdd f :=
  ⟨(continuous_of_eucl hf.1.choose_spec).measurable, hf.2⟩

lemma borelBdd_mul_jacDet (c : Ctx T π ψ Λ M μ) {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    IsBorelBdd (jacW ψ π h) := by
  refine ⟨hh.1.mul ((continuous_jacDet c).comp (continuous_evalTuple c.hπ)).measurable, ?_⟩
  obtain ⟨C, hC⟩ := hh.2
  refine ⟨C * (Real.sqrt k * M) ^ k, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (abs_jacDet_le c _) (abs_nonneg _) ((abs_nonneg _).trans (hC 0))

lemma abs_akExt_le (c : Ctx T π ψ Λ M μ) {h : Vec d → ℝ} (hh : IsBorelBdd h)
    {π' : Fin k → Vec d → ℝ} {K : Fin k → ℝ≥0} (hπ' : ∀ i, IsEuclLipschitzWith (K i) (π' i)) :
    |akExt T h π'| ≤ (∏ i, (K i : ℝ)) * ∫ x, |h x| ∂μ :=
  (akext c.hT).1.2.2.2 μ c.hμ.1 h hh π' K hπ'

lemma integrable_of_borelBdd [IsFiniteMeasure μ] {h : Vec d → ℝ} (hh : IsBorelBdd h) :
    Integrable h μ := by
  obtain ⟨C, hC⟩ := hh.2
  exact Integrable.of_bound hh.1.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

end ctx

end AFree.MetricCurrents.AKTaylor
