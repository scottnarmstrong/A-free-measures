module

public import AFree.Defs
public import AFree.Analysis.WaveCone
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.ClassicalLaplacian

/-!
# Vector calculus helpers for the elliptic system

Coordinate derivatives of vector fields, and Euclidean operator-norm bounds for matrices, used for the
mollified elliptic system in [DPR, proof of Theorem 1.1].
-/

@[expose] public section

open Matrix

namespace AFree

open PDE

variable {d : ℕ}

lemma euclideanBall_zero_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    euclideanBall (0 : Vec d) a ⊆ euclideanBall 0 b := by
  intro x hx
  simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq] at hx ⊢
  nlinarith

section Deriv

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise derivative `∂_ℓ f` of a vector field `f : ℝ^d → ℝ^ι`. -/
noncomputable def vecCoordDeriv (ℓ : Fin d) (f : Vec d → ι → ℝ) (x : Vec d) : ι → ℝ :=
  fun i => euclideanCoordDeriv ℓ (fun z => f z i) x

lemma euclideanCoordDeriv_mul {a b : Vec d → ℝ} {x : Vec d} (ℓ : Fin d)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    euclideanCoordDeriv ℓ (fun z => a z * b z) x =
      euclideanCoordDeriv ℓ a x * b x + a x * euclideanCoordDeriv ℓ b x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_mul ha hb]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

lemma euclideanCoordDeriv_sub {a b : Vec d → ℝ} {x : Vec d} (ℓ : Fin d)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    euclideanCoordDeriv ℓ (fun z => a z - b z) x =
      euclideanCoordDeriv ℓ a x - euclideanCoordDeriv ℓ b x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_sub ha hb]
  simp

lemma euclideanCoordDeriv_neg (ℓ : Fin d) (a : Vec d → ℝ) (x : Vec d) :
    euclideanCoordDeriv ℓ (fun z => -a z) x = -euclideanCoordDeriv ℓ a x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_neg]
  simp

lemma differentiableAt_coord {f : Vec d → ι → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι)
    (x : Vec d) : DifferentiableAt ℝ (fun z => f z i) x :=
  ((contDiff_pi.1 hf i).differentiable (by simp)) x

lemma vecCoordDeriv_mulVec {κ : Type*} [Fintype κ] (C : Matrix κ ι ℝ) {f : Vec d → ι → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ℓ : Fin d) (x : Vec d) :
    vecCoordDeriv ℓ (fun z => C *ᵥ f z) x = C *ᵥ vecCoordDeriv ℓ f x := by
  funext k
  have h : ∀ j ∈ Finset.univ, HasFDerivAt (fun z => C k j * f z j)
      (C k j • fderiv ℝ (fun z => f z j) x) x := fun j _ =>
    (differentiableAt_coord hf j x).hasFDerivAt.const_mul (C k j)
  have := HasFDerivAt.sum h
  simp only [vecCoordDeriv, euclideanCoordDeriv, Matrix.mulVec, dotProduct]
  have e : (fun z => ∑ j, C k j * f z j) = ∑ j, fun z => C k j * f z j := by
    funext z; simp
  rw [show (fun z => (fun j => ∑ x, C j x * f z x) k) = fun z => ∑ j, C k j * f z j from rfl, e,
    this.fderiv]
  simp

lemma vecCoordDeriv_smul {a : Vec d → ℝ} {f : Vec d → ι → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ℓ : Fin d) (x : Vec d) :
    vecCoordDeriv ℓ (fun z => a z • f z) x =
      euclideanCoordDeriv ℓ a x • f x + a x • vecCoordDeriv ℓ f x := by
  funext i
  simp only [vecCoordDeriv, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  exact euclideanCoordDeriv_mul ℓ ((ha.differentiable (by simp)) x) (differentiableAt_coord hf i x)

lemma vecCoordDeriv_sub {f g : Vec d → ι → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ℓ : Fin d) (x : Vec d) :
    vecCoordDeriv ℓ (fun z => f z - g z) x = vecCoordDeriv ℓ f x - vecCoordDeriv ℓ g x := by
  funext i
  exact euclideanCoordDeriv_sub ℓ (differentiableAt_coord hf i x) (differentiableAt_coord hg i x)

omit [Fintype ι] in
lemma vecCoordDeriv_neg (f : Vec d → ι → ℝ) (ℓ : Fin d) (x : Vec d) :
    vecCoordDeriv ℓ (fun z => -f z) x = -vecCoordDeriv ℓ f x := by
  funext i
  exact euclideanCoordDeriv_neg ℓ (fun z => f z i) x

end Deriv

section Norm

/-- The `ℓ¹` entry bound `Σ |C_{ij}|` of a matrix. -/
noncomputable def matBound {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  ∑ i, ∑ j, |C i j|

lemma matBound_nonneg {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℝ) : 0 ≤ matBound C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The Euclidean norm of `C v` is at most `matBound C · |v|`. -/
lemma vecEuclideanNorm_mulVec_le {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℝ) (v : Vec q) :
    vecEuclideanNorm (C *ᵥ v) ≤ matBound C * vecEuclideanNorm v := by
  refine (vecEuclideanNorm_le_sum_abs _).trans ?_
  unfold matBound
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  have e : (C *ᵥ v) i = ∑ j, C i j * v j := rfl
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_apply_le_vecEuclideanNorm v j) (abs_nonneg _)

lemma vecEuclideanNorm_sum_le {n : ℕ} {ι₀ : Type*} {s : Finset ι₀} (f : ι₀ → Vec n) :
    vecEuclideanNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, vecEuclideanNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vecEuclideanNorm, vecNormSq, vecDot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (vecEuclideanNorm_add_le _ _).trans (by gcongr)

end Norm

end AFree
