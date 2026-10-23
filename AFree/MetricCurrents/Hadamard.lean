module

public import AFree.MetricCurrents.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hadamard's inequality
-/

@[expose] public section

open scoped BigOperators

namespace AFree

open PDE

private lemma piEuclideanNorm_eq_norm {s : ℕ} (v : Fin s → ℝ) :
    piEuclideanNorm v = ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : Fin s => ℝ))‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [piEuclideanNorm, Real.norm_eq_abs, sq, abs_mul_abs_self]

private lemma piEuclideanNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ piEuclideanNorm v := Real.sqrt_nonneg _

/-- Hadamard's inequality: `|det(a_1,…,a_s)| ≤ ∏ |a_i|` (rows `a_i`, Euclidean
norms). -/
theorem hadamard_abs_det_le {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) :
    |A.det| ≤ ∏ i, piEuclideanNorm (A i) := by
  let E := PiLp 2 (fun _ : Fin s => ℝ)
  let f : Fin s → E := fun i => WithLp.toLp 2 (A i)
  have hdim : Module.finrank ℝ E = Fintype.card (Fin s) := by simp [E]
  let gs := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  let std : OrthonormalBasis (Fin s) ℝ E := ⟨LinearIsometryEquiv.refl _ _⟩
  have h1 : gs.toBasis.det f = ∏ i, inner ℝ (gs i) (f i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim f
  have h2 : std.toBasis.det f = std.toBasis.det gs.toBasis * gs.toBasis.det f := by
    have := congrArg (fun m => m f) (AlternatingMap.eq_smul_basis_det gs.toBasis (f := std.toBasis.det))
    simpa using this
  have h3 : ‖std.toBasis.det gs.toBasis‖ = 1 := OrthonormalBasis.det_to_matrix_orthonormalBasis std gs
  have h4 : std.toBasis.det f = A.transpose.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have h5 : |A.det| = |gs.toBasis.det f| := by
    have : |std.toBasis.det f| = |gs.toBasis.det f| := by
      rw [h2, abs_mul]
      have : |std.toBasis.det gs.toBasis| = 1 := by rw [← Real.norm_eq_abs]; exact h3
      rw [this, one_mul]
    rw [← this, h4, Matrix.det_transpose]
  rw [h5, h1, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [piEuclideanNorm_eq_norm]
  exact (abs_real_inner_le_norm _ _).trans (by rw [gs.norm_eq_one]; simp [f])

/-- If all rows have norm `≤ C` then `|det| ≤ C ^ s`. -/
theorem hadamard_abs_det_le_pow {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) {C : ℝ}
    (h : ∀ i, piEuclideanNorm (A i) ≤ C) : |A.det| ≤ C ^ s := by
  refine (hadamard_abs_det_le A).trans ?_
  calc ∏ i, piEuclideanNorm (A i) ≤ ∏ _i : Fin s, C :=
        Finset.prod_le_prod₀ (fun i _ => piEuclideanNorm_nonneg' _) fun i _ => h i
    _ = C ^ s := by simp

private lemma abs_det_updateRow_le {s : ℕ} (M : Matrix (Fin s) (Fin s) ℝ) (i : Fin s)
    (u : Fin s → ℝ) {B δ : ℝ} (hM : ∀ j, j ≠ i → piEuclideanNorm (M j) ≤ B)
    (hu : piEuclideanNorm u ≤ δ) : |(M.updateRow i u).det| ≤ δ * B ^ (s - 1) := by
  refine (hadamard_abs_det_le _).trans ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Matrix.updateRow_self]
  refine mul_le_mul hu ?_ (Finset.prod_nonneg fun _ _ => piEuclideanNorm_nonneg' _)
    ((piEuclideanNorm_nonneg' _).trans hu)
  have : ∏ j ∈ Finset.univ.erase i, piEuclideanNorm (M.updateRow i u j) ≤
      ∏ _j ∈ Finset.univ.erase i, B :=
    Finset.prod_le_prod₀ (fun _ _ => piEuclideanNorm_nonneg' _) fun j hj => by
      rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj)]
      exact hM j (Finset.ne_of_mem_erase hj)
  refine this.trans ?_
  simp [Finset.card_erase_of_mem]

/-- Perturbation: rows of norm `≤ M`, differing by `≤ δ`, change the determinant by
at most `s M^(s-1) δ`. -/
theorem hadamard_abs_det_sub_le {s : ℕ} (A B : Matrix (Fin s) (Fin s) ℝ) {M δ : ℝ}
    (hA : ∀ i, piEuclideanNorm (A i) ≤ M) (hB : ∀ i, piEuclideanNorm (B i) ≤ M)
    (hAB : ∀ i, piEuclideanNorm (A i - B i) ≤ δ) :
    |A.det - B.det| ≤ s * M ^ (s - 1) * δ := by
  let D : ℕ → Matrix (Fin s) (Fin s) ℝ := fun n => Matrix.of fun j => if (j : ℕ) < n then B j else A j
  have hD0 : D 0 = A := by ext j x; simp [D]
  have hDs : D s = B := by ext j x; simp [D, j.2]
  have key : ∀ i : Fin s, |(D i).det - (D (i + 1)).det| ≤ M ^ (s - 1) * δ := by
    intro i
    have e1 : D i = (D i).updateRow i (A i) := by
      ext j x
      by_cases hj : j = i
      · subst hj; simp [D]
      · simp [Matrix.updateRow_ne hj]
    have e2 : D (i + 1) = (D i).updateRow i (B i) := by
      ext j x
      by_cases hj : j = i
      · subst hj; simp [D]
      · have : ((j : ℕ) < i + 1 ↔ (j : ℕ) < i) := by
          have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
          omega
        simp [D, Matrix.updateRow_ne hj, this]
    have : (D i).det - (D (i + 1)).det = ((D i).updateRow i (A i - B i)).det := by
      have := Matrix.det_updateRow_add (D i) i (A i - B i) (B i)
      rw [sub_add_cancel, ← e1, ← e2] at this
      linarith
    rw [this, mul_comm]
    refine abs_det_updateRow_le _ i _ (fun j hj => ?_) (hAB i)
    show piEuclideanNorm (if (j : ℕ) < i then B j else A j) ≤ M
    split_ifs
    exacts [hB j, hA j]
  have hsum : A.det - B.det = ∑ i : Fin s, ((D i).det - (D (i + 1)).det) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (D i).det - (D (i + 1)).det) s,
      Finset.sum_range_sub', hD0, hDs]
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => key i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [le_refl ((s : ℝ) * (M ^ (s - 1) * δ))]

private lemma piEuclideanNorm_comp_le {s n : ℕ} (v : Fin n → ℝ) (c : Fin s → Fin n)
    (hc : Function.Injective c) : piEuclideanNorm (fun j => v (c j)) ≤ piEuclideanNorm v := by
  unfold piEuclideanNorm
  refine Real.sqrt_le_sqrt ?_
  rw [← Finset.sum_image (s := Finset.univ) (g := c) (f := fun l => v l * v l)
    (fun a _ b _ h => hc h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun l _ _ => mul_self_nonneg _

/-- Minors: every `s × s` minor of a `k × d` matrix with rows of Euclidean norm
`≤ C_i` is bounded by the product of the `C_{r i}` over the chosen rows `r` (in particular by
`C^s` if all `C_i ≤ C`). -/
theorem hadamard_abs_minor_le {k d s : ℕ} (A : Matrix (Fin k) (Fin d) ℝ) {C : Fin k → ℝ}
    (h : ∀ i, piEuclideanNorm (A i) ≤ C i) (r : Fin s → Fin k) (c : Fin s → Fin d)
    (hc : Function.Injective c) : |(A.submatrix r c).det| ≤ ∏ i, C (r i) := by
  refine (hadamard_abs_det_le _).trans ?_
  exact Finset.prod_le_prod₀ (fun i _ => piEuclideanNorm_nonneg' _) fun i _ =>
    (piEuclideanNorm_comp_le (A (r i)) c hc).trans (h _)

end AFree
