module

public import AFree.TopCurrents.PiolaDet

/-!
# Divergence structure of minors

For `G : Fin m → Vec d → ℝ` of class `C²` and `r : Fin (s+1) → Fin m`, `c : Fin (s+1) → Fin d`
(`r`, `c` the enumerations of `I`, `J`), with `r' = r ∘ succ` and `c^b = c ∘ b.succAbove`:
(a) Laplace expansion along the first row; (b) the Piola identity `∑ (-1)^b ∂_{c b} M_{r', c^b} = 0`;
(c) the divergence form `M = ∑ (-1)^b ∂_{c b} (G_{r 0} M_{r', c^b})`.
-/

@[expose] public section

open Matrix

namespace AFree

open PDE

variable {d m s : ℕ}

/-- (a) Laplace expansion of a minor along its first row. -/
theorem piola_laplace (G : Fin m → Vec d → ℝ) (r : Fin (s + 1) → Fin m)
    (c : Fin (s + 1) → Fin d) (x : Vec d) :
    minorDet G r c x = ∑ b : Fin (s + 1), (-1) ^ (b : ℕ) * fderiv ℝ (G (r 0)) x (Pi.single (c b) 1) *
      minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) x := by
  unfold minorDet
  rw [Matrix.det_succ_row_zero]
  exact Finset.sum_congr rfl fun b _ => rfl

/-- Linearity of the determinant in one row. -/
private lemma det_updateRow_expand {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin n)
    (v : Fin n → ℝ) :
    (M.updateRow a v).det = ∑ j, v j * (M.updateRow a (Pi.single j 1)).det := by
  classical
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap.toLinearMap M a
  have hL : ∀ w, L w = (M.updateRow a w).det := fun w => rfl
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [← hL]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hL]
  rfl

/-- The determinant with row `0` replaced by `e_b` and row `a'` by `e_j`, antisymmetric in `(b,j)`. -/
private lemma beta_antisymm {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a' : Fin (n + 1))
    (ha : a' ≠ 0) (b j : Fin (n + 1)) :
    ((A.updateRow 0 (Pi.single j 1)).updateRow a' (Pi.single b 1)).det =
      -((A.updateRow 0 (Pi.single b 1)).updateRow a' (Pi.single j 1)).det := by
  have h := Matrix.det_permute (Equiv.swap (0 : Fin (n + 1)) a')
    ((A.updateRow 0 (Pi.single b 1)).updateRow a' (Pi.single j 1))
  rw [Equiv.Perm.sign_swap ha.symm] at h
  have e : ((A.updateRow 0 (Pi.single b 1)).updateRow a' (Pi.single j 1)).submatrix
      (Equiv.swap (0 : Fin (n + 1)) a') id =
      (A.updateRow 0 (Pi.single j 1)).updateRow a' (Pi.single b 1) := by
    ext i k
    by_cases h0 : i = 0
    · subst h0
      simp [Equiv.swap_apply_left, Matrix.updateRow_ne ha.symm]
    · by_cases h1 : i = a'
      · subst h1; simp [Equiv.swap_apply_right, Matrix.updateRow_ne ha.symm]
      · simp [Equiv.swap_apply_of_ne_of_ne h0 h1, Matrix.updateRow_ne h0, Matrix.updateRow_ne h1]
  rw [e] at h
  simpa using h

private lemma hasFDerivAt_fderiv_apply {G : Vec d → ℝ} (hG : ContDiff ℝ 2 G) (x w : Vec d) :
    HasFDerivAt (fun y => fderiv ℝ G y w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ G) x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  exact (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hd.hasFDerivAt

private lemma laplace_row {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (b : Fin (n + 1))
    (a : Fin n) (v : Fin (n + 1) → ℝ) :
    (-1 : ℝ) ^ (b : ℕ) * ((A.submatrix Fin.succ b.succAbove).updateRow a
        (fun j => v (b.succAbove j))).det =
      ((A.updateRow 0 (Pi.single b 1)).updateRow a.succ v).det := by
  rw [Matrix.det_succ_row_zero]
  have h0 : ∀ k, ((A.updateRow 0 (Pi.single b 1)).updateRow a.succ v) 0 k = (Pi.single b (1 : ℝ) : Fin (n + 1) → ℝ) k := by
    intro k
    rw [Matrix.updateRow_ne (Fin.succ_ne_zero a).symm]; simp
  simp only [h0]
  rw [Finset.sum_eq_single b]
  · have e : ((A.updateRow 0 (Pi.single b 1)).updateRow a.succ v).submatrix Fin.succ b.succAbove =
        (A.submatrix Fin.succ b.succAbove).updateRow a (fun j => v (b.succAbove j)) := by
      ext i k
      by_cases hi : i = a
      · subst hi; simp
      · have : i.succ ≠ a.succ := fun h => hi (Fin.succ_injective _ h)
        simp [Matrix.updateRow_ne hi, Matrix.updateRow_ne this, Fin.succ_ne_zero]
    rw [e]; simp
  · intro j _ hj; simp [hj]
  · simp

/-- (b) The Piola identity. -/
theorem piola_div_free (G : Fin m → Vec d → ℝ) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (r : Fin (s + 1) → Fin m) (c : Fin (s + 1) → Fin d) (x : Vec d) :
    ∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      fderiv ℝ (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x (Pi.single (c b) 1) =
      0 := by
  classical
  set A : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ := (jacMat G x).submatrix r c with hA
  set H : Fin m → Vec d → Vec d → ℝ := fun i p q => fderiv ℝ (fderiv ℝ (G i)) x p q with hH
  have Hsymm : ∀ i p q, H i p q = H i q p := fun i p q =>
    ((hG i).contDiffAt.isSymmSndFDerivAt (by simp)).eq p q
  have hD : ∀ b : Fin (s + 1),
      fderiv ℝ (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x (Pi.single (c b) 1) =
        ∑ a : Fin s, ((A.submatrix Fin.succ b.succAbove).updateRow a
          (fun j => H (r a.succ) (Pi.single (c b) 1) (Pi.single (c (b.succAbove j)) 1))).det := by
    intro b
    obtain ⟨D, hD, hDv⟩ := hasFDerivAt_det_rows
      (M := fun a j y => fderiv ℝ (G (r a.succ)) y (Pi.single (c (b.succAbove j)) 1))
      (M' := fun a j => (ContinuousLinearMap.apply ℝ ℝ (Pi.single (c (b.succAbove j)) 1)).comp
        (fderiv ℝ (fderiv ℝ (G (r a.succ))) x)) (x := x)
      (fun a j => hasFDerivAt_fderiv_apply (hG _) x _)
    have e : (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) =
        fun y => (Matrix.of fun (a j : Fin s) =>
          fderiv ℝ (G (r a.succ)) y (Pi.single (c (b.succAbove j)) 1)).det := rfl
    rw [e, hD.fderiv, hDv]
    exact Finset.sum_congr rfl fun a _ => rfl
  have key : ∀ a : Fin s, ∑ b : Fin (s + 1), ((A.submatrix Fin.succ b.succAbove).updateRow a
      (fun j => H (r a.succ) (Pi.single (c b) 1) (Pi.single (c (b.succAbove j)) 1))).det *
        (-1 : ℝ) ^ (b : ℕ) = 0 := by
    intro a
    set β : Fin (s + 1) → Fin (s + 1) → ℝ := fun b j =>
      ((A.updateRow 0 (Pi.single b 1)).updateRow a.succ (Pi.single j 1)).det with hβ
    set h : Fin (s + 1) → Fin (s + 1) → ℝ := fun b j =>
      H (r a.succ) (Pi.single (c b) 1) (Pi.single (c j) 1) with hh
    have h1 : ∀ b, ((A.submatrix Fin.succ b.succAbove).updateRow a
        (fun j => h b (b.succAbove j))).det * (-1 : ℝ) ^ (b : ℕ) = ∑ j, h b j * β b j := by
      intro b
      rw [mul_comm, laplace_row A b a (h b)]
      exact det_updateRow_expand _ _ _
    have h2 : ∑ b, ∑ j, h b j * β b j = - ∑ b, ∑ j, h b j * β b j := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : β j b = -β b j := beta_antisymm A a.succ (Fin.succ_ne_zero a) b j
      have hs : h j b = h b j := Hsymm _ _ _
      rw [this, hs, mul_neg]
    have h3 : ∑ b, ∑ j, h b j * β b j = 0 := by linarith
    rw [← h3]
    exact Finset.sum_congr rfl fun b _ => h1 b
  calc _ = ∑ b : Fin (s + 1), ∑ a : Fin s, ((A.submatrix Fin.succ b.succAbove).updateRow a
        (fun j => H (r a.succ) (Pi.single (c b) 1) (Pi.single (c (b.succAbove j)) 1))).det *
          (-1 : ℝ) ^ (b : ℕ) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hD b, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a : Fin s, ∑ b : Fin (s + 1), ((A.submatrix Fin.succ b.succAbove).updateRow a
        (fun j => H (r a.succ) (Pi.single (c b) 1) (Pi.single (c (b.succAbove j)) 1))).det *
          (-1 : ℝ) ^ (b : ℕ) := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun a _ => key a

private lemma minorDet_differentiableAt (G : Fin m → Vec d → ℝ) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (r : Fin s → Fin m) (c : Fin s → Fin d) (x : Vec d) :
    DifferentiableAt ℝ (fun y => minorDet G r c y) x := by
  obtain ⟨D, hD, -⟩ := hasFDerivAt_det_rows
    (M := fun a j y => fderiv ℝ (G (r a)) y (Pi.single (c j) 1))
    (M' := fun a j => (ContinuousLinearMap.apply ℝ ℝ (Pi.single (c j) 1)).comp
      (fderiv ℝ (fderiv ℝ (G (r a))) x)) (x := x)
    (fun a j => hasFDerivAt_fderiv_apply (hG _) x _)
  exact hD.differentiableAt

/-- Part (c) of `piola`: The divergence form `M = ∑ (-1)^b ∂_{c b}(G_{r 0} M')`. -/
theorem piola_div_form (G : Fin m → Vec d → ℝ) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (r : Fin (s + 1) → Fin m) (c : Fin (s + 1) → Fin d) (x : Vec d) :
    minorDet G r c x = ∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      fderiv ℝ (fun y => G (r 0) y * minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x
        (Pi.single (c b) 1) := by
  have hprod : ∀ b : Fin (s + 1),
      fderiv ℝ (fun y => G (r 0) y * minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x
        (Pi.single (c b) 1) =
      G (r 0) x * fderiv ℝ (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x
        (Pi.single (c b) 1) +
      fderiv ℝ (G (r 0)) x (Pi.single (c b) 1) *
        minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) x := by
    intro b
    have h1 : DifferentiableAt ℝ (G (r 0)) x := ((hG _).differentiable (by simp)) x
    have h2 := minorDet_differentiableAt G hG (r ∘ Fin.succ) (c ∘ b.succAbove) x
    have := fderiv_mul h1 h2
    simp only [Pi.mul_def] at this
    rw [this]
    simp [mul_comm]
  have hb := piola_div_free G hG r c x
  rw [piola_laplace G r c x]
  simp only [hprod, mul_add, Finset.sum_add_distrib]
  have : ∑ b : Fin (s + 1), (-1 : ℝ) ^ (b : ℕ) * (G (r 0) x *
      fderiv ℝ (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x (Pi.single (c b) 1)) =
      G (r 0) x * ∑ b : Fin (s + 1), (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x (Pi.single (c b) 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, hb, mul_zero, zero_add]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Divergence structure of minors: for `G ∈ C²`, (a) Laplace expansion along the first
row, (b) the Piola identity, (c) the divergence form. -/
theorem piola (G : Fin m → Vec d → ℝ) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (r : Fin (s + 1) → Fin m) (c : Fin (s + 1) → Fin d) (x : Vec d) :
    (minorDet G r c x = ∑ b : Fin (s + 1), (-1) ^ (b : ℕ) * fderiv ℝ (G (r 0)) x
        (Pi.single (c b) 1) * minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) x) ∧
    (∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      fderiv ℝ (fun y => minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x (Pi.single (c b) 1) =
      0) ∧
    (minorDet G r c x = ∑ b : Fin (s + 1), (-1) ^ (b : ℕ) *
      fderiv ℝ (fun y => G (r 0) y * minorDet G (r ∘ Fin.succ) (c ∘ b.succAbove) y) x
        (Pi.single (c b) 1)) :=
  ⟨piola_laplace G r c x, piola_div_free G hG r c x, piola_div_form G hG r c x⟩

end AFree
