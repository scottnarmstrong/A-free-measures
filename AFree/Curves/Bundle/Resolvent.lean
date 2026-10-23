module

public import AFree.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The resolvent limit onto the kernel of a symmetric positive semidefinite matrix

For symmetric
positive semidefinite `A`, `(mA + I)⁻¹` converges to the orthogonal projection onto `ker A`.
-/

@[expose] public section

open Matrix Filter Topology

namespace AFree.Bundle

variable {d : ℕ}

/-- A symmetric positive semidefinite real matrix, in the elementary sense. -/
structure IsSymmPSD (A : Matrix (Fin d) (Fin d) ℝ) : Prop where
  symm : Aᵀ = A
  psd : ∀ y : Fin d → ℝ, 0 ≤ y ⬝ᵥ (A *ᵥ y)

/-- The `m`-th resolvent `((m+1) A + I)⁻¹`. -/
noncomputable def resolvent (A : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (((m : ℝ) + 1) • A + 1)⁻¹

variable {A : Matrix (Fin d) (Fin d) ℝ}

theorem dot_comm_of_symm (h : Aᵀ = A) (u w : Fin d → ℝ) :
    (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (A *ᵥ w) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, h, dotProduct_comm]

theorem IsSymmPSD.dot_comm (h : IsSymmPSD A) (u w : Fin d → ℝ) :
    (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (A *ᵥ w) := dot_comm_of_symm h.symm u w

theorem matrix_ext_mulVec {B C : Matrix (Fin d) (Fin d) ℝ} (h : ∀ y, B *ᵥ y = C *ᵥ y) :
    B = C :=
  Matrix.toLin'.injective (LinearMap.ext fun y => by simpa [Matrix.toLin'_apply] using h y)

theorem dot_self_nonneg (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private theorem mulVec_eq_zero (h : IsSymmPSD A) {c : ℝ} (hc : 0 ≤ c) (w : Fin d → ℝ)
    (hw : (c • A + 1) *ᵥ w = 0) : w = 0 := by
  have h1 : w ⬝ᵥ ((c • A + 1) *ᵥ w) = 0 := by rw [hw]; simp
  rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul] at h1
  have h2 := mul_nonneg hc (h.psd w)
  have h3 : w ⬝ᵥ w = 0 := by
    have := dot_self_nonneg w
    simp only [smul_eq_mul] at h1
    linarith
  exact dotProduct_self_eq_zero.1 h3

private theorem isUnit_det (h : IsSymmPSD A) {c : ℝ} (hc : 0 ≤ c) : IsUnit (c • A + 1).det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro y z hyz
  have : (c • A + 1) *ᵥ (y - z) = 0 := by rw [mulVec_sub, hyz, sub_self]
  exact sub_eq_zero.1 (mulVec_eq_zero h hc _ this)

private theorem res_mul (h : IsSymmPSD A) (m : ℕ) :
    (((m : ℝ) + 1) • A + 1) * resolvent A m = 1 :=
  mul_nonsing_inv _ (isUnit_det h (by positivity))

private theorem mul_res (h : IsSymmPSD A) (m : ℕ) :
    resolvent A m * (((m : ℝ) + 1) • A + 1) = 1 :=
  nonsing_inv_mul _ (isUnit_det h (by positivity))

/-- `M u = z` for `u = R z`. -/
private theorem mulVec_res (h : IsSymmPSD A) (m : ℕ) (z : Fin d → ℝ) :
    (((m : ℝ) + 1) • A + 1) *ᵥ (resolvent A m *ᵥ z) = z := by
  rw [mulVec_mulVec, res_mul h, one_mulVec]

private theorem res_mulVec_fixed (h : IsSymmPSD A) (m : ℕ) {k : Fin d → ℝ} (hk : A *ᵥ k = 0) :
    resolvent A m *ᵥ k = k := by
  have : (((m : ℝ) + 1) • A + 1) *ᵥ k = k := by
    rw [add_mulVec, smul_mulVec, hk]; simp
  have h2 := congrArg (fun v => resolvent A m *ᵥ v) this
  simp only [mulVec_mulVec, mul_res h, one_mulVec] at h2
  exact h2.symm

private theorem res_comm (h : IsSymmPSD A) (m : ℕ) :
    resolvent A m * A = A * resolvent A m := by
  set M := ((m : ℝ) + 1) • A + 1 with hM
  have h1 : M * A = A * M := by
    rw [hM, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  calc resolvent A m * A = resolvent A m * A * (M * resolvent A m) := by
        rw [res_mul h, mul_one]
    _ = resolvent A m * (A * M) * resolvent A m := by simp only [Matrix.mul_assoc]
    _ = resolvent A m * (M * A) * resolvent A m := by rw [h1]
    _ = (resolvent A m * M) * A * resolvent A m := by simp only [Matrix.mul_assoc]
    _ = A * resolvent A m := by rw [mul_res h, one_mul]

/-- `‖R z‖² ≤ ‖z‖²`. -/
private theorem res_bound (h : IsSymmPSD A) (m : ℕ) (z : Fin d → ℝ) :
    (resolvent A m *ᵥ z) ⬝ᵥ (resolvent A m *ᵥ z) ≤ z ⬝ᵥ z := by
  set u := resolvent A m *ᵥ z with hu
  have hz : (((m : ℝ) + 1) • A + 1) *ᵥ u = z := mulVec_res h m z
  have h1 : u ⬝ᵥ z = ((m : ℝ) + 1) * (u ⬝ᵥ (A *ᵥ u)) + u ⬝ᵥ u := by
    conv_lhs => rw [← hz]
    rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1) (h.psd u)
  have h3 := dot_self_nonneg (u - z)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm z u] at h3
  linarith

/-- `R (A z) = (1/(m+1)) (z - R z)`. -/
private theorem res_mulVec_range (h : IsSymmPSD A) (m : ℕ) (z : Fin d → ℝ) :
    resolvent A m *ᵥ (A *ᵥ z) = (((m : ℝ) + 1)⁻¹) • (z - resolvent A m *ᵥ z) := by
  have hz := mulVec_res h m z
  have h1 : resolvent A m *ᵥ (A *ᵥ z) = A *ᵥ (resolvent A m *ᵥ z) := by
    rw [mulVec_mulVec, mulVec_mulVec, res_comm h]
  rw [h1]
  rw [add_mulVec, smul_mulVec, one_mulVec] at hz
  have h2 : z - resolvent A m *ᵥ z = ((m : ℝ) + 1) • (A *ᵥ (resolvent A m *ᵥ z)) := by
    exact sub_eq_of_eq_add hz.symm
  rw [h2, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- Kernel and range of a symmetric matrix span everything. -/
theorem IsSymmPSD.exists_decomp (h : IsSymmPSD A) (y : Fin d → ℝ) :
    ∃ k z, A *ᵥ k = 0 ∧ y = k + A *ᵥ z := by
  let f := Matrix.toLin' A
  have hinf : LinearMap.ker f ⊓ LinearMap.range f = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hk, z, rfl⟩
    have hk' : A *ᵥ (A *ᵥ z) = 0 := by simpa [f] using hk
    have : (A *ᵥ z) ⬝ᵥ (A *ᵥ z) = 0 := by
      rw [h.dot_comm, hk', dotProduct_zero]
    simpa [f] using (dotProduct_self_eq_zero.1 this)
  have hsup : LinearMap.ker f ⊔ LinearMap.range f = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.range f)
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    rw [hinf, finrank_bot] at h1
    omega
  have hy : y ∈ LinearMap.ker f ⊔ LinearMap.range f := by rw [hsup]; trivial
  obtain ⟨k, hk, w, ⟨z, rfl⟩, hkw⟩ := Submodule.mem_sup.1 hy
  exact ⟨k, z, by simpa [f] using hk, by simpa [f] using hkw.symm⟩

private theorem tendsto_res_vec (h : IsSymmPSD A) {k z : Fin d → ℝ} (hk : A *ᵥ k = 0) :
    Tendsto (fun m : ℕ => resolvent A m *ᵥ (k + A *ᵥ z)) atTop (𝓝 k) := by
  have heq : ∀ m : ℕ, resolvent A m *ᵥ (k + A *ᵥ z) =
      k + (((m : ℝ) + 1)⁻¹) • (z - resolvent A m *ᵥ z) := fun m => by
    rw [mulVec_add, res_mulVec_fixed h m hk, res_mulVec_range h m]
  simp_rw [heq]
  rw [tendsto_pi_nhds]
  intro i
  have hC : ∀ m : ℕ, |(resolvent A m *ᵥ z) i| ≤ Real.sqrt (z ⬝ᵥ z) := fun m => by
    apply Real.abs_le_sqrt
    calc ((resolvent A m *ᵥ z) i) ^ 2 ≤ (resolvent A m *ᵥ z) ⬝ᵥ (resolvent A m *ᵥ z) := by
          rw [dotProduct]
          exact Finset.single_le_sum (f := fun j => (resolvent A m *ᵥ z) j * (resolvent A m *ᵥ z) j)
            (fun j _ => mul_self_nonneg _) (Finset.mem_univ i) |>.trans_eq' (by ring)
      _ ≤ z ⬝ᵥ z := res_bound h m z
  have hlim : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹ * (|z i| + Real.sqrt (z ⬝ᵥ z))) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (|z i| + Real.sqrt (z ⬝ᵥ z))
    simpa only [one_div, zero_mul] using this
  have h0 : Tendsto (fun m : ℕ => (k + (((m : ℝ) + 1)⁻¹) • (z - resolvent A m *ᵥ z)) i - k i)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hlim
    intro m
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left,
      Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1)⁻¹)]
    gcongr
    exact (abs_sub _ _).trans (add_le_add le_rfl (hC m))
  have h1 := h0.add_const (k i)
  rw [zero_add] at h1
  exact h1.congr fun m => sub_add_cancel _ _

/-- For a symmetric positive semidefinite matrix `A`, the
resolvents `((m+1) A + I)⁻¹` converge to a symmetric idempotent matrix with range `ker A`, i.e.
the orthogonal projection onto `ker A`. -/
theorem IsSymmPSD.exists_resolvent_limit (h : IsSymmPSD A) :
    ∃ Q : Matrix (Fin d) (Fin d) ℝ, Qᵀ = Q ∧ Q * Q = Q ∧
      LinearMap.range (Matrix.toLin' Q) = LinearMap.ker (Matrix.toLin' A) ∧
      Tendsto (resolvent A) atTop (𝓝 Q) := by
  have hcol : ∀ j : Fin d, ∃ q : Fin d → ℝ,
      Tendsto (fun m : ℕ => resolvent A m *ᵥ (Pi.single j 1)) atTop (𝓝 q) := fun j => by
    obtain ⟨k, z, hk, hy⟩ := h.exists_decomp (Pi.single j 1)
    exact ⟨k, by rw [hy]; exact tendsto_res_vec h hk⟩
  choose q hq using hcol
  have hQ : Tendsto (resolvent A) atTop (𝓝 (Matrix.of fun i j => q j i)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have := (tendsto_pi_nhds.1 (hq j)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  set Q : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => q j i with hQdef
  have hQy : ∀ k z, A *ᵥ k = 0 → Q *ᵥ (k + A *ᵥ z) = k := fun k z hk => by
    have h1 : Tendsto (fun m : ℕ => resolvent A m *ᵥ (k + A *ᵥ z)) atTop (𝓝 (Q *ᵥ (k + A *ᵥ z))) :=
      ((Continuous.matrix_mulVec continuous_id continuous_const).tendsto Q).comp hQ
    exact tendsto_nhds_unique h1 (tendsto_res_vec h hk)
  have hfix : ∀ k, A *ᵥ k = 0 → Q *ᵥ k = k := fun k hk => by
    simpa using hQy k 0 hk
  have hQr : ∀ y, ∃ k, A *ᵥ k = 0 ∧ Q *ᵥ y = k := fun y => by
    obtain ⟨k, z, hk, rfl⟩ := h.exists_decomp y
    exact ⟨k, hk, hQy k z hk⟩
  refine ⟨Q, ?_, ?_, ?_, hQ⟩
  · have h1 : Tendsto (fun m : ℕ => (resolvent A m)ᵀ) atTop (𝓝 Qᵀ) :=
      ((Continuous.matrix_transpose continuous_id).tendsto Q).comp hQ
    have h2 : (fun m : ℕ => (resolvent A m)ᵀ) = resolvent A := by
      funext m
      rw [resolvent, transpose_nonsing_inv]
      simp [transpose_add, transpose_smul, h.symm]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hQ
  · apply matrix_ext_mulVec
    intro y
    obtain ⟨k, hk, hy⟩ := hQr y
    rw [← mulVec_mulVec, hy, hfix k hk]
  · ext y
    simp only [LinearMap.mem_range, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, hk, hx⟩ := hQr x
      rw [hx]; exact hk
    · intro hy
      exact ⟨y, hfix y hy⟩

/-- The orthogonal projection matrix onto `ker A` (the limit of the resolvents). -/
noncomputable def kerProj (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  limUnder atTop (resolvent A)

theorem IsSymmPSD.tendsto_kerProj (h : IsSymmPSD A) : Tendsto (resolvent A) atTop (𝓝 (kerProj A)) := by
  obtain ⟨Q, -, -, -, hQ⟩ := h.exists_resolvent_limit
  rw [kerProj, hQ.limUnder_eq]; exact hQ

theorem IsSymmPSD.kerProj_spec (h : IsSymmPSD A) :
    (kerProj A)ᵀ = kerProj A ∧ kerProj A * kerProj A = kerProj A ∧
      LinearMap.range (Matrix.toLin' (kerProj A)) = LinearMap.ker (Matrix.toLin' A) := by
  obtain ⟨Q, h1, h2, h3, hQ⟩ := h.exists_resolvent_limit
  have : kerProj A = Q := by rw [kerProj, hQ.limUnder_eq]
  rw [this]; exact ⟨h1, h2, h3⟩

end AFree.Bundle
