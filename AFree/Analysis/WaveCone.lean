module

public import AFree.Defs
public import PDEFoundation.Ambient.Matrix

/-!
# The first-order wave cone and ellipticity

Closedness and homogeneity of the wave cone, and the ellipticity of `M_v = B_vᵀ B_v` for `v`
outside the cone for a first-order operator.
-/

@[expose] public section

open Matrix

namespace AFree

open PDE

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The matrix `B_v` with columns `A_ℓ v`. -/
def symbolColumns (A : Fin d → Matrix κ ι ℝ) (v : ι → ℝ) : Matrix κ (Fin d) ℝ :=
  fun k ℓ => (A ℓ *ᵥ v) k

/-- The matrix `M_v = B_vᵀ B_v`. -/
def ellipticMatrix (A : Fin d → Matrix κ ι ℝ) (v : ι → ℝ) : Mat d :=
  (symbolColumns A v)ᵀ * symbolColumns A v

omit [Fintype κ] in
theorem symbolColumns_mulVec (A : Fin d → Matrix κ ι ℝ) (v : ι → ℝ) (ξ : Vec d) :
    symbolColumns A v *ᵥ ξ = (∑ ℓ, ξ ℓ • A ℓ) *ᵥ v := by
  funext k
  simp only [symbolColumns, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype κ] in
theorem symbol_apply (A : Fin d → Matrix κ ι ℝ) (ξ : Vec d) (v : ι → ℝ) (k : κ) :
    ((∑ ℓ, ξ ℓ • A ℓ) *ᵥ v) k = ∑ ℓ, ∑ j, ξ ℓ * (A ℓ k j * v j) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The quadratic form of `M_v` is `|(Σ ξ_ℓ A_ℓ) v|²`. -/
theorem vecDot_ellipticMatrix (A : Fin d → Matrix κ ι ℝ) (v : ι → ℝ) (ξ : Vec d) :
    vecDot ξ (matVecMul (ellipticMatrix A v) ξ) = ∑ k, ((∑ ℓ, ξ ℓ • A ℓ) *ᵥ v) k ^ 2 := by
  rw [← symbolColumns_mulVec]
  have h : matVecMul (ellipticMatrix A v) ξ = (symbolColumns A v)ᵀ *ᵥ (symbolColumns A v *ᵥ ξ) := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [h]
  have : vecDot ξ ((symbolColumns A v)ᵀ *ᵥ (symbolColumns A v *ᵥ ξ)) =
      ξ ⬝ᵥ ((symbolColumns A v)ᵀ *ᵥ (symbolColumns A v *ᵥ ξ)) := rfl
  rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [dotProduct, sq]

theorem isSymm_ellipticMatrix (A : Fin d → Matrix κ ι ℝ) (v : ι → ℝ) :
    (ellipticMatrix A v).IsSymm := by
  unfold ellipticMatrix
  simp [Matrix.IsSymm, Matrix.transpose_mul]

theorem isCompact_unitSphere : IsCompact {ξ : Vec d | vecEuclideanNorm ξ = 1} := by
  have hc : Continuous fun ξ : Vec d => vecEuclideanNorm ξ := by
    unfold vecEuclideanNorm vecNormSq vecDot
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq hc continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := 1)).subset ?_
  intro ξ hξ
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_apply_le_vecEuclideanNorm ξ i).trans hξ.le

omit [Fintype κ] in
/-- The wave cone is closed. -/
theorem isClosed_waveConeFirstOrder (A : Fin d → Matrix κ ι ℝ) :
    IsClosed (waveConeFirstOrder A) := by
  set S : Set (Vec d) := {ξ : Vec d | vecEuclideanNorm ξ = 1} with hSdef
  have : CompactSpace S := isCompact_iff_compactSpace.1 isCompact_unitSphere
  have hcont : Continuous fun p : S × (ι → ℝ) => (∑ ℓ, (p.1 : Vec d) ℓ • A ℓ) *ᵥ p.2 := by
    refine continuous_pi fun k => ?_
    simp only [symbol_apply]
    refine continuous_finsetSum _ fun ℓ _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_apply ℓ).comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_const.mul ((continuous_apply j).comp continuous_snd))
  have hC : IsClosed {p : S × (ι → ℝ) | (∑ ℓ, (p.1 : Vec d) ℓ • A ℓ) *ᵥ p.2 = 0} :=
    isClosed_eq hcont continuous_const
  have himg := isClosedMap_snd_of_compactSpace _ hC
  convert himg using 1
  ext v
  constructor
  · rintro ⟨ξ, h1, h2⟩
    exact ⟨(⟨ξ, h1⟩, v), h2, rfl⟩
  · rintro ⟨⟨⟨ξ, h1⟩, w⟩, h2, rfl⟩
    exact ⟨ξ, h1, h2⟩

omit [Fintype κ] in
/-- The wave cone is a cone: closed under real scalar multiplication. -/
theorem smul_mem_waveConeFirstOrder (A : Fin d → Matrix κ ι ℝ) {v : ι → ℝ}
    (hv : v ∈ waveConeFirstOrder A) (t : ℝ) : t • v ∈ waveConeFirstOrder A := by
  obtain ⟨ξ, h1, h2⟩ := hv
  exact ⟨ξ, h1, by rw [Matrix.mulVec_smul, h2, smul_zero]⟩

/-- For `v` outside the wave cone, `M_v` is `Λ`-elliptic. -/
theorem exists_elliptic_ellipticMatrix (A : Fin d → Matrix κ ι ℝ) {v : ι → ℝ}
    (hv : v ∉ waveConeFirstOrder A) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ (ellipticMatrix A v).IsSymm ∧ ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (ellipticMatrix A v) ξ) ∧
      vecDot ξ (matVecMul (ellipticMatrix A v) ξ) ≤ Λ * vecNormSq ξ := by
  set q : Vec d → ℝ := fun ξ => ∑ k, ((∑ ℓ, ξ ℓ • A ℓ) *ᵥ v) k ^ 2 with hq
  have hqe : ∀ ξ, vecDot ξ (matVecMul (ellipticMatrix A v) ξ) = q ξ :=
    fun ξ => vecDot_ellipticMatrix A v ξ
  have hq0 : ∀ ξ, 0 ≤ q ξ := fun ξ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hqcont : Continuous q := by
    refine continuous_finsetSum _ fun k _ => ?_
    refine Continuous.pow ?_ _
    simp only [symbol_apply]
    refine continuous_finsetSum _ fun ℓ _ => continuous_finsetSum _ fun j _ => ?_
    fun_prop
  have hhom : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ := by
    intro t ξ
    have : (∑ ℓ, (t • ξ) ℓ • A ℓ) = t • ∑ ℓ, ξ ℓ • A ℓ := by
      rw [Finset.smul_sum]; simp [smul_smul]
    change ∑ k, ((∑ ℓ, (t • ξ) ℓ • A ℓ) *ᵥ v) k ^ 2 = t ^ 2 * ∑ k, ((∑ ℓ, ξ ℓ • A ℓ) *ᵥ v) k ^ 2
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_pow]
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℝ, 0 < c ∧ ∀ ξ : Vec d, vecEuclideanNorm ξ = 1 → c ≤ q ξ := by
    rcases (Set.eq_empty_or_nonempty {ξ : Vec d | vecEuclideanNorm ξ = 1}) with h | h
    · exact ⟨1, one_pos, fun ξ hξ => absurd (h ▸ hξ : ξ ∈ (∅ : Set (Vec d))) (by simp)⟩
    · obtain ⟨x, hx, hmin⟩ := isCompact_unitSphere.exists_isMinOn h hqcont.continuousOn
      refine ⟨q x, lt_of_le_of_ne (hq0 x) fun h0 => hv ⟨x, hx, ?_⟩, fun ξ hξ => hmin hξ⟩
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).1 h0.symm
      funext k
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (this k (Finset.mem_univ k))
  set C : ℝ := ∑ k, ∑ ℓ, (symbolColumns A v k ℓ) ^ 2 with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun ℓ _ => sq_nonneg _
  have hup : ∀ ξ, q ξ ≤ C * vecNormSq ξ := by
    intro ξ
    have hqk : q ξ = ∑ k, (∑ ℓ, symbolColumns A v k ℓ * ξ ℓ) ^ 2 := by
      change ∑ k, ((∑ ℓ, ξ ℓ • A ℓ) *ᵥ v) k ^ 2 = _
      simp only [← symbolColumns_mulVec]
      rfl
    rw [hqk, hC, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [vecNormSq_eq_sum_sq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hlow : ∀ ξ, c * vecNormSq ξ ≤ q ξ := by
    intro ξ
    by_cases h0 : ξ = 0
    · subst h0; simp [vecNormSq, vecDot, hq0]
    · have hn : 0 < vecEuclideanNorm ξ := vecEuclideanNorm_pos_iff.2 h0
      have h1 : vecEuclideanNorm ((vecEuclideanNorm ξ)⁻¹ • ξ) = 1 := by
        rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
      have := hcS _ h1
      have h2 : q ξ = vecEuclideanNorm ξ ^ 2 * q ((vecEuclideanNorm ξ)⁻¹ • ξ) := by
        rw [hhom, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne']; simp
      rw [h2, ← vecEuclideanNorm_sq]
      exact mul_comm c _ ▸ mul_le_mul_of_nonneg_left this (sq_nonneg _)
  refine ⟨max 1 (max c⁻¹ C), le_max_left _ _, isSymm_ellipticMatrix A v, fun ξ => ?_⟩
  have hΛ : 0 < max 1 (max c⁻¹ C) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hN := vecNormSq_nonneg ξ
  rw [hqe]
  refine ⟨?_, (hup ξ).trans (mul_le_mul_of_nonneg_right
    ((le_max_right _ _).trans' (le_max_right _ _)) hN)⟩
  have : (max 1 (max c⁻¹ C))⁻¹ ≤ c :=
    (inv_le_comm₀ hΛ hc).2 ((le_max_left _ _).trans (le_max_right _ _))
  exact (mul_le_mul_of_nonneg_right this hN).trans (hlow ξ)

omit [Fintype κ] in
/-- The wave cone is the set of `v` annihilated by `Σ ξ_ℓ A_ℓ` for some `ξ ≠ 0`
(the unit-sphere normalisation is immaterial by homogeneity). -/
theorem mem_waveConeFirstOrder_iff_exists_ne_zero (A : Fin d → Matrix κ ι ℝ) (v : ι → ℝ) :
    v ∈ waveConeFirstOrder A ↔ ∃ ξ : Vec d, ξ ≠ 0 ∧ (∑ ℓ, ξ ℓ • A ℓ) *ᵥ v = 0 := by
  constructor
  · rintro ⟨ξ, h1, h2⟩
    refine ⟨ξ, fun h0 => ?_, h2⟩
    subst h0
    simp [vecEuclideanNorm, vecNormSq, vecDot] at h1
  · rintro ⟨ξ, h0, h2⟩
    have hn : 0 < vecEuclideanNorm ξ := vecEuclideanNorm_pos_iff.2 h0
    refine ⟨(vecEuclideanNorm ξ)⁻¹ • ξ, ?_, ?_⟩
    · rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    · have : (∑ ℓ, ((vecEuclideanNorm ξ)⁻¹ • ξ) ℓ • A ℓ) =
          (vecEuclideanNorm ξ)⁻¹ • ∑ ℓ, ξ ℓ • A ℓ := by
        rw [Finset.smul_sum]; simp [smul_smul]
      rw [this, Matrix.smul_mulVec, h2, smul_zero]

end AFree
