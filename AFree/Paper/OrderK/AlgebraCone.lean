module

public import AFree.Paper.OrderK.HarmonicSymbols
public import AFree.Analysis.WaveCone
public import AFree.Measure.PolarFacts

/-!
# Properties of the order-`k` wave cone

The cone is closed and homogeneous, the
ellipticity bound (iii') of [DPR, Section 2.3], and the relative closedness of the variable-coefficient cone, hence
Borel measurability of the bad set.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The matrix `𝔸_k(ξ) = Σ_{|α|=k} ξ^α A_α`. -/
def symbolK (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (ξ : Vec d) : Matrix κ ι ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, ξ i ^ α i) • A α

omit [Fintype κ] in
theorem symbA_eq (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ) (ξ : Vec d) :
    symbA k A P₀ ξ = symbolK k A ξ *ᵥ P₀ := rfl

omit [Fintype κ] in
theorem isClosed_setOf_mem_waveCone {X : Type*} [TopologicalSpace X] (k : ℕ)
    (B : X → (Fin d → ℕ) → Matrix κ ι ℝ)
    (hB : ∀ α ∈ Finset.Nat.antidiagonalTuple d k, Continuous fun x => B x α) :
    IsClosed {p : X × (ι → ℝ) | p.2 ∈ waveCone k (B p.1)} := by
  set S : Set (Vec d) := {ξ : Vec d | vecEuclideanNorm ξ = 1} with hS
  have : CompactSpace S := isCompact_iff_compactSpace.1 isCompact_unitSphere
  have hcont : Continuous fun q : (X × (ι → ℝ)) × S =>
      symbolK k (B q.1.1) (q.2 : Vec d) *ᵥ q.1.2 := by
    refine Continuous.matrix_mulVec ?_ (continuous_snd.comp continuous_fst)
    unfold symbolK
    refine continuous_finsetSum _ fun α hα => ?_
    have h1 : Continuous fun q : (X × (ι → ℝ)) × S => ∏ i, (q.2 : Vec d) i ^ α i :=
      continuous_finsetProd _ fun i _ =>
        (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd).pow _
    have h2 : Continuous fun q : (X × (ι → ℝ)) × S => B q.1.1 α :=
      (hB α hα).comp (continuous_fst.comp continuous_fst)
    exact h1.smul h2
  have hC : IsClosed {q : (X × (ι → ℝ)) × S | symbolK k (B q.1.1) (q.2 : Vec d) *ᵥ q.1.2 = 0} :=
    isClosed_eq hcont continuous_const
  have himg := isClosedMap_fst_of_compactSpace (X := X × (ι → ℝ)) (Y := S) _ hC
  convert himg using 1
  ext p
  constructor
  · rintro ⟨ξ, h1, h2⟩
    exact ⟨(p, ⟨ξ, h1⟩), h2, rfl⟩
  · rintro ⟨⟨p', ⟨ξ, h1⟩⟩, h2, rfl⟩
    exact ⟨ξ, h1, h2⟩

omit [Fintype ι] [Fintype κ] in
theorem symbolK_smul (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (t : ℝ) (ξ : Vec d) :
    symbolK k A (t • ξ) = t ^ k • symbolK k A ξ := by
  unfold symbolK
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hα
  have : ∏ i, (t • ξ) i ^ α i = t ^ k * ∏ i, ξ i ^ α i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [hα]
  rw [this, smul_smul]

theorem exists_ellipticity_symbA (hd : 0 < d) {k : ℕ} (A : (Fin d → ℕ) → Matrix κ ι ℝ)
    {P₀ : ι → ℝ} (hP : P₀ ∉ waveCone k A) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Vec d, c * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ) := by
  set S : Set (Vec d) := {ξ : Vec d | vecEuclideanNorm ξ = 1} with hS
  have hSne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
    simp [hS, vecEuclideanNorm, vecNormSq, vecDot, Pi.single_apply]
  have hcont : Continuous fun ξ : Vec d => piEuclideanNorm (symbA k A P₀ ξ) := by
    refine continuous_piEuclideanNorm.comp ?_
    refine Continuous.matrix_mulVec ?_ continuous_const
    exact continuous_finsetSum _ fun α _ => Continuous.smul
      (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _) continuous_const
  obtain ⟨x, hx, hmin⟩ := isCompact_unitSphere.exists_isMinOn hSne hcont.continuousOn
  have hpos : 0 < piEuclideanNorm (symbA k A P₀ x) := by
    refine lt_of_le_of_ne (piEuclideanNorm_nonneg _) fun h0 => hP ⟨x, hx, ?_⟩
    have := (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => mul_self_nonneg _)).1 h0.symm
    funext i
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg _)).1 this i
      (Finset.mem_univ i)
    exact mul_self_eq_zero.1 h2
  refine ⟨_, hpos, fun ξ => ?_⟩
  by_cases h0 : ξ = 0
  · subst h0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hconst : ∀ ξ : Vec d, symbA 0 A P₀ ξ = symbA 0 A P₀ x := fun ξ => by
        simp [symbA, Finset.Nat.antidiagonalTuple_zero_right]
      simp [hconst]
    · have hz : vecEuclideanNorm (0 : Vec d) = 0 := by simp [vecEuclideanNorm, vecNormSq, vecDot]
      rw [hz, zero_pow hk.ne', mul_zero]
      exact piEuclideanNorm_nonneg _
  · have hn : 0 < vecEuclideanNorm ξ := vecEuclideanNorm_pos_iff.2 h0
    have h1 : vecEuclideanNorm ((vecEuclideanNorm ξ)⁻¹ • ξ) = 1 := by
      rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    have hm := hmin (show (vecEuclideanNorm ξ)⁻¹ • ξ ∈ S from h1)
    have hξ : ξ = vecEuclideanNorm ξ • ((vecEuclideanNorm ξ)⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hsc : piEuclideanNorm (symbA k A P₀ ξ) =
        vecEuclideanNorm ξ ^ k *
          piEuclideanNorm (symbA k A P₀ ((vecEuclideanNorm ξ)⁻¹ • ξ)) := by
      conv_lhs => rw [hξ]
      rw [symbA_eq, symbolK_smul, Matrix.smul_mulVec, ← symbA_eq, piEuclideanNorm_smul,
        abs_of_pos (pow_pos hn k)]
    rw [hsc, mul_comm]
    exact mul_le_mul_of_nonneg_left hm (pow_nonneg hn.le _)

/-- (a) The cone is closed and invariant under real scalars, (b) the ellipticity bound
`|𝔸_k(ξ) P₀| ≥ c |ξ|^k` for `P₀ ∉ Λ` (`d ≥ 1`), (c) the variable-coefficient set
`{(x,v) : v ∈ Λ_{A(x)}}` is relatively closed in `Ω' × ℝ^ι`, and the bad set of a Borel `P` is
Borel (`Ω'` open, the `A_α`, `|α| = k`, continuous on `Ω'`). -/
theorem lem_conek (hd : 0 < d) (k : ℕ) :
    (∀ A : (Fin d → ℕ) → Matrix κ ι ℝ, IsClosed (waveCone k A) ∧
      ∀ v ∈ waveCone k A, ∀ t : ℝ, t • v ∈ waveCone k A) ∧
    (∀ (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ), P₀ ∉ waveCone k A →
      ∃ c : ℝ, 0 < c ∧ ∀ ξ : Vec d,
        c * vecEuclideanNorm ξ ^ k ≤ piEuclideanNorm (symbA k A P₀ ξ)) ∧
    (∀ (Ω' : Set (Vec d)) (A : (Fin d → ℕ) → Vec d → Matrix κ ι ℝ), IsOpen Ω' →
      (∀ α ∈ Finset.Nat.antidiagonalTuple d k, ContinuousOn (A α) Ω') →
      IsClosed {p : Ω' × (ι → ℝ) | p.2 ∈ waveCone k (fun α => A α p.1)} ∧
      ∀ P : Vec d → ι → ℝ, Measurable P →
        MeasurableSet {x | x ∈ Ω' ∧ P x ∉ waveCone k (fun α => A α x)}) := by
  refine ⟨fun A => ⟨?_, ?_⟩, fun A P₀ hP => exists_ellipticity_symbA hd A hP, ?_⟩
  · have := isClosed_setOf_mem_waveCone (X := Unit) k (fun _ => A) (fun α _ => continuous_const)
    have h := this.preimage (f := fun v : ι → ℝ => ((), v))
      (continuous_const.prodMk continuous_id)
    exact h
  · rintro v ⟨ξ, h1, h2⟩ t
    exact ⟨ξ, h1, by rw [Matrix.mulVec_smul, h2, smul_zero]⟩
  · intro Ω' A hΩ hA
    have hZ : IsClosed {p : Ω' × (ι → ℝ) | p.2 ∈ waveCone k (fun α => A α p.1)} :=
      isClosed_setOf_mem_waveCone (X := Ω') k (fun x α => A α x) fun α hα =>
        (hA α hα).domRestrict
    refine ⟨hZ, fun P hP => ?_⟩
    have hg : Measurable fun x : Ω' => (x, P x) :=
      measurable_id.prodMk (hP.comp measurable_subtype_coe)
    have ht : MeasurableSet ((fun x : Ω' => (x, P x)) ⁻¹'
        {p : Ω' × (ι → ℝ) | p.2 ∈ waveCone k (fun α => A α p.1)}ᶜ) :=
      hg hZ.measurableSet.compl
    have := MeasurableSet.subtype_image hΩ.measurableSet ht
    convert this using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · rintro ⟨hx, hP'⟩
      exact ⟨⟨x, hx⟩, hP', rfl⟩
    · rintro ⟨⟨y, hy⟩, hP', rfl⟩
      exact ⟨hy, hP'⟩

end

end AFree
