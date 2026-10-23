module

public import AFree.Algebra.KVec.Interior

/-!
# [DPR, Theorem 1.10], "Equivalently"

The dimension of `ker ω`, the equivalence `v ⌟ ω = 0 ↔ v ∈ Λ_k(ker ω)`, and the interior product of a
`1`-vector.
-/

@[expose] public section

open Matrix PDE

namespace AFree

variable {d m : ℕ}

/-- The linear functional `w ↦ w · ω`. -/
noncomputable def covectorFunctional (ω : Vec d) : Vec d →ₗ[ℝ] ℝ :=
  ∑ i, ω i • LinearMap.proj i

theorem covectorKernel_eq_ker (ω : Vec d) :
    covectorKernel ω = LinearMap.ker (covectorFunctional ω) := by
  ext w
  simp [covectorKernel, covectorFunctional, vecDot, mul_comm]

/-- `ker ω` has dimension `d - 1` when `ω ≠ 0`. -/
theorem finrank_covectorKernel (ω : Vec d) (hω : ω ≠ 0) :
    Module.finrank ℝ (covectorKernel ω) = d - 1 := by
  obtain ⟨n, hn⟩ : ∃ n, ω n ≠ 0 := by
    by_contra h
    push Not at h
    exact hω (funext h)
  have hsurj : Function.Surjective (covectorFunctional ω) := by
    intro c
    refine ⟨Pi.single n (c / ω n), ?_⟩
    simp [covectorFunctional, Pi.single_apply]
    field_simp
  have hrange : LinearMap.range (covectorFunctional ω) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker (covectorFunctional ω)
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, ← covectorKernel_eq_ker] at h
  omega

/-- If `ω n ≠ 0`, `w ⌟ ω = 0`, and `w` vanishes on all indices not containing `n`, then `w = 0`. -/
theorem eq_zero_of_interiorProduct_eq_zero (ω : Vec d) (n : Fin d) (hn : ω n ≠ 0)
    (w : KVec d (m + 1)) (hw : interiorProduct w ω = 0)
    (hz : ∀ I : KIdx d (m + 1), n ∉ I.1 → w I = 0) : w = 0 := by
  ext I
  by_cases hnI : n ∈ I.1
  swap
  · exact hz I hnI
  have hJc : (I.1.erase n).card = m + 1 - 1 := by
    rw [Finset.card_erase_of_mem hnI, I.2]
  set J : KIdx d (m + 1 - 1) := ⟨I.1.erase n, hJc⟩ with hJ
  have h0 := congrFun hw J
  rw [interiorProduct_apply_of_one_le (Nat.le_add_left 1 m)] at h0
  have hnJ : n ∉ J.1 := by simp [hJ]
  rw [Finset.sum_eq_single (⟨n, hnJ⟩ : {j : Fin d // j ∉ J.1})] at h0
  · have hIeq : insert n J.1 = I.1 := Finset.insert_erase hnI
    have : w ⟨insert n J.1, card_insert_eq_of_one_le (Nat.le_add_left 1 m) J n hnJ⟩ = w I :=
      congrArg w (Subtype.ext hIeq)
    simp only at h0
    rw [this] at h0
    have hs : insertSign n J.1 ≠ 0 := pow_ne_zero _ (by norm_num)
    simpa [hn, hs] using h0
  · intro j _ hjn
    have hjn' : n ≠ j.1 := fun h => hjn (Subtype.ext h.symm)
    have : w ⟨insert j.1 J.1, card_insert_eq_of_one_le (Nat.le_add_left 1 m) J j.1 j.2⟩ = 0 := by
      apply hz
      simp [hJ, hjn']
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The generators `e_i - (ω_i / ω_n) e_n` of `ker ω`. -/
noncomputable def kernelGen (ω : Vec d) (n i : Fin d) : Vec d :=
  Pi.single i 1 - (ω i / ω n) • Pi.single n 1

theorem kernelGen_mem (ω : Vec d) (n : Fin d) (hn : ω n ≠ 0) (i : Fin d) :
    kernelGen ω n i ∈ covectorKernel ω := by
  show vecDot _ ω = 0
  simp [kernelGen, vecDot, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, hn]

/-- The vector `F_I = wedge (f_{I^↑ b})_b`. -/
noncomputable def kernelWedge (ω : Vec d) (n : Fin d) {k : ℕ} (I : KIdx d k) : KVec d k :=
  wedge fun b => kernelGen ω n (I.1.orderEmbOfFin I.2 b)

theorem kernelWedge_mem {k : ℕ} (ω : Vec d) (n : Fin d) (hn : ω n ≠ 0) (I : KIdx d k) :
    kernelWedge ω n I ∈ kvecSpan (covectorKernel ω) k :=
  Submodule.subset_span ⟨_, fun _ => kernelGen_mem ω n hn _, rfl⟩

/-- On indices `I'` avoiding `n`, `F_I` has coordinate `1` if `I' = I` and `0` otherwise. -/
theorem kernelWedge_apply {k : ℕ} (ω : Vec d) (n : Fin d) (I I' : KIdx d k) (hn : n ∉ I'.1) :
    kernelWedge ω n I I' = if I = I' then 1 else 0 := by
  have hM : wedgeMat I' (fun b => kernelGen ω n (I.1.orderEmbOfFin I.2 b)) =
      Matrix.of fun a b => if I'.1.orderEmbOfFin I'.2 a = I.1.orderEmbOfFin I.2 b then 1 else 0 := by
    ext a b
    have hne : I'.1.orderEmbOfFin I'.2 a ≠ n := fun h =>
      hn (h ▸ Finset.orderEmbOfFin_mem _ _ _)
    simp [wedgeMat, kernelGen, Pi.single_apply, hne]
  rw [kernelWedge, wedge_apply, hM]
  split_ifs with h
  · subst h
    have : (Matrix.of fun a b : Fin k =>
        if I.1.orderEmbOfFin I.2 a = I.1.orderEmbOfFin I.2 b then (1 : ℝ) else 0) = 1 := by
      ext a b
      simp [Matrix.one_apply, (I.1.orderEmbOfFin I.2).injective.eq_iff]
    rw [this, Matrix.det_one]
  · have : ∃ a, I'.1.orderEmbOfFin I'.2 a ∉ I.1 := by
      by_contra hcon
      push Not at hcon
      have hsub : I'.1 ⊆ I.1 := by
        intro x hx
        obtain ⟨a, rfl⟩ : x ∈ Set.range (I'.1.orderEmbOfFin I'.2) := by
          rw [Finset.range_orderEmbOfFin]; exact hx
        exact hcon a
      exact h (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [I.2, I'.2])).symm)
    obtain ⟨a, ha⟩ := this
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    have : I'.1.orderEmbOfFin I'.2 a ≠ I.1.orderEmbOfFin I.2 b := fun h' =>
      ha (h' ▸ Finset.orderEmbOfFin_mem _ _ _)
    simp [this]

/-- [DPR, Theorem 1.10], "Equivalently": for `k ≥ 1`, `ω ≠ 0`,
`v ⌟ ω = 0 ↔ v ∈ Λ_k(ker ω)`. -/
theorem equiv_interiorProduct_kvecSpan {k : ℕ} (hk : 1 ≤ k) (ω : Vec d) (hω : ω ≠ 0)
    (v : KVec d k) :
    interiorProduct v ω = 0 ↔ v ∈ kvecSpan (covectorKernel ω) k := by
  refine ⟨fun hv => ?_, interiorProduct_eq_zero_of_mem_kvecSpan hk ω v⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, ω n ≠ 0 := by
    by_contra h
    push Not at h
    exact hω (funext h)
  set T : Finset (KIdx d (m + 1)) := Finset.univ.filter fun I => n ∉ I.1 with hT
  set v' : KVec d (m + 1) := ∑ I ∈ T, v I • kernelWedge ω n I with hv'
  have hmem : v' ∈ kvecSpan (covectorKernel ω) (m + 1) :=
    Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (kernelWedge_mem ω n hn I)
  have hker : interiorProduct v' ω = 0 := by
    have : v' ∈ LinearMap.ker (interiorProductLM (m + 1) ω) := by
      refine Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ ?_
      exact interiorProduct_eq_zero_of_mem_kvecSpan hk ω _ (kernelWedge_mem ω n hn I)
    exact this
  have hv'apply : ∀ I' : KIdx d (m + 1), n ∉ I'.1 → v' I' = v I' := by
    intro I' hI'
    simp only [hv', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single I']
    · simp [kernelWedge_apply ω n I' I' hI']
    · intro I _ hne
      rw [kernelWedge_apply ω n I I' hI']
      simp [hne]
    · intro h
      exact absurd (by simpa [hT] using hI') h
  have hw : v - v' = 0 := by
    refine eq_zero_of_interiorProduct_eq_zero ω n hn (v - v') ?_ ?_
    · rw [show interiorProduct (v - v') ω = interiorProduct v ω - interiorProduct v' ω from
        map_sub (interiorProductLM (m + 1) ω) v v', hv, hker, sub_zero]
    · intro I hI
      simp [hv'apply I hI]
  rw [sub_eq_zero.mp hw]
  exact hmem

theorem vecDot_comm' (x y : Vec d) : vecDot x y = vecDot y x := by
  simp [vecDot, mul_comm]

/-- For a `1`-vector `v`, `(v ⌟ ω)(∅) = ω · kvecOneToVec v`, hence
`v ⌟ ω = 0 ↔ kvecOneToVec v · ω = 0`. -/
theorem oneip (v : KVec d 1) (ω : Vec d) :
    (∀ J : KIdx d (1 - 1), interiorProduct v ω J = vecDot ω (kvecOneToVec v)) ∧
      (interiorProduct v ω = 0 ↔ vecDot (kvecOneToVec v) ω = 0) := by
  have hJ : ∀ J : KIdx d (1 - 1), J.1 = ∅ := fun J =>
    Finset.card_eq_zero.mp (by simpa using J.2)
  have h1 : ∀ J : KIdx d (1 - 1), interiorProduct v ω J = vecDot ω (kvecOneToVec v) := by
    intro J
    unfold interiorProduct
    simp [hJ J, insertSign, vecDot, kvecOneToVec]
  refine ⟨h1, ?_⟩
  constructor
  · intro h
    have := h1 ⟨∅, by simp⟩
    rw [h] at this
    rw [vecDot_comm']
    exact this.symm
  · intro h
    ext J
    rw [h1 J, vecDot_comm']
    exact h

end AFree
