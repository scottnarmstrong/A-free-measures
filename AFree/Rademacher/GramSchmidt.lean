module

public import AFree.Rademacher.Dot
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Gram--Schmidt on `Vec d` is continuous

Gram--Schmidt for the
Euclidean dot product `vecDot` of a sequence `a : ℕ → Vec d`; only the first `p` terms matter.
-/

@[expose] public section

open PDE Filter Topology

namespace AFree.Rademacher

variable {d : ℕ}

/-- The Gram--Schmidt vectors `b_k = u_k / |u_k|` of a sequence `a`, where
`u_k = a_k - ∑_{l<k} (a_k · b_l) b_l`. -/
noncomputable def gsB (a : ℕ → Vec d) (k : ℕ) : Vec d :=
  (vecEuclideanNorm (a k - ∑ l : Fin k, vecDot (a k) (gsB a l) • gsB a l))⁻¹ •
    (a k - ∑ l : Fin k, vecDot (a k) (gsB a l) • gsB a l)
termination_by k
decreasing_by all_goals exact l.2

/-- The unnormalised Gram--Schmidt vectors `u_k = a_k - ∑_{l<k} (a_k · b_l) b_l`. -/
noncomputable def gsU (a : ℕ → Vec d) (k : ℕ) : Vec d :=
  a k - ∑ l ∈ Finset.range k, vecDot (a k) (gsB a l) • gsB a l

theorem gsB_eq (a : ℕ → Vec d) (k : ℕ) :
    gsB a k = (vecEuclideanNorm (gsU a k))⁻¹ • gsU a k := by
  rw [gsB]
  simp only [gsU, Fin.sum_univ_eq_sum_range (fun l => vecDot (a k) (gsB a l) • gsB a l) k]

theorem linearIndependent_mono {a : ℕ → Vec d} {p q : ℕ} (h : q ≤ p)
    (ha : LinearIndependent ℝ (fun k : Fin p => a k)) :
    LinearIndependent ℝ (fun k : Fin q => a k) :=
  ha.comp (Fin.castLE h) (Fin.castLE_injective h)

theorem notMem_span_of_linearIndependent {a : ℕ → Vec d} {p q : ℕ} (hq : q < p)
    (ha : LinearIndependent ℝ (fun k : Fin p => a k)) :
    a q ∉ Submodule.span ℝ (a '' Set.Iio q) := by
  have h := ha.notMem_span_image (s := {k : Fin p | (k : ℕ) < q}) (x := ⟨q, hq⟩) (by simp)
  have himg : (fun k : Fin p => a k) '' {k : Fin p | (k : ℕ) < q} = a '' Set.Iio q := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl.trans hq⟩, hl, rfl⟩
  rw [himg] at h
  exact h

private theorem gs_induct {a : ℕ → Vec d} {p : ℕ}
    (ha : LinearIndependent ℝ (fun k : Fin p => a k)) :
    ∀ q, q ≤ p → (∀ k < q, gsU a k ≠ 0) ∧
      (∀ k < q, ∀ l < q, vecDot (gsB a k) (gsB a l) = if k = l then 1 else 0) ∧
      Submodule.span ℝ (gsB a '' Set.Iio q) = Submodule.span ℝ (a '' Set.Iio q) := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hqp
    obtain ⟨hne, horth, hspan⟩ := ih (Nat.le_of_succ_le hqp)
    have hbmem : ∀ l < q, gsB a l ∈ Submodule.span ℝ (a '' Set.Iio q) := fun l hl =>
      hspan ▸ Submodule.subset_span ⟨l, hl, rfl⟩
    have hsum_mem : (∑ l ∈ Finset.range q, vecDot (a q) (gsB a l) • gsB a l) ∈
        Submodule.span ℝ (a '' Set.Iio q) :=
      Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (hbmem l (Finset.mem_range.1 hl))
    have hu : gsU a q ≠ 0 := by
      intro h
      have h' : a q = ∑ l ∈ Finset.range q, vecDot (a q) (gsB a l) • gsB a l := by
        unfold gsU at h; exact sub_eq_zero.1 h
      exact notMem_span_of_linearIndependent (Nat.lt_of_succ_le hqp) ha (h' ▸ hsum_mem)
    have hperp : ∀ l < q, vecDot (gsU a q) (gsB a l) = 0 := by
      intro l hl
      unfold gsU
      rw [vecDot_sub_left, vecDot_sum_left]
      simp only [vecDot_smul_left]
      have : ∀ j ∈ Finset.range q, vecDot (a q) (gsB a j) * vecDot (gsB a j) (gsB a l) =
          if j = l then vecDot (a q) (gsB a l) else 0 := by
        intro j hj
        rw [horth j (Finset.mem_range.1 hj) l hl]
        by_cases h : j = l
        · subst h; simp
        · simp [h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range q) l]
      simp [hl]
    have hnorm : vecEuclideanNorm (gsU a q) ≠ 0 := fun h => hu (vecEuclideanNorm_eq_zero_iff.1 h)
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact hne k h
      · exact h ▸ hu
    · intro k hk l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk' <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | hl'
      · exact horth k hk' l hl'
      · rw [hl', gsB_eq a q, vecDot_smul_right, vecDot_comm (gsB a k), hperp k hk']
        simp [hk'.ne]
      · rw [hk', gsB_eq a q, vecDot_smul_left, hperp l hl']
        simp [hl'.ne']
      · rw [hk', hl', gsB_eq a q, vecDot_smul_left, vecDot_smul_right, vecDot_self]
        field_simp
        simp
    · have hbq : gsB a q = (vecEuclideanNorm (gsU a q))⁻¹ • gsU a q := gsB_eq a q
      have hnu : vecEuclideanNorm (gsU a q) • gsB a q = gsU a q := by
        rw [hbq, smul_inv_smul₀ hnorm]
      have hIio : Set.Iio (q + 1) = insert q (Set.Iio q) := by
        ext x; simp
      have hmono : Submodule.span ℝ (a '' Set.Iio q) ≤ Submodule.span ℝ (a '' Set.Iio (q + 1)) :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ q)))
      have haq : a q ∈ Submodule.span ℝ (a '' Set.Iio (q + 1)) :=
        Submodule.subset_span ⟨q, Nat.lt_succ_self q, rfl⟩
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨l, hl, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
        · exact hmono (hbmem l h)
        · subst h
          rw [hbq]
          refine Submodule.smul_mem _ _ ?_
          unfold gsU
          exact Submodule.sub_mem _ haq (hmono hsum_mem)
      · rw [Submodule.span_le]
        rintro _ ⟨l, hl, rfl⟩
        have hbm : ∀ j < q + 1, gsB a j ∈ Submodule.span ℝ (gsB a '' Set.Iio (q + 1)) :=
          fun j hj => Submodule.subset_span ⟨j, hj, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
        · have : a l ∈ Submodule.span ℝ (gsB a '' Set.Iio q) :=
            hspan ▸ Submodule.subset_span ⟨l, h, rfl⟩
          exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ q))) this
        · subst h
          have : a l = vecEuclideanNorm (gsU a l) • gsB a l +
              ∑ j ∈ Finset.range l, vecDot (a l) (gsB a j) • gsB a j := by
            rw [hnu]; unfold gsU; abel
          rw [this]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hbm l (Nat.lt_succ_self l)))
            (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
              (hbm j (Nat.lt_succ_of_lt (Finset.mem_range.1 hj))))

/-- The Gram--Schmidt vectors of the first `p` terms of a linearly independent sequence are
nonzero before normalisation. -/
theorem gsU_ne_zero {a : ℕ → Vec d} {p : ℕ} (ha : LinearIndependent ℝ (fun k : Fin p => a k))
    {k : ℕ} (hk : k < p) : gsU a k ≠ 0 :=
  (gs_induct ha p le_rfl).1 k hk

/-- The Gram--Schmidt vectors of a linearly independent `p`-tuple are orthonormal. -/
theorem gsB_orthonormal {a : ℕ → Vec d} {p : ℕ} (ha : LinearIndependent ℝ (fun k : Fin p => a k))
    {k l : ℕ} (hk : k < p) (hl : l < p) :
    vecDot (gsB a k) (gsB a l) = if k = l then 1 else 0 :=
  (gs_induct ha p le_rfl).2.1 k hk l hl

/-- Gram--Schmidt preserves the flag of spans. -/
theorem span_gsB {a : ℕ → Vec d} {p : ℕ} (ha : LinearIndependent ℝ (fun k : Fin p => a k))
    {q : ℕ} (hq : q ≤ p) :
    Submodule.span ℝ (gsB a '' Set.Iio q) = Submodule.span ℝ (a '' Set.Iio q) :=
  (gs_induct ha q hq).2.2

/-- Gram--Schmidt of an orthonormal tuple is the tuple itself. -/
theorem gsB_eq_self {a : ℕ → Vec d} {p : ℕ}
    (ha : ∀ k < p, ∀ l < p, vecDot (a k) (a l) = if k = l then 1 else 0) :
    ∀ k < p, gsB a k = a k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hu : gsU a k = a k := by
      unfold gsU
      have : ∀ l ∈ Finset.range k, vecDot (a k) (gsB a l) • gsB a l = 0 := by
        intro l hl
        have hl' := Finset.mem_range.1 hl
        rw [ih l hl' (hl'.trans hk), ha k hk l (hl'.trans hk)]
        simp [hl'.ne']
      rw [Finset.sum_eq_zero this, sub_zero]
    have h1 : vecEuclideanNorm (a k) = 1 := by
      have := ha k hk k hk
      simp only [ite_true, vecDot_self] at this
      have h0 := vecEuclideanNorm_nonneg (a k)
      nlinarith
    rw [gsB_eq, hu, h1]
    simp

/-- The set of linearly independent `p`-tuples is open. -/
theorem isOpen_linearIndependent (p : ℕ) :
    IsOpen {a : ℕ → Vec d | LinearIndependent ℝ (fun k : Fin p => a k)} :=
  (isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := Vec d) (ι := Fin p)).preimage
    (f := fun (a : ℕ → Vec d) (k : Fin p) => a k) (continuous_pi fun k => continuous_apply (k : ℕ))

private theorem gsB_continuousOn (k : ℕ) :
    ContinuousOn (fun a : ℕ → Vec d => gsB a k)
      {a | LinearIndependent ℝ (fun l : Fin (k + 1) => a l)} := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hsub : ∀ l < k, {a : ℕ → Vec d | LinearIndependent ℝ (fun j : Fin (k + 1) => a j)} ⊆
        {a | LinearIndependent ℝ (fun j : Fin (l + 1) => a j)} := fun l hl a ha =>
      linearIndependent_mono (Nat.succ_le_succ hl.le) ha
    have hU : ContinuousOn (fun a : ℕ → Vec d => gsU a k)
        {a | LinearIndependent ℝ (fun l : Fin (k + 1) => a l)} := by
      unfold gsU
      refine (continuous_apply k).continuousOn.sub (continuousOn_finsetSum _ fun l hl => ?_)
      have hb := (ih l (Finset.mem_range.1 hl)).mono (hsub l (Finset.mem_range.1 hl))
      have h1 := continuousOn_vecDot (f := fun a : ℕ → Vec d => a k) (g := fun a => gsB a l)
        (continuous_apply k).continuousOn hb
      exact h1.smul hb
    have hne : ∀ a ∈ {a : ℕ → Vec d | LinearIndependent ℝ (fun l : Fin (k + 1) => a l)},
        vecEuclideanNorm (gsU a k) ≠ 0 := fun a ha h =>
      gsU_ne_zero ha (Nat.lt_succ_self k) (vecEuclideanNorm_eq_zero_iff.1 h)
    exact (((continuousOn_vecEuclideanNorm hU).inv₀ hne).smul hU).congr fun a _ => gsB_eq a k

/-- Gram--Schmidt is continuous. For a linearly independent `p`-tuple
`a_0, …, a_{p-1}` of `ℝ^d`, with `u_k = a_k - ∑_{l<k} (a_k · b_l) b_l` and `b_k = u_k / |u_k|`:
`u_k ≠ 0`, `(b_k)` is orthonormal, `span(b_0..b_{q-1}) = span(a_0..a_{q-1})` for all `q`, the map
`(a_k) ↦ (b_k)` is continuous on the open set of independent `p`-tuples, and `b = a` when `a` is
already orthonormal. -/
theorem gram_schmidt (p : ℕ) :
    IsOpen {a : ℕ → Vec d | LinearIndependent ℝ (fun k : Fin p => a k)} ∧
    ContinuousOn (fun a : ℕ → Vec d => fun k : Fin p => gsB a k)
      {a | LinearIndependent ℝ (fun k : Fin p => a k)} ∧
    ∀ a : ℕ → Vec d, LinearIndependent ℝ (fun k : Fin p => a k) →
      (∀ k < p, gsU a k ≠ 0) ∧
      (∀ k < p, ∀ l < p, vecDot (gsB a k) (gsB a l) = if k = l then 1 else 0) ∧
      (∀ q ≤ p, Submodule.span ℝ (gsB a '' Set.Iio q) = Submodule.span ℝ (a '' Set.Iio q)) ∧
      ((∀ k < p, ∀ l < p, vecDot (a k) (a l) = if k = l then 1 else 0) →
        ∀ k < p, gsB a k = a k) :=
  ⟨isOpen_linearIndependent p,
    continuousOn_pi.2 fun k => (gsB_continuousOn k).mono fun _ ha =>
      linearIndependent_mono (Nat.succ_le_of_lt k.2) ha,
    fun _ ha => ⟨fun _ hk => gsU_ne_zero ha hk, fun _ hk _ hl => gsB_orthonormal ha hk hl,
      fun _ hq => span_gsB ha hq, fun h => gsB_eq_self h⟩⟩

end AFree.Rademacher
