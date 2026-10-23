module

public import AFree.Algebra.KVec.Basic

/-!
# Interior product of a wedge

Sorting of an inserted index, Laplace expansion, the interior product of a wedge, and `Λ_k(ker ω) ⊆ ker (· ⌟ ω)`.
-/

@[expose] public section

open Matrix PDE

namespace AFree

variable {d m : ℕ}

theorem sort_apply_pos (J : Finset (Fin d)) (hJ : J.card = m) (j : Fin d) (hI : (insert j J).card = m + 1) :
    (insert j J).orderEmbOfFin hI ⟨(J.filter (· < j)).card, by
      have := Finset.card_le_card (Finset.filter_subset (· < j) J)
      omega⟩ = j := by
  set I := insert j J with hIdef
  have hjI : j ∈ I := Finset.mem_insert_self _ _
  obtain ⟨q, hq⟩ : ∃ q, I.orderEmbOfFin hI q = j := by
    have : j ∈ Set.range (I.orderEmbOfFin hI) := by rw [Finset.range_orderEmbOfFin]; exact hjI
    exact this
  have hset : I.filter (· < j) = (Finset.univ.filter (· < q)).image (I.orderEmbOfFin hI) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hx, hxj⟩
      obtain ⟨a, rfl⟩ : x ∈ Set.range (I.orderEmbOfFin hI) := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      refine ⟨a, ?_, rfl⟩
      rw [← hq] at hxj
      exact (I.orderEmbOfFin hI).lt_iff_lt.mp hxj
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Finset.orderEmbOfFin_mem _ _ _, ?_⟩
      rw [← hq]
      exact (I.orderEmbOfFin hI).lt_iff_lt.mpr ha
  have hcard : (I.filter (· < j)).card = q := by
    rw [hset, Finset.card_image_of_injective _ (I.orderEmbOfFin hI).injective]
    have : Finset.univ.filter (· < q) = Finset.Iio q := by ext; simp
    rw [this, Fin.card_Iio]
  have hJc : (I.filter (· < j)) = J.filter (· < j) := by
    rw [hIdef, Finset.filter_insert]; simp
  have : q = ⟨(J.filter (· < j)).card, by
      have := Finset.card_le_card (Finset.filter_subset (· < j) J)
      omega⟩ := by
    apply Fin.ext; simp only; rw [← hJc, hcard]
  rw [← this]; exact hq

/-- Sorting `J ∪ {j}`: with `p = #{i ∈ J : i < j}`, `I^↑(p) = j` and
`I^↑ ∘ p.succAbove = J^↑`. (The hypothesis `j ∉ J` is implicit in
`(insert j J).card = m + 1`.) -/
theorem sort (J : Finset (Fin d)) (hJ : J.card = m) (j : Fin d)
    (hI : (insert j J).card = m + 1) :
    (insert j J).orderEmbOfFin hI ⟨(J.filter (· < j)).card, by
      have := Finset.card_le_card (Finset.filter_subset (· < j) J)
      omega⟩ = j ∧
    ∀ a : Fin m, (insert j J).orderEmbOfFin hI
      (Fin.succAbove ⟨(J.filter (· < j)).card, by
        have := Finset.card_le_card (Finset.filter_subset (· < j) J)
        omega⟩ a) = J.orderEmbOfFin hJ a := by
  refine ⟨sort_apply_pos J hJ j hI, ?_⟩
  set p : Fin (m + 1) := ⟨(J.filter (· < j)).card, by
      have := Finset.card_le_card (Finset.filter_subset (· < j) J)
      omega⟩ with hp
  have hpj := sort_apply_pos J hJ j hI
  rw [← hp] at hpj
  have hmem : ∀ a : Fin m, (insert j J).orderEmbOfFin hI (p.succAbove a) ∈ J := by
    intro a
    have h1 := Finset.orderEmbOfFin_mem (insert j J) hI (p.succAbove a)
    rcases Finset.mem_insert.mp h1 with h | h
    · exfalso
      exact Fin.succAbove_ne p a (((insert j J).orderEmbOfFin hI).injective (h.trans hpj.symm))
    · exact h
  have hmono : StrictMono fun a : Fin m => (insert j J).orderEmbOfFin hI (p.succAbove a) :=
    ((insert j J).orderEmbOfFin hI).strictMono.comp (Fin.strictMono_succAbove p)
  intro a
  exact congrFun (Finset.orderEmbOfFin_unique hJ hmem hmono) a

/-- Laplace expansion step in the interior product of a wedge, case `j ∉ J`. -/
theorem insertSign_mul_wedge (u : Fin (m + 1) → Vec d) (J : Finset (Fin d)) (hJ : J.card = m)
    (j : Fin d) (hI : (insert j J).card = m + 1) :
    insertSign j J * wedge u ⟨insert j J, hI⟩ =
      ∑ b : Fin (m + 1), (-1) ^ (b : ℕ) * u b j * wedge (u ∘ b.succAbove) ⟨J, hJ⟩ := by
  set p : Fin (m + 1) := ⟨(J.filter (· < j)).card, by
      have := Finset.card_le_card (Finset.filter_subset (· < j) J)
      omega⟩ with hp
  obtain ⟨h1, h2⟩ := sort J hJ j hI
  rw [← hp] at h1 h2
  rw [wedge_apply, Matrix.det_succ_row _ p, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hM : (wedgeMat ⟨insert j J, hI⟩ u) p b = u b j := by
    simp only [wedgeMat, Matrix.of_apply]; rw [h1]
  have hsub : (wedgeMat ⟨insert j J, hI⟩ u).submatrix p.succAbove b.succAbove =
      wedgeMat ⟨J, hJ⟩ (u ∘ b.succAbove) := by
    ext a c
    simp only [wedgeMat, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply]
    rw [h2]
  rw [hM, hsub, wedge_apply]
  have hs : insertSign j J = (-1) ^ (p : ℕ) := rfl
  rw [hs]
  have : ((-1 : ℝ) ^ (p : ℕ)) * (-1) ^ ((p : ℕ) + (b : ℕ)) = (-1) ^ (b : ℕ) := by
    rw [← pow_add, show (p : ℕ) + ((p : ℕ) + (b : ℕ)) = 2 * (p : ℕ) + b by ring, pow_add, pow_mul]
    simp
  rw [← mul_assoc, ← mul_assoc, this]

/-- Laplace expansion along a repeated row, case `j ∈ J`. -/
theorem sum_wedge_eq_zero_of_mem (u : Fin (m + 1) → Vec d) (J : Finset (Fin d)) (hJ : J.card = m)
    (j : Fin d) (hj : j ∈ J) :
    ∑ b : Fin (m + 1), (-1) ^ (b : ℕ) * u b j * wedge (u ∘ b.succAbove) ⟨J, hJ⟩ = 0 := by
  set N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun a b => u b ((Fin.cons j (J.orderEmbOfFin hJ) : Fin (m + 1) → Fin d) a) with hN
  obtain ⟨a0, ha0⟩ : j ∈ Set.range (J.orderEmbOfFin hJ) := by
    rw [Finset.range_orderEmbOfFin]; exact hj
  have hdet : N.det = 0 := by
    refine Matrix.det_zero_of_row_eq (Fin.succ_ne_zero a0).symm ?_
    ext c
    simp [hN, ha0]
  rw [Matrix.det_succ_row N 0] at hdet
  rw [← hdet]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsub : N.submatrix (0 : Fin (m + 1)).succAbove b.succAbove =
      wedgeMat ⟨J, hJ⟩ (u ∘ b.succAbove) := by
    ext a c
    simp [hN, wedgeMat, Fin.succAbove_zero]
  rw [hsub, wedge_apply]
  simp [hN]

/-- `(wedge u) ⌟ ω = ∑_b (-1)^b (u_b · ω) wedge (u ∖ u_b)`. -/
theorem interiorProduct_wedge (u : Fin (m + 1) → Vec d) (ω : Vec d) :
    interiorProduct (wedge u) ω =
      (∑ b : Fin (m + 1), ((-1) ^ (b : ℕ) * vecDot (u b) ω) • (wedge (u ∘ b.succAbove) : KVec d m) :
        KVec d m) := by
  ext J
  have hJ : J.1.card = m := by have := J.2; omega
  rw [interiorProduct_apply_of_one_le (Nat.le_add_left 1 m)]
  have h1 : ∀ j : {j : Fin d // j ∉ J.1},
      ω j.1 * insertSign j.1 J.1 * wedge u ⟨insert j.1 J.1, card_insert_eq_of_one_le
        (Nat.le_add_left 1 m) J j.1 j.2⟩ =
      ω j.1 * ∑ b : Fin (m + 1), (-1) ^ (b : ℕ) * u b j.1 * wedge (u ∘ b.succAbove) ⟨J.1, hJ⟩ := by
    intro j
    rw [mul_assoc, insertSign_mul_wedge u J.1 hJ j.1]
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∉ J.1)) (p := fun j => j ∉ J.1) (by simp)
    (fun j => ω j * ∑ b : Fin (m + 1), (-1) ^ (b : ℕ) * u b j * wedge (u ∘ b.succAbove) ⟨J.1, hJ⟩)]
  rw [Finset.sum_filter_of_ne]
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecDot, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = _ * (wedge (u ∘ b.succAbove)) ⟨J.1, hJ⟩
    ring
  · intro j _ hne
    by_contra hj
    exact hne (by rw [sum_wedge_eq_zero_of_mem u J.1 hJ j hj, mul_zero])

/-- For `k ≥ 1`, `Λ_k(ker ω) ⊆ ker (· ⌟ ω)`. -/
theorem interiorProduct_eq_zero_of_mem_kvecSpan {k : ℕ} (hk : 1 ≤ k) (ω : Vec d) (v : KVec d k)
    (hv : v ∈ kvecSpan (covectorKernel ω) k) : interiorProduct v ω = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  change interiorProductLM (m + 1) ω v = 0
  have hle : kvecSpan (covectorKernel ω) (m + 1) ≤ LinearMap.ker (interiorProductLM (m + 1) ω) := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    change interiorProduct (wedge u) ω = 0
    rw [interiorProduct_wedge]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : vecDot (u b) ω = 0 := hu b
    simp [this]
  exact hle hv

end AFree
