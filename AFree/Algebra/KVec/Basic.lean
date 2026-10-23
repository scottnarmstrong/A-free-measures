module

public import AFree.Defs

/-!
# Exterior algebra in coordinates: basic properties

Multilinearity and alternation of the coordinate wedge, the case `k = 0`, and the coordinate formula for
the interior product.
-/

@[expose] public section

open Matrix PDE

namespace AFree

variable {d k : ℕ}

/-- The matrix `M_I(u) = (u_b(I^↑(a)))_{a,b}` so `wedge u I = det M_I(u)`. -/
noncomputable def wedgeMat (I : KIdx d k) (u : Fin k → Vec d) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a b => u b (I.1.orderEmbOfFin I.2 a)

theorem wedge_apply (u : Fin k → Vec d) (I : KIdx d k) : wedge u I = (wedgeMat I u).det := rfl

theorem wedgeMat_update (I : KIdx d k) (u : Fin k → Vec d) (b : Fin k) (x : Vec d) :
    wedgeMat I (Function.update u b x) =
      (wedgeMat I u).updateCol b (fun a => x (I.1.orderEmbOfFin I.2 a)) := by
  ext a c
  by_cases h : c = b
  · subst h; simp [wedgeMat]
  · simp [wedgeMat, h]

/-- The wedge is additive in each slot. -/
theorem wedge_update_add (u : Fin k → Vec d) (b : Fin k) (x y : Vec d) :
    wedge (Function.update u b (x + y)) =
      wedge (Function.update u b x) + wedge (Function.update u b y) := by
  ext I
  simp only [wedge_apply, wedgeMat_update, Pi.add_apply]
  rw [← Matrix.det_updateCol_add]
  rfl

/-- The wedge is homogeneous in each slot. -/
theorem wedge_update_smul (u : Fin k → Vec d) (b : Fin k) (c : ℝ) (x : Vec d) :
    wedge (Function.update u b (c • x)) = c • wedge (Function.update u b x) := by
  ext I
  simp only [wedge_apply, wedgeMat_update, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_updateCol_smul]
  rfl

/-- Change of vectors: `wedge y = det M • wedge z` if `y a = ∑ M a b • z b`. -/
theorem wedge_change (M : Matrix (Fin k) (Fin k) ℝ) (y z : Fin k → Vec d)
    (h : ∀ a, y a = ∑ b, M a b • z b) : wedge y = M.det • wedge z := by
  ext I
  have hm : wedgeMat I y = wedgeMat I z * Mᵀ := by
    ext a c
    simp [wedgeMat, h c, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  simp only [wedge_apply, hm, Matrix.det_mul, Matrix.det_transpose, Pi.smul_apply, smul_eq_mul]
  ring

/-- The wedge of linearly dependent vectors vanishes. -/
theorem wedge_eq_zero_of_dep (u : Fin k → Vec d) (t : Fin k → ℝ) (ht : t ≠ 0)
    (h : ∑ b, t b • u b = 0) : wedge u = 0 := by
  ext I
  simp only [wedge_apply, Pi.zero_apply]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨t, ht, ?_⟩
  ext a
  have := congrFun h (I.1.orderEmbOfFin I.2 a)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [Matrix.mulVec, dotProduct, wedgeMat, Matrix.of_apply, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- Every `0`-vector is a multiple of the empty wedge. -/
theorem wedge_zero_index (u : Fin 0 → Vec d) : wedge u = fun _ => 1 := by
  ext I
  simp [wedge_apply]

theorem isSimpleKVec_of_eq_zero {k : ℕ} (hk : k = 0) (w : KVec d k) : IsSimpleKVec w := by
  subst hk
  exact ⟨w ⟨∅, by simp⟩, Fin.elim0, by
    ext I
    have : I = ⟨∅, by simp⟩ := Subtype.ext (Finset.card_eq_zero.mp I.2)
    subst this
    simp [wedge_zero_index]⟩

theorem kvecSpan_zero_eq_top (V : Submodule ℝ (Vec d)) : kvecSpan V 0 = ⊤ := by
  refine eq_top_iff.mpr fun w _ => ?_
  have hw : w = w ⟨∅, by simp⟩ • wedge (Fin.elim0 : Fin 0 → Vec d) := by
    ext I
    have : I = ⟨∅, by simp⟩ := Subtype.ext (Finset.card_eq_zero.mp I.2)
    subst this
    simp [wedge_zero_index]
  rw [hw]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.elim0, fun i => i.elim0, rfl⟩)

/-- For `k = 0` the wedge is the constant `1`, every `0`-vector is simple, and
`Λ₀(V) = Λ₀` for every subspace `V`. -/
theorem kzero :
    (∀ u : Fin 0 → Vec d, wedge u = fun _ => 1) ∧ (∀ w : KVec d 0, IsSimpleKVec w) ∧
      ∀ V : Submodule ℝ (Vec d), kvecSpan V 0 = ⊤ :=
  ⟨wedge_zero_index, isSimpleKVec_of_eq_zero rfl, kvecSpan_zero_eq_top⟩

theorem card_insert_eq_of_one_le (hk : 1 ≤ k) (J : KIdx d (k - 1)) (j : Fin d) (hj : j ∉ J.1) :
    (insert j J.1).card = k := by
  have := J.2
  rw [Finset.card_insert_of_notMem hj]
  omega

/-- The interior product coordinate formula for `k ≥ 1`: only the first branch of the
definition occurs. -/
theorem interiorProduct_apply_of_one_le (hk : 1 ≤ k) (v : KVec d k) (ω : Vec d)
    (J : KIdx d (k - 1)) :
    interiorProduct v ω J = ∑ j : {j : Fin d // j ∉ J.1},
      ω j.1 * insertSign j.1 J.1 * v ⟨insert j.1 J.1, card_insert_eq_of_one_le hk J j.1 j.2⟩ := by
  unfold interiorProduct
  rw [Finset.sum_subtype (Finset.univ.filter (· ∉ J.1)) (p := fun j => j ∉ J.1) (by simp)]
  exact Finset.sum_congr rfl fun j _ => by simp [card_insert_eq_of_one_le hk J j.1 j.2]

theorem interiorProduct_add (v w : KVec d k) (ω : Vec d) :
    interiorProduct (v + w) ω = interiorProduct v ω + interiorProduct w ω := by
  ext J
  simp only [interiorProduct, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_add]

theorem interiorProduct_smul (c : ℝ) (v : KVec d k) (ω : Vec d) :
    interiorProduct (c • v) ω = c • interiorProduct v ω := by
  ext J
  simp only [interiorProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_left_comm]

/-- The interior product with `ω` as a linear map. -/
noncomputable def interiorProductLM (k : ℕ) (ω : Vec d) : KVec d k →ₗ[ℝ] KVec d (k - 1) where
  toFun v := interiorProduct v ω
  map_add' v w := interiorProduct_add v w ω
  map_smul' c v := interiorProduct_smul c v ω

end AFree
