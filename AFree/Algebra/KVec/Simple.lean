module

public import AFree.Algebra.KVec.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Simplicity of `(d-2)`-vectors of a hyperplane (Remark 1.11, linear algebra)

Sums of simple `(m+1)`-vectors of a hyperplane of `ℝ^{m+3}` are simple; the dimension is written
`d = m + 3` throughout.
-/

@[expose] public section

open Matrix PDE

namespace AFree

variable {d m : ℕ}

/-- If `(z, p)` is independent in `H` with `dim H = m + 1`, every `y ∈ H^{m+1}` has
`wedge y` a multiple of `wedge (z, p)` (change of vectors). -/
theorem exists_wedge_eq_smul_snoc (z : Fin m → Vec d) (hz : LinearIndependent ℝ z) (p : Vec d)
    (hp : p ∉ Submodule.span ℝ (Set.range z)) (H : Submodule ℝ (Vec d))
    (hH : Module.finrank ℝ H = m + 1) (hzH : ∀ i, z i ∈ H) (hpH : p ∈ H)
    (y : Fin (m + 1) → Vec d) (hy : ∀ a, y a ∈ H) :
    ∃ c : ℝ, wedge y = c • wedge (Fin.snoc z p : Fin (m + 1) → Vec d) := by
  set u : Fin (m + 1) → Vec d := Fin.snoc z p with hu
  have hli : LinearIndependent ℝ u := linearIndependent_finSnoc.mpr ⟨hz, hp⟩
  have hle : Submodule.span ℝ (Set.range u) ≤ H := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [hu] using hpH
    · simpa [hu] using hzH i
  have heq : Submodule.span ℝ (Set.range u) = H :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli]; simp [hH])
  have hmem : ∀ a, ∃ c : Fin (m + 1) → ℝ, ∑ i, c i • u i = y a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (heq ▸ hy a)
  choose M hM using hmem
  exact ⟨(Matrix.of M).det, wedge_change (Matrix.of M) y u fun a => (hM a).symm⟩

/-- Sums of simple `(m+1)`-vectors of a hyperplane `V ⊂ ℝ^{m+3}` are simple
(already as wedges of vectors of `V`). -/
theorem simpleadd (V : Submodule ℝ (Vec (m + 3))) (hV : Module.finrank ℝ V = m + 2)
    (y y' : Fin (m + 1) → Vec (m + 3)) (hy : ∀ i, y i ∈ V) (hy' : ∀ i, y' i ∈ V) :
    ∃ y'' : Fin (m + 1) → Vec (m + 3), (∀ i, y'' i ∈ V) ∧ wedge y + wedge y' = wedge y'' := by
  by_cases h0 : wedge y = 0
  · exact ⟨y', hy', by rw [h0, zero_add]⟩
  by_cases h0' : wedge y' = 0
  · exact ⟨y, hy, by rw [h0', add_zero]⟩
  have hind : ∀ w : Fin (m + 1) → Vec (m + 3), wedge w ≠ 0 → LinearIndependent ℝ w := by
    intro w hw
    rw [Fintype.linearIndependent_iff]
    intro t ht
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    exact hw (wedge_eq_zero_of_dep w t (fun h => hi (by simp [h])) ht)
  have hli := hind y h0
  have hli' := hind y' h0'
  set H := Submodule.span ℝ (Set.range y) with hHdef
  set H' := Submodule.span ℝ (Set.range y') with hH'def
  have hH : Module.finrank ℝ H = m + 1 := by rw [hHdef, finrank_span_eq_card hli]; simp
  have hH' : Module.finrank ℝ H' = m + 1 := by rw [hH'def, finrank_span_eq_card hli']; simp
  have hHV : H ≤ V := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy i)
  have hH'V : H' ≤ V := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy' i)
  have hyH : ∀ i, y i ∈ H := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hyH' : ∀ i, y' i ∈ H' := fun i => Submodule.subset_span ⟨i, rfl⟩
  -- a common independent family of `m` vectors in `H ⊓ H'`
  have hsup : Module.finrank ℝ (H ⊔ H' : Submodule ℝ (Vec (m + 3))) ≤ m + 2 :=
    hV ▸ Submodule.finrank_mono (sup_le hHV hH'V)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq H H'
  have hK : m ≤ Module.finrank ℝ (H ⊓ H' : Submodule ℝ (Vec (m + 3))) := by omega
  set b := Module.finBasis ℝ (H ⊓ H' : Submodule ℝ (Vec (m + 3))) with hb
  set z : Fin m → Vec (m + 3) := fun i => (b (Fin.castLE hK i) : Vec (m + 3)) with hz
  have hzli : LinearIndependent ℝ z :=
    (b.linearIndependent.comp _ (Fin.castLE_injective hK)).map' (H ⊓ H').subtype
      (Submodule.ker_subtype _)
  have hzK : ∀ i, z i ∈ H ⊓ H' := fun i => (b (Fin.castLE hK i)).2
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range z)) = m := by
    rw [finrank_span_eq_card hzli]; simp
  have hex : ∀ (G : Submodule ℝ (Vec (m + 3))), Module.finrank ℝ G = m + 1 →
      ∃ p ∈ G, p ∉ Submodule.span ℝ (Set.range z) := by
    intro G hG
    by_contra hc
    push Not at hc
    have := Submodule.finrank_mono (show G ≤ Submodule.span ℝ (Set.range z) from hc)
    omega
  obtain ⟨p, hpH, hp⟩ := hex H hH
  obtain ⟨q, hqH', hq⟩ := hex H' hH'
  obtain ⟨c, hc⟩ := exists_wedge_eq_smul_snoc z hzli p hp H hH (fun i => (hzK i).1) hpH y hyH
  obtain ⟨c', hc'⟩ :=
    exists_wedge_eq_smul_snoc z hzli q hq H' hH' (fun i => (hzK i).2) hqH' y' hyH'
  refine ⟨Fin.snoc z (c • p + c' • q), ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using Submodule.add_mem _ (Submodule.smul_mem _ c (hHV hpH))
        (Submodule.smul_mem _ c' (hH'V hqH'))
    · simpa using hHV (hzK i).1
  · have e1 : (Fin.snoc z (c • p + c' • q) : Fin (m + 1) → Vec (m + 3)) =
        Function.update (Fin.snoc z p : Fin (m + 1) → Vec (m + 3)) (Fin.last m)
          (c • p + c' • q) := (Fin.update_snoc_last _ _ _).symm
    have e2 : (Fin.snoc z q : Fin (m + 1) → Vec (m + 3)) =
        Function.update (Fin.snoc z p : Fin (m + 1) → Vec (m + 3)) (Fin.last m) q :=
      (Fin.update_snoc_last _ _ _).symm
    have e3 : (Fin.snoc z p : Fin (m + 1) → Vec (m + 3)) =
        Function.update (Fin.snoc z p : Fin (m + 1) → Vec (m + 3)) (Fin.last m) p :=
      (Fin.update_snoc_last _ _ _).symm
    rw [hc, hc', e1, wedge_update_add, wedge_update_smul, wedge_update_smul, ← e2, ← e3]

/-- Every `m+1`-fold wedge of vectors of `V` (`dim V = m + 2`, ambient `m + 3`) spans, together
with sums, only simple vectors: `Λ_{m+1}(V)` consists of simple `(m+1)`-vectors. -/
theorem isSimpleKVec_of_mem_kvecSpan_aux (V : Submodule ℝ (Vec (m + 3)))
    (hV : Module.finrank ℝ V = m + 2) (w : KVec (m + 3) (m + 1))
    (hw : w ∈ kvecSpan V (m + 1)) : IsSimpleKVec w := by
  have key : ∃ y : Fin (m + 1) → Vec (m + 3), (∀ i, y i ∈ V) ∧ w = wedge y := by
    refine Submodule.span_induction (p := fun w _ => ∃ y : Fin (m + 1) → Vec (m + 3),
      (∀ i, y i ∈ V) ∧ w = wedge y) ?_ ?_ ?_ ?_ hw
    · intro w hw
      exact hw
    · refine ⟨fun _ => 0, fun _ => V.zero_mem, ?_⟩
      ext I
      have h0 : (Matrix.of fun (_ _ : Fin (m + 1)) => (0 : ℝ)) = 0 := rfl
      simp [wedge_apply, wedgeMat, h0, Matrix.det_zero]
    · rintro x x' _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      obtain ⟨y'', hy'', h⟩ := simpleadd V hV y y' hy hy'
      exact ⟨y'', hy'', h⟩
    · rintro a x _ ⟨y, hy, rfl⟩
      refine ⟨Function.update y 0 (a • y 0), fun i => ?_, ?_⟩
      · by_cases hi : i = 0
        · subst hi; simpa using V.smul_mem a (hy 0)
        · simpa [Function.update_of_ne hi] using hy i
      · rw [wedge_update_smul, Function.update_eq_self]
  obtain ⟨y, -, rfl⟩ := key
  exact ⟨1, y, (one_smul _ _).symm⟩

/-- [DPR, Remark 1.11], linear algebra: if `dim V = d - 1` then every
`w ∈ Λ_{d-2}(V)` is simple. -/
theorem simplelin {d : ℕ} (V : Submodule ℝ (Vec d)) (hV : Module.finrank ℝ V = d - 1)
    (w : KVec d (d - 2)) (hw : w ∈ kvecSpan V (d - 2)) : IsSimpleKVec w := by
  by_cases hd : d ≤ 2
  · exact isSimpleKVec_of_eq_zero (by omega) w
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
    exact isSimpleKVec_of_mem_kvecSpan_aux V (by omega) w hw

end AFree
