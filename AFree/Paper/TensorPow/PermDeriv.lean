module

public import AFree.Defs

/-!
# Iterated derivatives commute

Mixed partials of a smooth function commute, so `∂^L φ` only depends on the multiset of the list `L`.
-/

public section

open MeasureTheory

namespace AFree

open PDE

variable {d : ℕ}

/-- `∂^L φ = ∂_{L₀}(∂_{L₁}(⋯ ∂_{L_{n-1}} φ))` is smooth. -/
theorem contDiff_foldr_euclideanCoordDeriv {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (L : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (L.foldr (fun j g => euclideanCoordDeriv j g) φ) := by
  induction L with
  | nil => exact hφ
  | cons j L ih => exact contDiff_euclideanCoordDeriv ih j

/-- Permutation invariance: `∂^L φ = ∂^{L'} φ` when `L ~ L'`. -/
theorem foldr_euclideanCoordDeriv_perm {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {L L' : List (Fin d)} (h : L.Perm L') :
    L.foldr (fun j g => euclideanCoordDeriv j g) φ =
      L'.foldr (fun j g => euclideanCoordDeriv j g) φ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y L =>
    simp only [List.foldr_cons]
    exact euclideanCoordSecondDeriv_comm_fun (contDiff_foldr_euclideanCoordDeriv hφ L) x y
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The index lists of the two sides of `∂^{α[h↦i]} ∂_j φ = ∂^{α[h↦j]} ∂_i φ` are permutations of each other. -/
theorem ofFn_update_append_perm {r : ℕ} (α : Fin r → Fin d) (h : Fin r) (i j : Fin d) :
    (List.ofFn (Function.update α h i) ++ [j]).Perm
      (List.ofFn (Function.update α h j) ++ [i]) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.coe_add, ← Fin.univ_val_map,
    ← Fin.univ_val_map]
  have key : ∀ b : Fin d, (Finset.univ.val.map (Function.update α h b) : Multiset (Fin d)) =
      b ::ₘ ((Finset.univ.erase h).val.map α) := by
    intro b
    have : (Finset.univ : Finset (Fin r)).val = h ::ₘ (Finset.univ.erase h).val := by
      rw [Finset.erase_val, Multiset.cons_erase (Finset.mem_univ h)]
    rw [this, Multiset.map_cons, Function.update_self]
    congr 1
    refine Multiset.map_congr rfl fun t ht => ?_
    exact Function.update_of_ne (by
      rintro rfl
      rw [Finset.erase_val] at ht
      exact ((Multiset.Nodup.mem_erase_iff (Finset.univ).nodup).1 ht).1 rfl) _ _
  rw [key, key]
  ext a
  simp [Multiset.count_add, Multiset.count_cons, Multiset.count_singleton]
  omega

/-- `∂^{α[h↦i]} ∂_j φ = ∂^{α[h↦j]} ∂_i φ`. -/
theorem iteratedCoordDeriv_update_coordDeriv {r : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (α : Fin r → Fin d) (h : Fin r) (i j : Fin d) :
    iteratedCoordDeriv (Function.update α h i) (euclideanCoordDeriv j φ) =
      iteratedCoordDeriv (Function.update α h j) (euclideanCoordDeriv i φ) := by
  have e : ∀ (β : Fin r → Fin d) (k : Fin d),
      iteratedCoordDeriv β (euclideanCoordDeriv k φ) =
        (List.ofFn β ++ [k]).foldr (fun j g => euclideanCoordDeriv j g) φ := by
    intro β k
    simp [iteratedCoordDeriv, List.foldr_append]
  rw [e, e]
  exact foldr_euclideanCoordDeriv_perm hφ (ofFn_update_append_perm α h i j)

end AFree
