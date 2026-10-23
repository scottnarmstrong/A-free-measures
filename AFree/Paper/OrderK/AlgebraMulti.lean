module

public import AFree.Paper.OrderK.AlgebraPeel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# Multi-index bookkeeping

The index set `{β ≤ α}`, the multi-binomial coefficient, the coordinate induction principle, and
the splitting of `Σ_{β ≤ update α' i n}` into `Σ_{β' ≤ α'} Σ_{a ≤ n}`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ}

/-- The multi-indices `β ≤ α` (coordinatewise), as a finset. -/
def multiLE (α : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (α i + 1)

/-- The multi-binomial coefficient `(α choose β) = ∏ᵢ (αᵢ choose βᵢ)`. -/
def multiChoose (α β : Fin d → ℕ) : ℝ := ∏ i, ((α i).choose (β i) : ℝ)

/-- The order `|α| = Σᵢ αᵢ` of a multi-index. -/
def multiAbs (α : Fin d → ℕ) : ℕ := ∑ i, α i

theorem mem_multiLE {α β : Fin d → ℕ} : β ∈ multiLE α ↔ ∀ i, β i ≤ α i := by
  simp [multiLE, Fintype.mem_piFinset, ]

theorem multiLE_apply_le {α β : Fin d → ℕ} (h : β ∈ multiLE α) (i : Fin d) : β i ≤ α i :=
  mem_multiLE.1 h i

/-- Induction over multi-indices, one coordinate at a time. -/
theorem coord_induction {P : (Fin d → ℕ) → Prop} (h0 : P 0)
    (hstep : ∀ (α : Fin d → ℕ) (i : Fin d), α i = 0 → P α → ∀ n, P (Function.update α i n)) :
    ∀ α, P α := by
  have key : ∀ s : Finset (Fin d), ∀ α : Fin d → ℕ, (∀ i ∉ s, α i = 0) → P α := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro α h
      have : α = 0 := funext fun i => h i (by simp)
      rw [this]; exact h0
    | insert j s hj ih =>
      intro α h
      have h' : ∀ i ∉ s, Function.update α j 0 i = 0 := by
        intro i hi
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij]; exact h i (by simp [hij, hi])
      have := hstep _ j (by simp) (ih _ h') (α j)
      rwa [Function.update_idem, Function.update_eq_self] at this
  exact fun α => key Finset.univ α (fun i hi => absurd (Finset.mem_univ i) hi)

theorem sum_multiLE_update {M : Type*} [AddCommMonoid M] (α' : Fin d → ℕ) (i : Fin d)
    (hα' : α' i = 0) (n : ℕ) (G : (Fin d → ℕ) → M) :
    ∑ β ∈ multiLE (Function.update α' i n), G β =
      ∑ β' ∈ multiLE α', ∑ a ∈ Finset.range (n + 1), G (Function.update β' i a) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => Function.update p.1 i p.2)
    (fun β => (Function.update β i 0, β i)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨β', a⟩ hp
    rw [Finset.mem_product, mem_multiLE, Finset.mem_range] at hp
    rw [mem_multiLE]
    intro x
    by_cases hx : x = i
    · subst hx; simp; omega
    · simp only [Function.update_of_ne hx]; exact hp.1 x
  · intro β hβ
    rw [mem_multiLE] at hβ
    rw [Finset.mem_product, mem_multiLE, Finset.mem_range]
    refine ⟨fun x => ?_, ?_⟩
    · by_cases hx : x = i
      · subst hx; simp
      · have := hβ x; simp only [Function.update_of_ne hx] at this ⊢; exact this
    · have := hβ i; simp at this; omega
  · rintro ⟨β', a⟩ hp
    rw [Finset.mem_product, mem_multiLE] at hp
    have h0 : β' i = 0 := by have := hp.1 i; simp only at this; omega
    have e : Function.update β' i 0 = β' := by
      funext x
      by_cases hx : x = i
      · subst hx; simp [h0]
      · simp [Function.update_of_ne hx]
    simp [Function.update_idem, e]
  · intro β _
    simp
  · intro p _; rfl

theorem multiChoose_update {α' β' : Fin d → ℕ} (i : Fin d) (hα' : α' i = 0) (hβ' : β' i = 0)
    (n a : ℕ) :
    multiChoose (Function.update α' i n) (Function.update β' i a) =
      (n.choose a : ℝ) * multiChoose α' β' := by
  unfold multiChoose
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun x => ((α' x).choose (β' x) : ℝ)) (Finset.mem_univ i)]
  simp only [Function.update_self, hα', hβ', Nat.choose_zero_right, Nat.cast_one, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' : x ≠ i := Finset.ne_of_mem_erase hx
  simp [Function.update_of_ne hx']

theorem update_sub_update (α' β' : Fin d → ℕ) (i : Fin d) (n a : ℕ) :
    Function.update α' i n - Function.update β' i a = Function.update (α' - β') i (n - a) := by
  funext x
  by_cases hx : x = i
  · subst hx; simp
  · simp [Function.update_of_ne hx]

theorem multiAbs_update {γ : Fin d → ℕ} (i : Fin d) (hγ : γ i = 0) (m : ℕ) :
    multiAbs (Function.update γ i m) = multiAbs γ + m := by
  unfold multiAbs
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase Finset.univ γ (Finset.mem_univ i), hγ]
  simp [Finset.sdiff_singleton_eq_erase, add_comm]

theorem sub_apply_eq_zero {α' β' : Fin d → ℕ} (i : Fin d) (hα' : α' i = 0) :
    (α' - β') i = 0 := by simp [hα']

end

end AFree
