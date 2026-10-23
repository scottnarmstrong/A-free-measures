module

public import AFree.Paper.OrderK.AlgebraVarPair

/-!
# Linearity of `∂^α`, and `∂^γ ∂^{γ'} = ∂^{γ+γ'}`

Composition of multi-index derivatives, and the global linearity facts used by the cut-off.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}

/-- Global additivity of `∂^α` on smooth functions. -/
theorem multiCoordDeriv_sum_global {ι : Type*} (s : Finset ι) {F : ι → Vec d → ℝ}
    (h : ∀ a ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F a)) (α : Fin d → ℕ) :
    multiCoordDeriv α (fun x => ∑ a ∈ s, F a x) = fun x => ∑ a ∈ s, multiCoordDeriv α (F a) x := by
  have hs : ∀ a ∈ s, SmOn Set.univ (F a) := fun a ha => smOn_univ_iff.2 (h a ha)
  have key : ∀ l : List (Fin d), foldDeriv l α (fun x => ∑ a ∈ s, F a x) =
      fun x => ∑ a ∈ s, foldDeriv l α (F a) x := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      funext x
      show (euclideanCoordDeriv i)^[α i] (foldDeriv l α (fun x => ∑ a ∈ s, F a x)) x = _
      rw [ih]
      exact iterD_sum isOpen_univ s (fun a ha => (hs a ha).foldr α l) i (α i) (Set.mem_univ x)
  exact key _

theorem multiCoordDeriv_add_global (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (α : Fin d → ℕ) :
    multiCoordDeriv α (fun x => f x + g x) =
      fun x => multiCoordDeriv α f x + multiCoordDeriv α g x := by
  have := multiCoordDeriv_sum_global (Finset.univ : Finset (Fin 2))
    (F := fun a => if a = 0 then f else g) (fun a _ => by split_ifs <;> assumption) α
  simpa [Fin.sum_univ_two] using this

theorem multiCoordDeriv_zero_fun (α : Fin d → ℕ) :
    multiCoordDeriv α (fun _ : Vec d => (0 : ℝ)) = fun _ => 0 := by
  have := multiCoordDeriv_const_mul (f := fun _ : Vec d => (0 : ℝ)) contDiff_const 0 α
  simpa using this

theorem multiCoordDeriv_neg_global (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : Fin d → ℕ) :
    multiCoordDeriv α (fun x => -f x) = fun x => -multiCoordDeriv α f x := by
  have := multiCoordDeriv_const_mul hf (-1) α
  simpa using this

/-- `∂_i^n ∂^β = ∂^{β + n e_i}`. -/
theorem multiCoordDeriv_shift (hU : IsOpen U) (hf : SmOn U f) (i : Fin d) (β : Fin d → ℕ) (n : ℕ) :
    Set.EqOn (multiCoordDeriv (Function.update β i (β i + n)) f)
      ((euclideanCoordDeriv i)^[n] (multiCoordDeriv β f)) U := by
  intro x hx
  rw [multiCoordDeriv_peel hU hf i _ hx]
  simp only [Function.update_self, Function.update_idem]
  rw [add_comm, Function.iterate_add_apply]
  refine eqOn_iterD hU ?_ i n hx
  intro y hy
  have := multiCoordDeriv_peel hU hf i β hy
  exact this.symm

/-- `∂^γ ∂^{γ'} f = ∂^{γ+γ'} f`. -/
theorem multiCoordDeriv_multiCoordDeriv (hU : IsOpen U) (hf : SmOn U f) (γ γ' : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv γ (multiCoordDeriv γ' f)) (multiCoordDeriv (γ + γ') f) U := by
  refine coord_induction (P := fun γ => Set.EqOn (multiCoordDeriv γ (multiCoordDeriv γ' f))
    (multiCoordDeriv (γ + γ') f) U) ?_ ?_ γ
  · intro x _
    simp [multiCoordDeriv_zero]
  · intro γ'' i hγ'' ih n x hx
    rw [multiCoordDeriv_update hU (hf.multi γ') i hγ'' n hx, eqOn_iterD hU ih i n hx]
    have e : Function.update γ'' i n + γ' =
        Function.update (γ'' + γ') i ((γ'' + γ') i + n) := by
      funext y
      by_cases hy : y = i
      · subst hy; simp [hγ'']; ring
      · simp [Function.update_of_ne hy]
    rw [e, multiCoordDeriv_shift hU hf i _ n hx]

end

end AFree
