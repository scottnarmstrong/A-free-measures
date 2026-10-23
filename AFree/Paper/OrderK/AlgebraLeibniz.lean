module

public import AFree.Paper.OrderK.AlgebraMulti

/-!
# The multi-index Leibniz rule and the reverse Leibniz rule

The multi-index Leibniz rule and the reverse Leibniz identity
on an open set `U`, by induction over coordinates.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}

theorem multiLE_zero : multiLE (0 : Fin d → ℕ) = {0} := by
  ext β
  simp only [mem_multiLE, Finset.mem_singleton, Pi.zero_apply, nonpos_iff_eq_zero]
  exact ⟨fun h => funext h, fun h i => by simp [h]⟩

theorem zero_sub_zero : (0 : Fin d → ℕ) - 0 = 0 := by funext; simp

theorem multiChoose_zero : multiChoose (0 : Fin d → ℕ) 0 = 1 := by simp [multiChoose]

/-- `∂^γ` commutes with `D_i^b` on smooth functions. -/
theorem multiCoordDeriv_comm_iterD (hU : IsOpen U) (hf : SmOn U f) (i : Fin d) (b : ℕ)
    (γ : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv γ ((euclideanCoordDeriv i)^[b] f))
      ((euclideanCoordDeriv i)^[b] (multiCoordDeriv γ f)) U := by
  have key : ∀ l : List (Fin d), Set.EqOn (foldDeriv l γ ((euclideanCoordDeriv i)^[b] f))
      ((euclideanCoordDeriv i)^[b] (foldDeriv l γ f)) U := by
    intro l
    induction l with
    | nil => exact fun _ _ => rfl
    | cons j l ih =>
      intro x hx
      show (euclideanCoordDeriv j)^[γ j] (foldDeriv l γ ((euclideanCoordDeriv i)^[b] f)) x = _
      rw [eqOn_iterD hU ih j (γ j) hx]
      exact iterD_iterD_comm hU (hf.foldr γ l) i j b (γ j) hx
  exact key _

/-- The Leibniz rule `∂^α(fg) = Σ_{β ≤ α} (α β) ∂^β f ∂^{α-β} g`
on the open set `U` where `f, g` are smooth. -/
theorem multiCoordDeriv_mul (hU : IsOpen U) (hf : SmOn U f) (hg : SmOn U g)
    (α : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv α (fun x => f x * g x))
      (fun x => ∑ β ∈ multiLE α, multiChoose α β *
        (multiCoordDeriv β f x * multiCoordDeriv (α - β) g x)) U := by
  refine coord_induction (P := fun α => Set.EqOn (multiCoordDeriv α (fun x => f x * g x))
      (fun x => ∑ β ∈ multiLE α, multiChoose α β *
        (multiCoordDeriv β f x * multiCoordDeriv (α - β) g x)) U) ?_ ?_ α
  · intro x hx
    simp [multiLE_zero, multiChoose_zero, multiCoordDeriv_zero, zero_sub_zero]
  · intro α' i hα' ih n x hx
    rw [multiCoordDeriv_update hU (hf.mul hg) i hα' n hx,
      eqOn_iterD hU ih i n hx]
    have hs : ∀ β ∈ multiLE α', SmOn U (fun x => multiChoose α' β *
        (multiCoordDeriv β f x * multiCoordDeriv (α' - β) g x)) :=
      fun β _ => ((hf.multi β).mul (hg.multi _)).const_mul _
    rw [iterD_sum hU _ hs i n hx]
    dsimp only
    rw [sum_multiLE_update α' i hα' n]
    refine Finset.sum_congr rfl fun β' hβ' => ?_
    have hβ0 : β' i = 0 := by have := multiLE_apply_le hβ' i; omega
    have e1 := iterD_const_mul hU (multiChoose α' β')
      ((hf.multi β').mul (hg.multi (α' - β'))) i n hx
    dsimp only at e1
    rw [e1]
    have e2 := iterD_mul_range hU (hf.multi β') (hg.multi (α' - β')) i n hx
    dsimp only at e2
    rw [e2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [multiChoose_update i hα' hβ0, update_sub_update,
      multiCoordDeriv_update hU hf i hβ0 a hx,
      multiCoordDeriv_update hU hg i (sub_apply_eq_zero i hα') (n - a) hx]
    ring

/-- The reverse Leibniz rule on the open set `U` where `χ, f` are smooth:
`χ ∂^γ f = Σ_{δ ≤ γ} (-1)^{|γ-δ|} (γ δ) ∂^δ((∂^{γ-δ} χ) f)`. -/
theorem multiCoordDeriv_rev (hU : IsOpen U) (γ : Fin d → ℕ) :
    ∀ {χ f : Vec d → ℝ}, SmOn U χ → SmOn U f →
    Set.EqOn (fun x => χ x * multiCoordDeriv γ f x)
      (fun x => ∑ δ ∈ multiLE γ, (-1 : ℝ) ^ multiAbs (γ - δ) * multiChoose γ δ *
        multiCoordDeriv δ (fun y => multiCoordDeriv (γ - δ) χ y * f y) x) U := by
  refine coord_induction (P := fun γ => ∀ {χ f : Vec d → ℝ}, SmOn U χ → SmOn U f →
    Set.EqOn (fun x => χ x * multiCoordDeriv γ f x)
      (fun x => ∑ δ ∈ multiLE γ, (-1 : ℝ) ^ multiAbs (γ - δ) * multiChoose γ δ *
        multiCoordDeriv δ (fun y => multiCoordDeriv (γ - δ) χ y * f y) x) U) ?_ ?_ γ
  · intro χ f _ _ x hx
    simp [multiLE_zero, multiChoose_zero, multiCoordDeriv_zero, multiAbs, zero_sub_zero]
  · intro γ' i hγ' ih n χ f hχ hf x hx
    beta_reduce
    rw [multiCoordDeriv_update hU hf i hγ' n hx]
    have e0 := iterD_rev hU (hf.multi γ') i n hχ hx
    beta_reduce at e0
    rw [e0]
    rw [sum_multiLE_update γ' i hγ' n,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ab => (-1 : ℝ) ^ ab.2 * (n.choose ab.1 : ℝ) *
          (euclideanCoordDeriv i)^[ab.1] (fun y => (euclideanCoordDeriv i)^[ab.2] χ y *
            multiCoordDeriv γ' f y) x) n]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    have hb : SmOn U ((euclideanCoordDeriv i)^[n - a] χ) := hχ.iterD i _
    have ihe := ih hb hf
    have e1 := eqOn_iterD hU ihe i a hx
    rw [e1]
    have hs : ∀ δ ∈ multiLE γ', SmOn U (fun x => (-1 : ℝ) ^ multiAbs (γ' - δ) * multiChoose γ' δ *
        multiCoordDeriv δ (fun y => multiCoordDeriv (γ' - δ) ((euclideanCoordDeriv i)^[n - a] χ) y *
          f y) x) :=
      fun δ _ => (((hb.multi _).mul hf).multi δ).const_mul _
    have e2 := iterD_sum hU _ hs i a hx
    dsimp only at e2
    rw [e2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    have hδ0 : δ i = 0 := by have := multiLE_apply_le hδ i; omega
    have hδs : SmOn U (fun y => multiCoordDeriv (γ' - δ) ((euclideanCoordDeriv i)^[n - a] χ) y *
        f y) := (hb.multi _).mul hf
    have e3 := iterD_const_mul hU ((-1 : ℝ) ^ multiAbs (γ' - δ) * multiChoose γ' δ)
      (hδs.multi δ) i a hx
    dsimp only at e3
    rw [e3]
    have e4 := multiCoordDeriv_update hU hδs i hδ0 a hx
    rw [← e4]
    have e5 : Set.EqOn (fun y => multiCoordDeriv (γ' - δ) ((euclideanCoordDeriv i)^[n - a] χ) y *
          f y)
        (fun y => multiCoordDeriv (Function.update (γ' - δ) i (n - a)) χ y * f y) U := by
      intro y hy
      dsimp only
      rw [multiCoordDeriv_comm_iterD hU hχ i (n - a) (γ' - δ) hy,
        multiCoordDeriv_update hU hχ i (sub_apply_eq_zero i hγ') (n - a) hy]
    rw [eqOn_multiCoordDeriv hU e5 (Function.update δ i a) hx]
    rw [multiChoose_update i hγ' hδ0, update_sub_update,
      multiAbs_update i (sub_apply_eq_zero i hγ'), pow_add]
    ring

end

end AFree
