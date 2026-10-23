module

public import AFree.Paper.OrderK.BlowUpCut
public import AFree.Paper.OrderK.StrongConstancyPiecesA

/-!
# The algebra behind the cut-off system

The Leibniz expansion of `∂^α(χ u)`, the top-order equation extracted from the mollified equation,
and the derivative of the explicit top-order pieces `G^{(α)} = -χ(Ā_α V + Y_{α,α})`.
-/

@[expose] public section

open MeasureTheory PDE Matrix

namespace AFree

noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The coefficient `s(α,β) = (-1)^{|α-β|} (α β)` of the mollified equation. -/
def mollSign (α β : Fin d → ℕ) : ℝ := (-1 : ℝ) ^ multiAbs (α - β) * multiChoose α β

/-- The explicit top-order pieces `G^{(α)} = -χ (Ā_α V + Y_{α,α})`. -/
def systemG (χ : Vec d → ℝ) (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (V : Vec d → ι → ℝ)
    (Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ) (α : Fin d → ℕ) : Vec d → κ → ℝ :=
  fun x c => -(χ x * (∑ i, Abar α c i * V x i + Y α α x c))

theorem cut_leibniz {χ u : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (α : Fin d → ℕ) (x : Vec d) :
    multiCoordDeriv α (fun y => χ y * u y) x = χ x * multiCoordDeriv α u x +
      ∑ β ∈ (multiLE α).erase α, multiChoose α β *
        (multiCoordDeriv (α - β) χ x * multiCoordDeriv β u x) := by
  have h := multiCoordDeriv_mul isOpen_univ (smOn_univ_iff.2 hu) (smOn_univ_iff.2 hχ) α
    (Set.mem_univ x)
  have e : (fun y => χ y * u y) = fun y => u y * χ y := funext fun y => mul_comm _ _
  beta_reduce at h
  rw [e, h]
  have hαm : α ∈ multiLE α := mem_multiLE.2 fun i => le_rfl
  rw [← Finset.add_sum_erase _ _ hαm]
  simp only [multiChoose_self, sub_self_pi, multiCoordDeriv_zero, one_mul]
  rw [mul_comm (multiCoordDeriv α u x)]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [mul_comm (multiCoordDeriv β u x)]

omit [Fintype κ] in
theorem topk_eq {k : ℕ} (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) (P0 : ι → ℝ) (r : ℝ)
    {u : Vec d → ℝ} {V μ : Vec d → ι → ℝ}
    {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ}
    (hμ : ∀ x, μ x = u x • P0 + V x) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => V x i)) (c : κ) (x : Vec d)
    (hmoll : ∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        ∑ i, Abar α c i * multiCoordDeriv α (fun y => μ y i) x =
      -(∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
        ∑ β ∈ multiLE α, mollSign α β * multiCoordDeriv β (fun y => Y α β y c) x)) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c * multiCoordDeriv α u x =
      -(∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
          multiCoordDeriv α (fun y => V y i) x) -
        ∑ h ∈ Finset.range k, r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
          ∑ i, Abar α c i * multiCoordDeriv α (fun y => μ y i) x -
        ∑ h ∈ Finset.range (k + 1), r ^ (k - h) * ∑ α ∈ Finset.Nat.antidiagonalTuple d h,
          ∑ β ∈ multiLE α, mollSign α β * multiCoordDeriv β (fun y => Y α β y c) x := by
  rw [Finset.sum_range_succ] at hmoll
  have hμi : ∀ α i, multiCoordDeriv α (fun y => μ y i) x =
      P0 i * multiCoordDeriv α u x + multiCoordDeriv α (fun y => V y i) x := by
    intro α i
    have e : (fun y => μ y i) = fun y => P0 i * u y + V y i := by
      funext y; rw [hμ y]; simp [mul_comm]
    rw [e, multiCoordDeriv_add_global (contDiff_const.mul hu) (hV i),
      multiCoordDeriv_const_mul hu (P0 i) α]
  have hk : ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
      multiCoordDeriv α (fun y => μ y i) x =
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (Abar α *ᵥ P0) c * multiCoordDeriv α u x +
      ∑ α ∈ Finset.Nat.antidiagonalTuple d k, ∑ i, Abar α c i *
        multiCoordDeriv α (fun y => V y i) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [hμi, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Nat.sub_self, pow_zero, one_mul, hk] at hmoll
  linarith

omit [Fintype κ] in
theorem deriv_systemG {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (Abar : (Fin d → ℕ) → Matrix κ ι ℝ) {V : Vec d → ι → ℝ}
    {Y : (Fin d → ℕ) → (Fin d → ℕ) → Vec d → κ → ℝ}
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => V x i))
    (hY : ∀ α β c, ContDiff ℝ (⊤ : ℕ∞) (fun x => Y α β x c)) (α : Fin d → ℕ) (c : κ) (x : Vec d) :
    multiCoordDeriv α (fun y => systemG χ Abar V Y α y c) x =
      -(∑ i, Abar α c i * multiCoordDeriv α (fun y => χ y * V y i) x) -
        multiCoordDeriv α (fun y => χ y * Y α α y c) x := by
  have hi : ∀ i ∈ (Finset.univ : Finset ι), ContDiff ℝ (⊤ : ℕ∞)
      (fun y => Abar α c i * (χ y * V y i)) := fun i _ => contDiff_const.mul (hχ.mul (hV i))
  have e : (fun y => systemG χ Abar V Y α y c) =
      fun y => -(∑ i, Abar α c i * (χ y * V y i) + χ y * Y α α y c) := by
    funext y
    simp only [systemG]
    rw [mul_add, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ i, Abar α c i * (χ y * V y i)) :=
    ContDiff.sum fun i _ => contDiff_const.mul (hχ.mul (hV i))
  have hy : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * Y α α y c) := hχ.mul (hY α α c)
  rw [e, multiCoordDeriv_neg_global (hs.add hy), multiCoordDeriv_add_global hs hy,
    multiCoordDeriv_sum_global Finset.univ hi α]
  simp only [neg_add]
  rw [sub_eq_add_neg]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [multiCoordDeriv_const_mul (hχ.mul (hV i)) (Abar α c i) α]

end

end AFree
