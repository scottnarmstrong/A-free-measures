module

public import AFree.Paper.OrderK.HarmonicBasic

/-!
# Multi-index derivatives of `C_c^∞` functions

Facts used by strong constancy:
`∂^α` (`multiCoordDeriv`) preserves `C_c^∞` and does not enlarge the support, and the
Fourier rule `\\widehat{∂^α u}(ξ) = (2πi)^{|α|} ξ^α û(ξ)` obtained by iterating the first-order rule.
-/

@[expose] public section

open MeasureTheory PDE Matrix
open scoped SchwartzMap

namespace AFree

noncomputable section

variable {d : ℕ}

theorem isCc_euclideanCoordDeriv {u : Vec d → ℝ} (hu : IsCc u) (ℓ : Fin d) :
    IsCc (euclideanCoordDeriv ℓ u) :=
  ⟨contDiff_euclideanCoordDeriv hu.1 ℓ, hasCompactSupport_euclideanCoordDeriv hu.2 ℓ⟩

theorem isCc_iterate_euclideanCoordDeriv {u : Vec d → ℝ} (hu : IsCc u) (ℓ : Fin d) (n : ℕ) :
    IsCc ((euclideanCoordDeriv ℓ)^[n] u) := by
  induction n with
  | zero => exact hu
  | succ n ih => rw [Function.iterate_succ_apply']; exact isCc_euclideanCoordDeriv ih ℓ

theorem isCc_foldr_iterate {u : Vec d → ℝ} (hu : IsCc u) (α : Fin d → ℕ) (l : List (Fin d)) :
    IsCc (l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) u) := by
  induction l with
  | nil => exact hu
  | cons i l ih => exact isCc_iterate_euclideanCoordDeriv ih i (α i)

/-- Componentwise `∂^α` of a vector-valued function `F : ℝ^d → ℝ^κ`. -/
def multiCoordDerivVec {κ : Type*} (α : Fin d → ℕ) (F : Vec d → κ → ℝ) : Vec d → κ → ℝ :=
  fun x c => multiCoordDeriv α (fun y => F y c) x

/-- `∂^α` preserves `C_c^∞`. -/
theorem isCc_multiCoordDeriv {u : Vec d → ℝ} (hu : IsCc u) (α : Fin d → ℕ) :
    IsCc (multiCoordDeriv α u) :=
  isCc_foldr_iterate hu α _

theorem tsupport_iterate_euclideanCoordDeriv_subset (u : Vec d → ℝ) (ℓ : Fin d) (n : ℕ) :
    tsupport ((euclideanCoordDeriv ℓ)^[n] u) ⊆ tsupport u := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (closure_minimal (support_euclideanCoordDeriv_subset_tsupport ℓ _)
      (isClosed_tsupport _)).trans ih

theorem tsupport_foldr_iterate_subset (u : Vec d → ℝ) (α : Fin d → ℕ) (l : List (Fin d)) :
    tsupport (l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) u) ⊆ tsupport u := by
  induction l with
  | nil => exact subset_rfl
  | cons i l ih =>
    exact (tsupport_iterate_euclideanCoordDeriv_subset _ i (α i)).trans ih

/-- `tsupp ∂^α f ⊆ tsupp f`. -/
theorem tsupport_multiCoordDeriv_subset (u : Vec d → ℝ) (α : Fin d → ℕ) :
    tsupport (multiCoordDeriv α u) ⊆ tsupport u :=
  tsupport_foldr_iterate_subset u α _

theorem vecFourier_euclideanCoordDeriv_of_isCc {u : Vec d → ℝ} (hu : IsCc u) (ℓ : Fin d)
    (ξ : Vec d) :
    vecFourier (fun x => (euclideanCoordDeriv ℓ u x : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ ℓ : ℂ)) * vecFourier (fun x => (u x : ℂ)) ξ :=
  vecFourier_euclideanCoordDeriv (toSchwartz u hu.1 hu.2) ℓ ξ

theorem vecFourier_iterate_euclideanCoordDeriv {u : Vec d → ℝ} (hu : IsCc u) (ℓ : Fin d)
    (n : ℕ) (ξ : Vec d) :
    vecFourier (fun x => (((euclideanCoordDeriv ℓ)^[n] u) x : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ ℓ : ℂ)) ^ n * vecFourier (fun x => (u x : ℂ)) ξ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := vecFourier_euclideanCoordDeriv_of_isCc (isCc_iterate_euclideanCoordDeriv hu ℓ n) ℓ ξ
    rw [Function.iterate_succ_apply']
    rw [h, ih, pow_succ]
    ring

theorem vecFourier_foldr_iterate {u : Vec d → ℝ} (hu : IsCc u) (α : Fin d → ℕ)
    (l : List (Fin d)) (ξ : Vec d) :
    vecFourier (fun x => ((l.foldr (fun i g => (euclideanCoordDeriv i)^[α i] g) u) x : ℂ)) ξ =
      (l.map fun i => (2 * Real.pi * Complex.I * (ξ i : ℂ)) ^ α i).prod *
        vecFourier (fun x => (u x : ℂ)) ξ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have h := vecFourier_iterate_euclideanCoordDeriv (isCc_foldr_iterate hu α l) i (α i) ξ
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [h, ih]
    ring

/-- Fourier rule: `\\widehat{∂^α u}(ξ) = (2πi)^{|α|} ξ^α û(ξ)` for
`u ∈ C_c^∞`. -/
theorem vecFourier_multiCoordDeriv {u : Vec d → ℝ} (hu : IsCc u) (α : Fin d → ℕ) (ξ : Vec d) :
    vecFourier (fun x => ((multiCoordDeriv α u x : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I) ^ (∑ i, α i) * (((∏ i, ξ i ^ α i : ℝ)) : ℂ) *
        vecFourier (fun x => (u x : ℂ)) ξ := by
  unfold multiCoordDeriv
  rw [vecFourier_foldr_iterate hu α, ← Fin.prod_univ_def]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

/-- The cut-off system of strong constancy of order `k`:
`Σ_{|α|=k} A_α P₀ ∂^α w = Σ_{|α|=k} ∂^α G^{(α)} + Σ_{|β|≤k-1} ∂^β H_β` in `ℝ^κ`, at every point. -/
def IsSystemK {κ ι : Type*} [Fintype ι] (k : ℕ) (A : (Fin d → ℕ) → Matrix κ ι ℝ) (P₀ : ι → ℝ)
    (w : Vec d → ℝ) (G H : (Fin d → ℕ) → Vec d → κ → ℝ) : Prop :=
  ∀ x : Vec d, ∑ α ∈ Finset.Nat.antidiagonalTuple d k,
      multiCoordDeriv α w x • (A α *ᵥ P₀) =
    ∑ α ∈ Finset.Nat.antidiagonalTuple d k, multiCoordDerivVec α (G α) x +
      ∑ h ∈ Finset.range k, ∑ β ∈ Finset.Nat.antidiagonalTuple d h, multiCoordDerivVec β (H β) x

end

end AFree
