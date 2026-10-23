module

public import AFree.Curves.Bundle.Resolvent
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.LinearAlgebra.Trace

/-!
# Borel subspace fields: weighted sums, resolvents and dimension

Ingredients for the Borel measurability of countable intersections of subspace fields: the kernel of a
weighted sum of projections, the resolvent limit, and the dimension.
-/

@[expose] public section

open Matrix Filter Topology MeasureTheory

namespace AFree.Bundle

variable {d : ℕ}

/-- `P` is the matrix of the orthogonal projection onto `W`. -/
def IsProjMat (P : Matrix (Fin d) (Fin d) ℝ) (W : Submodule ℝ (Fin d → ℝ)) : Prop :=
  Pᵀ = P ∧ P * P = P ∧ LinearMap.range (Matrix.toLin' P) = W

variable {P : Matrix (Fin d) (Fin d) ℝ} {W : Submodule ℝ (Fin d → ℝ)}

theorem IsProjMat.mem_iff (h : IsProjMat P W) (y : Fin d → ℝ) : y ∈ W ↔ P *ᵥ y = y := by
  rw [← h.2.2]
  constructor
  · rintro ⟨x, rfl⟩
    simp only [Matrix.toLin'_apply]
    rw [mulVec_mulVec, h.2.1]
  · intro hy
    exact ⟨y, by simpa using hy⟩

theorem IsProjMat.mulVec_mem (h : IsProjMat P W) (y : Fin d → ℝ) : P *ᵥ y ∈ W := by
  rw [← h.2.2]; exact ⟨y, by simp⟩

/-- A symmetric idempotent matrix is determined by its range. -/
theorem IsProjMat.unique {P' : Matrix (Fin d) (Fin d) ℝ} (h : IsProjMat P W)
    (h' : IsProjMat P' W) : P = P' := by
  have h1 : P' * P = P := matrix_ext_mulVec fun y => by
    rw [← mulVec_mulVec, (h'.mem_iff _).1 (h.mulVec_mem y)]
  have h2 : P * P' = P' := matrix_ext_mulVec fun y => by
    rw [← mulVec_mulVec, (h.mem_iff _).1 (h'.mulVec_mem y)]
  have h3 : P' * P = P' := by
    have := congrArg Matrix.transpose h2
    rwa [transpose_mul, h.1, h'.1] at this
  rw [← h1, h3]

/-- The weighted sum `A = ∑_{n<N} (I - P_n)`. -/
def wsum (P : ℕ → Matrix (Fin d) (Fin d) ℝ) (N : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ n ∈ Finset.range N, (1 - P n)

private theorem dot_proj (h : IsProjMat P W) (y : Fin d → ℝ) :
    y ⬝ᵥ ((1 - P) *ᵥ y) = ((1 - P) *ᵥ y) ⬝ᵥ ((1 - P) *ᵥ y) := by
  have hs : (1 - P)ᵀ = 1 - P := by rw [transpose_sub, transpose_one, h.1]
  have hm : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, h.2.1]; abel
  rw [dot_comm_of_symm hs, mulVec_mulVec, hm]

/-- For orthogonal projection matrices `P_n` onto `W_n`,
`A = ∑_{n<N} (I - P_n)` is symmetric positive semidefinite and `ker A = ⋂_{n<N} W_n`. -/
theorem kernel_of_weighted_sum {P : ℕ → Matrix (Fin d) (Fin d) ℝ} {W : ℕ → Submodule ℝ (Fin d → ℝ)}
    (hP : ∀ n, IsProjMat (P n) (W n)) (N : ℕ) :
    IsSymmPSD (wsum P N) ∧ ∀ y, wsum P N *ᵥ y = 0 ↔ ∀ n < N, y ∈ W n := by
  have hq : ∀ y, y ⬝ᵥ (wsum P N *ᵥ y) =
      ∑ n ∈ Finset.range N, ((1 - P n) *ᵥ y) ⬝ᵥ ((1 - P n) *ᵥ y) := fun y => by
    rw [wsum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun n _ => dot_proj (hP n) y
  have hnn : ∀ y, 0 ≤ y ⬝ᵥ (wsum P N *ᵥ y) := fun y => by
    rw [hq]; exact Finset.sum_nonneg fun n _ => dot_self_nonneg _
  refine ⟨⟨?_, hnn⟩, fun y => ?_⟩
  · rw [wsum, transpose_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [transpose_sub, transpose_one, (hP n).1]
  · constructor
    · intro hy n hn
      have h0 : ∑ n ∈ Finset.range N, ((1 - P n) *ᵥ y) ⬝ᵥ ((1 - P n) *ᵥ y) = 0 := by
        rw [← hq, hy, dotProduct_zero]
      have := (Finset.sum_eq_zero_iff_of_nonneg fun n _ => dot_self_nonneg _).1 h0 n
        (Finset.mem_range.2 hn)
      have h1 : (1 - P n) *ᵥ y = 0 := dotProduct_self_eq_zero.1 this
      rw [(hP n).mem_iff]
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at h1
      exact h1.symm
    · intro hy
      rw [wsum, Matrix.sum_mulVec]
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [sub_mulVec, one_mulVec, ((hP n).mem_iff y).1 (hy n (Finset.mem_range.1 hn)), sub_self]

section Measurability

variable {α : Type*} [MeasurableSpace α]

/-- All entries of a matrix-valued map are measurable. -/
def EntryMeas (A : α → Matrix (Fin d) (Fin d) ℝ) : Prop := ∀ i j, Measurable fun x => A x i j

theorem EntryMeas.measurable {A : α → Matrix (Fin d) (Fin d) ℝ} (h : EntryMeas A) :
    Measurable A :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => h i j

theorem entryMeas_of_measurable {A : α → Matrix (Fin d) (Fin d) ℝ} (h : Measurable A) :
    EntryMeas A := fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h)

/-- Matrix inversion is Borel (`A⁻¹ = det⁻¹ • adj A`, with `det`, `adj` polynomial). -/
theorem measurable_matrix_inv : Measurable (fun B : Matrix (Fin d) (Fin d) ℝ => B⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

theorem entryMeas_resolvent {A : α → Matrix (Fin d) (Fin d) ℝ} (hA : EntryMeas A) (m : ℕ) :
    EntryMeas fun x => resolvent (A x) m := by
  have h1 : EntryMeas fun x => (((m : ℝ) + 1) • A x + 1) := fun i j => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((hA i j).const_mul _).add_const _
  exact entryMeas_of_measurable (measurable_matrix_inv.comp h1.measurable)

theorem entryMeas_wsum {P : ℕ → α → Matrix (Fin d) (Fin d) ℝ} (hP : ∀ n, EntryMeas (P n)) (N : ℕ) :
    EntryMeas fun x => wsum (fun n => P n x) N := fun i j => by
  simp only [wsum, Matrix.sum_apply, Matrix.sub_apply]
  exact Finset.measurable_sum _ fun n _ => (hP n i j).const_sub _

/-- The projection onto the kernel of a Borel
family of symmetric positive semidefinite matrices is a Borel family. -/
theorem entryMeas_kerProj {A : α → Matrix (Fin d) (Fin d) ℝ} (hA : EntryMeas A)
    (hs : ∀ x, IsSymmPSD (A x)) : EntryMeas fun x => kerProj (A x) := fun i j => by
  refine measurable_of_tendsto_metrizable (f := fun m x => resolvent (A x) m i j) ?_ ?_
  · exact fun m => entryMeas_resolvent hA m i j
  · rw [tendsto_pi_nhds]
    intro x
    exact (((continuous_apply j).comp (continuous_apply i)).tendsto _).comp (hs x).tendsto_kerProj

end Measurability

end AFree.Bundle
