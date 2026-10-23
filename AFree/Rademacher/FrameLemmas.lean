module

public import AFree.Rademacher.Dot
public import PDEFoundation.Ambient.Basis
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Linear independence helpers for the frame construction
-/

@[expose] public section

open PDE

namespace AFree.Rademacher

variable {d : ℕ}

/-- An orthonormal family in `ℝ^d` is linearly independent. -/
theorem linearIndependent_of_orthonormal {m : ℕ} {v : Fin m → Vec d}
    (h : ∀ k l, vecDot (v k) (v l) = if k = l then 1 else 0) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have := congrArg (fun u => vecDot u (v l)) hg
  simp only [vecDot_sum_left, vecDot_smul_left, h, vecDot_zero_left] at this
  simpa using this

/-- An independent `m`-tuple extends to an independent `d`-tuple by standard basis vectors. -/
theorem exists_extend_independent {m : ℕ} (hm : m ≤ d) {v : ℕ → Vec d}
    (hv : LinearIndependent ℝ (fun k : Fin m => v k)) :
    ∃ w : ℕ → Vec d, (∀ k < m, w k = v k) ∧ LinearIndependent ℝ (fun k : Fin d => w k) := by
  have key : ∀ j, m ≤ j → j ≤ d → ∃ w : ℕ → Vec d, (∀ k < m, w k = v k) ∧
      LinearIndependent ℝ (fun k : Fin j => w k) := by
    intro j hmj
    induction j, hmj using Nat.le_induction with
    | base => intro _; exact ⟨v, fun _ _ => rfl, hv⟩
    | succ j hmj ih =>
      intro hj
      obtain ⟨w, hw1, hw2⟩ := ih (Nat.le_of_succ_le hj)
      have hex : ∃ a : Fin d, basisVec a ∉ Submodule.span ℝ (Set.range fun k : Fin j => w k) := by
        by_contra hcon
        push Not at hcon
        have htop : Submodule.span ℝ (Set.range fun k : Fin j => w k) = ⊤ := by
          rw [eq_top_iff]
          intro x _
          rw [← sum_smul_basisVec x]
          exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hcon a)
        have h1 := finrank_span_eq_card hw2
        rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
        omega
      obtain ⟨a, ha⟩ := hex
      refine ⟨fun n => if n = j then basisVec a else w n, fun k hk => ?_, ?_⟩
      · have : k ≠ j := by omega
        simp [this, hw1 k hk]
      · have hfun : (fun k : Fin (j + 1) => (fun n => if n = j then basisVec a else w n) k) =
            Fin.snoc (α := fun _ => Vec d) (fun k : Fin j => w k) (basisVec a) := by
          funext k
          refine Fin.lastCases ?_ (fun i => ?_) k
          · simp
          · have : (i : ℕ) ≠ j := i.2.ne
            simp [this]
        rw [hfun, linearIndependent_finSnoc]
        exact ⟨hw2, ha⟩
  obtain ⟨w, hw1, hw2⟩ := key d hm le_rfl
  exact ⟨w, hw1, hw2⟩

end AFree.Rademacher
