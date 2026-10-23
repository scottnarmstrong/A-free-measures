module

public import AFree.Defs

/-!
# The boundary identity for top-dimensional currents

Unfolding of `IsBoundaryOn Set.univ N S'` for `N` with values in `Λ_d` and `S'` with values
in `Λ_{d-1}`: for `J_m = Fin d ∖ {m}` the only `j ∉ J_m` is `m`, and `insertSign m J_m = (-1)^m`.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

private lemma card_filter_lt_erase {d : ℕ} (m : Fin d) :
    ((Finset.univ.erase m).filter (· < m)).card = (m : ℕ) := by
  have h : (Finset.univ.erase m).filter (· < m) = Finset.Iio m := by
    ext i; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Iio]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  rw [h, Fin.card_Iio]

/-- For `d ≥ 1`, `IsBoundaryOn univ N S'` reads
`(∫ φ dS')(J_m) = (-1)^m (∫ ∂_m φ dN)(top)`, `J_m = Fin d ∖ {m}`. -/
theorem bdtop {d : ℕ} (_hd : 0 < d) {N : VectorMeasure (Vec d) (KVec d d)}
    {S' : VectorMeasure (Vec d) (KVec d (d - 1))} (hS : IsBoundaryOn Set.univ N S') {φ : Vec d → ℝ}
    (hφ : IsTestFunctionOn Set.univ φ) (m : Fin d) :
    (∫ᵛ x, φ x ∂•S') ⟨Finset.univ.erase m, by simp⟩ =
      (-1) ^ (m : ℕ) * (∫ᵛ x, euclideanCoordDeriv m φ x ∂•N) (topKIdx d) := by
  have h := hS.2 φ hφ ⟨Finset.univ.erase m, by simp⟩
  rw [h]
  have hf : Finset.univ.filter (· ∉ (Finset.univ.erase m)) = {m} := by
    ext j; simp [eq_comm]
  simp only [hf, Finset.sum_singleton]
  have hins : insert m (Finset.univ.erase m) = Finset.univ := Finset.insert_erase (Finset.mem_univ m)
  have hc : (insert m (Finset.univ.erase m)).card = d := by rw [hins]; simp
  simp only [hc, ↓reduceDIte]
  have : (⟨insert m (Finset.univ.erase m), hc⟩ : KIdx d d) = topKIdx d :=
    Subtype.ext hins
  rw [this, insertSign, card_filter_lt_erase]

end AFree
