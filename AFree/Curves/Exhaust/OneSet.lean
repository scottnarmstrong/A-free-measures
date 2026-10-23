module

public import AFree.Defs.Finite
public import AFree.Defs

/-!
# The one-set bound `|T(B)| ≤ |T|(B)` and `1`-vectors
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

/-- For a vector measure `T` into `ℝ^ι` and every set `B`,
`|T(B)| ≤ |T|(B)` (Euclidean norm, `|T| = euclideanVariation T`). -/
theorem piEuclideanNorm_apply_le_euclideanVariation {ι : Type*} [Fintype ι] {X : Type*}
    [MeasurableSpace X] (T : VectorMeasure X (ι → ℝ)) (B : Set X) :
    ENNReal.ofReal (piEuclideanNorm (T B)) ≤ euclideanVariation T B :=
  ofReal_piEuclideanNorm_le_euclideanVariation T B

/-- On `1`-vectors the Euclidean norm is that of the associated vector of `ℝ^d`. -/
lemma piEuclideanNorm_kvecOne {d : ℕ} (v : KVec d 1) :
    piEuclideanNorm v = vecEuclideanNorm (kvecOneToVec v) := by
  have hbij : ∀ K : KIdx d 1, ∃ j : Fin d, K = ⟨{j}, Finset.card_singleton j⟩ := fun K => by
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 K.2
    exact ⟨j, Subtype.ext hj⟩
  let f : Fin d → KIdx d 1 := fun j => ⟨{j}, Finset.card_singleton j⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => ?_, fun K => ?_⟩
    · have := congrArg Subtype.val h
      simpa [f] using this
    · obtain ⟨j, hj⟩ := hbij K
      exact ⟨j, hj.symm⟩
  have hsum : ∑ K : KIdx d 1, v K * v K = ∑ j : Fin d, v (f j) * v (f j) :=
    (Equiv.ofBijective f hf).sum_comp (fun K => v K * v K) |>.symm
  simp only [piEuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, kvecOneToVec, hsum]
  rfl

end AFree
