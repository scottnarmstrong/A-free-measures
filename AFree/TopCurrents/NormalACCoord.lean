module

public import AFree.TopCurrents.BdTop
public import AFree.TopCurrents.NormalACAux

/-!
# The coordinate `1`-currents `T_i = λ e_i` of a top-dimensional normal current

For `N` a normal `Λ_d`-valued current and `λ = N_top`, the `Λ_1`-valued measure `T_i` with the single
coordinate `{i} ↦ λ` is a normal `1`-current with boundary `S_i = (-1)^i S'(J_i)`.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

/-- The index `{i}` of `Λ_1`. -/
def oneIdx {d : ℕ} (i : Fin d) : KIdx d 1 := ⟨{i}, Finset.card_singleton i⟩

lemma oneIdx_injective {d : ℕ} : Function.Injective (oneIdx (d := d)) := fun i j h => by
  have := congrArg Subtype.val h
  simpa [oneIdx] using this

/-- `T_i = λ e_i` with `λ = N_top`. -/
noncomputable def coordOneCurrent {d : ℕ} (N : VectorMeasure (Vec d) (KVec d d)) (i : Fin d) :
    VectorMeasure (Vec d) (KVec d 1) :=
  coordSingle N (topKIdx d) (oneIdx i)

lemma topKIdx_unique {d : ℕ} (I : KIdx d d) : I = topKIdx d :=
  Subtype.ext (Finset.eq_univ_of_card I.1 (by simpa using I.2))

lemma piEuclideanNorm_topKVec {d : ℕ} (v : KVec d d) : piEuclideanNorm v = |v (topKIdx d)| := by
  unfold piEuclideanNorm
  have : ∑ I, v I * v I = v (topKIdx d) * v (topKIdx d) := by
    rw [Finset.sum_eq_single (topKIdx d)]
    · intro I _ hI; exact absurd (topKIdx_unique I) hI
    · simp
  rw [this, Real.sqrt_mul_self_eq_abs]

lemma coordOneCurrent_norm {d : ℕ} (N : VectorMeasure (Vec d) (KVec d d)) (i : Fin d)
    (E : Set (Vec d)) : piEuclideanNorm (coordOneCurrent N i E) = piEuclideanNorm (N E) := by
  rw [coordOneCurrent, coordSingle_norm, piEuclideanNorm_topKVec]

lemma euclideanVariation_coordOneCurrent {d : ℕ} (N : VectorMeasure (Vec d) (KVec d d))
    (i : Fin d) : euclideanVariation (coordOneCurrent N i) = euclideanVariation N :=
  euclideanVariation_eq_of_norm_eq _ _ (coordOneCurrent_norm N i)

/-- `T_i = λ e_i` is a normal `1`-current. -/
theorem coordOneCurrent_normal {d : ℕ} (hd : 0 < d) {N : VectorMeasure (Vec d) (KVec d d)}
    {S' : VectorMeasure (Vec d) (KVec d (d - 1))} (hS : IsBoundaryOn Set.univ N S') (i : Fin d) :
    IsNormalCurrentOn Set.univ (coordOneCurrent N i) := by
  refine ⟨by simp, ?_⟩
  let Ji : KIdx d (d - 1) := ⟨Finset.univ.erase i, by simp⟩
  let J0 : KIdx d (1 - 1) := ⟨∅, by simp⟩
  refine ⟨((-1 : ℝ) ^ (i : ℕ)) • coordSingle S' Ji J0, by simp, fun φ hφ J => ?_⟩
  have hJ : J = J0 := Subtype.ext (Finset.card_eq_zero.1 (by simpa using J.2))
  subst hJ
  obtain ⟨hm, C, hC⟩ := hφ.measurable_bound
  have hL : (∫ᵛ x, φ x ∂•(((-1 : ℝ) ^ (i : ℕ)) • coordSingle S' Ji J0)) J0 =
      (∫ᵛ x, euclideanCoordDeriv i φ x ∂•N) (topKIdx d) := by
    rw [VectorMeasure.integral_smul_vectorMeasure, Pi.smul_apply,
      integral_coordSingle_self S' Ji J0 hm hC, bdtop hd hS hφ i, smul_eq_mul, ← mul_assoc,
      ← mul_pow]
    simp
  rw [hL]
  have hf : Finset.univ.filter (· ∉ J0.1) = Finset.univ := by ext j; simp [J0]
  rw [hf, Finset.sum_eq_single i]
  · obtain ⟨hm', C', hC'⟩ := (hφ.coordDeriv i).measurable_bound
    have hc : (insert i J0.1).card = 1 := by simp [J0]
    simp only [hc, ↓reduceDIte]
    have : (⟨insert i J0.1, hc⟩ : KIdx d 1) = oneIdx i := by simp [J0, oneIdx]
    rw [this, coordOneCurrent, integral_coordSingle_self N (topKIdx d) (oneIdx i) hm' hC']
    simp [insertSign, J0]
  · intro j _ hji
    obtain ⟨hm', C', hC'⟩ := (hφ.coordDeriv j).measurable_bound
    have hc : (insert j J0.1).card = 1 := by simp [J0]
    simp only [hc, ↓reduceDIte]
    have : (⟨insert j J0.1, hc⟩ : KIdx d 1) = oneIdx j := by simp [J0, oneIdx]
    rw [this, coordOneCurrent,
      integral_coordSingle_ne N (topKIdx d) (fun h => hji (oneIdx_injective h)) hm' hC']
    simp
  · simp

end AFree
