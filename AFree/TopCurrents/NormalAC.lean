module

public import AFree.TopCurrents.NormalACCoord
public import AFree.Proofs.SpanAbsContProof

/-!
# Top-dimensional normal currents are absolutely continuous

The proof applies [DPR, Corollary 1.12] to the `1`-currents `T_i = λ e_i`.
-/

@[expose] public section

open MeasureTheory

namespace AFree

open PDE

private lemma polar_coordOne_ae {d : ℕ} (N : VectorMeasure (Vec d) (KVec d d)) :
    ∀ᵐ x ∂euclideanVariation N, ∀ i j : Fin d,
      polar (coordOneCurrent N i) x (oneIdx j) =
        if j = i then (coordMeasure N (topKIdx d)).rnDeriv (euclideanVariation N) x else 0 := by
  rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
  by_cases h : j = i
  · subst h
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [polar]
    rw [euclideanVariation_coordOneCurrent]
    simp only [↓reduceIte]
    unfold coordOneCurrent
    rw [coordMeasure_coordSingle_self]
  · have hne : oneIdx j ≠ oneIdx i := fun e => h (oneIdx_injective e)
    have h0 : coordMeasure (coordOneCurrent N i) (oneIdx j) = 0 :=
      coordMeasure_coordSingle_ne N (topKIdx d) hne
    have := SignedMeasure.eq_rnDeriv (μ := euclideanVariation N) (s := (0 : SignedMeasure (Vec d)))
      (0 : SignedMeasure (Vec d)) (fun _ => 0) (integrable_zero _ _ _)
      (VectorMeasure.MutuallySingular.zero_left)
      (by rw [show ((fun _ => 0 : Vec d → ℝ)) = 0 from rfl, withDensityᵥ_zero, add_zero])
    filter_upwards [this] with x hx
    simp only [polar, euclideanVariation_coordOneCurrent, h0, h, ↓reduceIte]
    exact hx.symm

private lemma span_smul_single {d : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) :
    Submodule.span ℝ (Set.range fun i : Fin d => ρ • (Pi.single i 1 : Vec d)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ j, (v j / ρ) • (ρ • (Pi.single j 1 : Vec d)) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, hρ]
  rw [hv]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- `|T_i|` does not depend on `i`, the polars `ρ e_i` span `ℝ^d`
`σ`-a.e. and [DPR, Corollary 1.12] gives `σ ≪ 𝓛^d`. -/
theorem normalac_variation_ac {d : ℕ} (hd : 0 < d) {N : VectorMeasure (Vec d) (KVec d d)}
    (hN : IsNormalCurrentOn Set.univ N) : euclideanVariation N ≪ volume := by
  obtain ⟨S', hS'⟩ := hN.2
  have hT := coordOneCurrent_normal hd hS'
  refine SpanAbsContProof.result (fun i => coordOneCurrent N i) hT
    (euclideanVariation N)
    (fun i => by rw [euclideanVariation_coordOneCurrent]) ?_
  set i0 : Fin d := ⟨0, hd⟩
  have h3 := piEuclideanNorm_polar_eq_one (coordOneCurrent N i0)
  rw [euclideanVariation_coordOneCurrent] at h3
  filter_upwards [h3, polar_coordOne_ae N] with x hx1 hx2
  set ρ := (coordMeasure N (topKIdx d)).rnDeriv (euclideanVariation N) x
  have hρ : ρ ≠ 0 := by
    intro h0
    have : polar (coordOneCurrent N i0) x = 0 := by
      funext I
      obtain ⟨j, rfl⟩ : ∃ j, I = oneIdx j := by
        obtain ⟨s, hs⟩ := I
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hs
        exact ⟨j, rfl⟩
      rw [hx2 i0 j]; simp [h0]
    rw [this] at hx1
    simp [piEuclideanNorm] at hx1
  have : ∀ i : Fin d, kvecOneToVec (polar (coordOneCurrent N i) x) =
      ρ • (Pi.single i 1 : Vec d) := by
    intro i; funext j
    simp only [kvecOneToVec]
    have := hx2 i j
    change polar (coordOneCurrent N i) x (oneIdx j) = _ at *
    rw [this]
    by_cases h : j = i <;> simp [h]
  simp only [this]
  exact span_smul_single hρ

/-- Let `N` be a `Λ_d`-valued normal current on `ℝ^d` and `λ = N_top`
(`coordMeasure N (topKIdx d)`). If `E` is Borel and `𝓛^d(E) = 0` then `λ(E) = 0`. -/
theorem normalac {d : ℕ} {N : VectorMeasure (Vec d) (KVec d d)}
    (hN : IsNormalCurrentOn Set.univ N) {E : Set (Vec d)} (hE : MeasurableSet E)
    (hE0 : volume E = 0) : coordMeasure N (topKIdx d) E = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : E = ∅ := by
      by_contra hne
      have hE' : E = Set.univ := Set.eq_univ_of_forall fun x =>
        by obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne; rwa [Subsingleton.elim x y]
      rw [hE'] at hE0
      exact (isOpen_univ.measure_pos _ Set.univ_nonempty).ne' hE0
    subst this
    simp
  · have h0 := normalac_variation_ac hd hN hE0
    have h1 := ofReal_piEuclideanNorm_le_euclideanVariation N E
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, piEuclideanNorm_topKVec] at h1
    rw [coordMeasure_apply]
    exact abs_nonpos_iff.mp h1

end AFree
