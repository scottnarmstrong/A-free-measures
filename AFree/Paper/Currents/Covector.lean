module

public import AFree.Proofs.FirstOrderMainProof
public import AFree.Paper.Currents.Free
public import AFree.Paper.DivAssembly
public import AFree.Measure.Decomp.Singular

/-!
# Theorem 1.10: a common covector annihilating the polars

[DPR, Theorem 1.10]. The first-order main theorem `polar_mem_waveConeFirstOrder` is the only external
input.
-/

public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {d r : ℕ}

/-- The polar of `𝐓` lies in the wave cone `Λ_A` at `|𝐓|ˢ`-a.e. point. -/
theorem ae_polar_blockMeasure_mem_waveCone_system {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    (k : Fin r → ℕ) (T : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i)))
    (hT : ∀ i, IsNormalCurrentOn Ω (T i)) :
    ∀ᵐ x ∂(euclideanVariation (blockMeasure T)).singularPart volume,
      polar (blockMeasure T) x ∈ waveConeFirstOrder (systemCoeff k) := by
  choose S hS using fun i => (hT i).2
  obtain ⟨h1, h2, h3⟩ := blockMeasure_system_free k T S (fun i => (hT i).1) hS
  have hfree := isFirstOrderFree_augmented_of_rhs Ω (systemCoeff k) 0 (blockMeasure T)
    (blockMeasure S) h3
  have hcompl := euclideanVariation_augmentedMeasure_compl_eq_zero _ _ h1 h2
  exact ae_polar_mem_waveCone_of_augmented (systemCoeff k) _ _
    (FirstOrderMainProof.result Ω hΩ _ _ _ hcompl hfree)

/-- The case `r = 0`. -/
theorem ae_exists_covector_of_isEmpty (k : Fin 0 → ℕ)
    (T : (i : Fin 0) → VectorMeasure (Vec d) (KVec d (k i))) (μ : Measure (Vec d)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ ω : Vec d, ω ≠ 0 ∧
      ∀ i, interiorProduct (polar (T i) x) ω = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ae_singularPart_of_dimZero μ _
  · refine Filter.Eventually.of_forall fun x => ⟨Pi.single ⟨0, hd⟩ 1, ?_, fun i => i.elim0⟩
    intro h
    have := congrFun h ⟨0, hd⟩
    simp at this

/-- [DPR, Theorem 1.10]: for `μˢ`-a.e. `x` there is `ω ≠ 0` with `polar(Tᵢ)(x) ⌟ ω = 0`
for all `i`. (`hμΩ`, `hμloc` are premises of the paper's statement that the proof does not use.) -/
theorem ae_exists_covector_interiorProduct_eq_zero (Ω : Set (Vec d)) (hΩ : IsOpen Ω)
    (k : Fin r → ℕ) (_hk : ∀ i, 1 ≤ k i ∧ k i ≤ d)
    (T : (i : Fin r) → VectorMeasure (Vec d) (KVec d (k i)))
    (hT : ∀ i, IsNormalCurrentOn Ω (T i))
    (μ : Measure (Vec d)) (_hμΩ : μ Ωᶜ = 0) (_hμloc : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hμ : ∀ i, μ ≪ euclideanVariation (T i)) :
    ∀ᵐ x ∂μ.singularPart volume, ∃ ω : Vec d, ω ≠ 0 ∧
      ∀ i, interiorProduct (polar (T i) x) ω = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ae_exists_covector_of_isEmpty k T μ
  have i0 : Fin r := ⟨0, hr⟩
  -- Step 2: from `|𝐓|ˢ` to `μˢ`
  have hμT : μ ≪ euclideanVariation (blockMeasure T) :=
    (hμ i0).trans (euclideanVariation_absolutelyContinuous_blockMeasure T i0)
  have hsa : μ.singularPart volume ≪ (euclideanVariation (blockMeasure T)).singularPart volume :=
    singularPart_absolutelyContinuous_of_ac μ _ hμT
  have hcone := hsa.ae_le (ae_polar_blockMeasure_mem_waveCone_system hΩ k T hT)
  -- Step 3: the Radon-Nikodym chain
  have hle : μ.singularPart volume ≪ μ := Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)
  have hprop := (hμT.ae_le (polar_blockMeasure_ae T))
  have hpos : ∀ᵐ x ∂μ, ∀ i, 0 < ((euclideanVariation (T i)).rnDeriv
      (euclideanVariation (blockMeasure T)) x).toReal :=
    ae_all_iff.2 fun i => (hμ i).ae_le (rnDeriv_blockMeasure_pos T i)
  filter_upwards [hcone, hle.ae_le hprop, hle.ae_le hpos] with x hx hxp hxc
  -- Step 4: conclusion
  obtain ⟨ξ, hξ, hξP⟩ := (mem_waveConeFirstOrder_systemCoeff_iff k _).1 hx
  refine ⟨ξ, ?_, fun i => ?_⟩
  · rintro rfl
    have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
    rw [this] at hξ
    exact zero_ne_one hξ
  · have h := hξP i
    rw [hxp i] at h
    have h2 := interiorProduct_smul (((euclideanVariation (T i)).rnDeriv
      (euclideanVariation (blockMeasure T)) x).toReal) (polar (T i) x) ξ
    rw [h2] at h
    exact (smul_eq_zero.1 h).resolve_left (hxc i).ne'

end AFree
