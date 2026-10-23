module

public import AFree.Paper.MainPair

/-!
# Reindexing the carriers

The main theorem for pairs, transported from the carriers `Fin m`, `Fin n` to arbitrary finite
index types along `Fintype.equivFin`.
-/

@[expose] public section

open MeasureTheory Matrix

namespace AFree

open PDE

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reindexing `v ↦ v ∘ e.symm` as a continuous linear equivalence. -/
noncomputable def reindexCLE {m : ℕ} (e : ι ≃ Fin m) : (ι → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toContinuousLinearEquiv

theorem reindexCLE_apply {m : ℕ} (e : ι ≃ Fin m) (v : ι → ℝ) :
    reindexCLE e v = v ∘ e.symm := rfl

omit [Fintype κ] in
/-- `𝒜`-freeness transfers along the reindexing. -/
theorem isFreePair_reindex {d m n : ℕ} {Ω : Set (Vec d)} (e : ι ≃ Fin m) (f : κ ≃ Fin n)
    {A : Fin d → Matrix κ ι ℝ} {A₀ : Matrix κ ι ℝ} {σ : Measure (Vec d)} {P : Vec d → ι → ℝ}
    (h : IsFreePair Ω A A₀ σ P) :
    IsFreePair Ω (fun ℓ => (A ℓ).submatrix f.symm e.symm) (A₀.submatrix f.symm e.symm) σ
      (fun x => reindexCLE e (P x)) := by
  refine ⟨h.1, fun φ hφ => ?_⟩
  have key : ∀ g : Vec d → ℝ, ∫ x, g x • reindexCLE e (P x) ∂σ =
      reindexCLE e (∫ x, g x • P x ∂σ) := fun g => by
    rw [← (reindexCLE e).integral_comp_comm]
    simp
  have hw : ∀ (B : Matrix κ ι ℝ) (v : ι → ℝ),
      B.submatrix f.symm e.symm *ᵥ reindexCLE e v = (B *ᵥ v) ∘ f.symm := fun B v => by
    rw [Matrix.submatrix_mulVec_equiv, reindexCLE_apply]
    congr 2
    funext i; simp
  rw [key, hw]
  have := h.2 φ hφ
  rw [this]
  funext k
  simp only [key, hw, Finset.sum_apply, Function.comp_apply]

/-- For `𝒜`-free `(σ, P)`, `P ∈ Λ_𝒜` at `σˢ`-a.e. point; general finite carriers. -/
theorem ae_mem_waveCone_of_isFreePair' {d : ℕ} {Ω : Set (Vec d)} (hΩ : IsOpen Ω)
    {A : Fin d → Matrix κ ι ℝ} {A₀ : Matrix κ ι ℝ}
    (σ : Measure (Vec d)) [IsFiniteMeasure σ] {P : Vec d → ι → ℝ}
    (hPm : Measurable P) (hPi : Integrable P σ) (h : IsFreePair Ω A A₀ σ P) :
    ∀ᵐ x ∂σ.singularPart volume, P x ∈ waveConeFirstOrder A := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set f : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hm : Measurable fun x => reindexCLE e (P x) := (reindexCLE e).continuous.measurable.comp hPm
  have hi : Integrable (fun x => reindexCLE e (P x)) σ :=
    ((reindexCLE e).toContinuousLinearMap.integrable_comp hPi)
  filter_upwards [ae_mem_waveCone_of_isFreePair hΩ σ hm hi (isFreePair_reindex e f h)] with x hx
  obtain ⟨ξ, hξ, hξP⟩ := hx
  refine ⟨ξ, hξ, ?_⟩
  have hs : (∑ ℓ, ξ ℓ • (A ℓ).submatrix f.symm e.symm) =
      (∑ ℓ, ξ ℓ • A ℓ).submatrix f.symm e.symm := by
    ext i j; simp [Matrix.sum_apply]
  rw [hs, show reindexCLE e (P x) = reindexCLE e (P x) from rfl] at hξP
  have hw := Matrix.submatrix_mulVec_equiv (∑ ℓ, ξ ℓ • A ℓ) (reindexCLE e (P x)) f.symm e.symm
  rw [hw] at hξP
  funext k
  have := congrFun hξP (f k)
  have e2 : (P x ∘ e.symm) ∘ e = P x := by funext i; simp
  simpa [reindexCLE_apply, e2] using this

end AFree
