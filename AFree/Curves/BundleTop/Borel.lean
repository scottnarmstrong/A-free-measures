module

public import AFree.Curves.BundleTop.Proj
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# `W` is a Borel subspace field

Matrices are encoded as functions
`Fin d → Fin d → ℝ` (a Polish space with its Borel structure) through `Matrix.of`.
-/

@[expose] public section

open Set Matrix MeasureTheory

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ} {w : ℕ → Vec d} {M : ℕ → ℕ → Set (Vec d)}

/-- The symmetric idempotent matrices `Π`. -/
private def PiSet (d : ℕ) : Set (Fin d → Fin d → ℝ) :=
  {P | (Matrix.of P)ᵀ = Matrix.of P ∧ Matrix.of P * Matrix.of P = Matrix.of P}

private lemma isClosed_PiSet : IsClosed (PiSet d) := by
  have hc : Continuous fun P : Fin d → Fin d → ℝ => Matrix.of P := continuous_id
  exact (isClosed_eq hc.matrix_transpose hc).inter (isClosed_eq (hc.matrix_mul hc) hc)

/-- `Γ_k = {(x, P) : x ∈ R_k, P ∈ Π_k, Φ(x, P) = 0}`. -/
private def Gam (w : ℕ → Vec d) (M : ℕ → ℕ → Set (Vec d)) (k : ℕ) :
    Set (Vec d × (Fin d → Fin d → ℝ)) :=
  {p | Module.finrank ℝ (selW w M p.1) = k ∧ p.2 ∈ PiSet d ∧ (Matrix.of p.2).trace = k ∧
    ∀ v ∈ selK w M p.1, Matrix.of p.2 *ᵥ v = v}

private lemma measurableSet_Gam (hw : ∀ i, vecEuclideanNorm (w i) = 1)
    (hM : ∀ i n, MeasurableSet (M i n)) (k : ℕ) : MeasurableSet (Gam w M k) := by
  have h1 : MeasurableSet {p : Vec d × (Fin d → Fin d → ℝ) |
      Module.finrank ℝ (selW w M p.1) = k} :=
    (measurableSet_finrank_eq hw hM k).preimage measurable_fst
  have h2 : MeasurableSet {p : Vec d × (Fin d → Fin d → ℝ) | p.2 ∈ PiSet d} :=
    isClosed_PiSet.measurableSet.preimage measurable_snd
  have h3 : MeasurableSet {p : Vec d × (Fin d → Fin d → ℝ) | (Matrix.of p.2).trace = k} := by
    have hc : Continuous fun P : Fin d → Fin d → ℝ => (Matrix.of P).trace := by
      simp only [Matrix.trace, Matrix.diag_apply]
      exact continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
    exact (isClosed_eq hc continuous_const).measurableSet.preimage measurable_snd
  exact (h1.inter (h2.inter (h3.inter (measurableSet_fixed hM hw)))).congr (by
    ext p; simp [Gam])

private lemma Gam_isProj {k : ℕ} {p : Vec d × (Fin d → Fin d → ℝ)} (hp : p ∈ Gam w M k) :
    IsProj (Matrix.of p.2) (selW w M p.1) := by
  obtain ⟨hk, ⟨hs, hi⟩, ht, hfix⟩ := hp
  have hle : selW w M p.1 ≤ LinearMap.range (Matrix.toLin' (Matrix.of p.2)) := by
    refine Submodule.span_le.2 fun v hv => ⟨v, ?_⟩
    simp [Matrix.toLin'_apply, hfix v hv]
  have hpr : IsProj (Matrix.of p.2) (LinearMap.range (Matrix.toLin' (Matrix.of p.2))) :=
    ⟨hs, hi, rfl⟩
  have hfr : Module.finrank ℝ (LinearMap.range (Matrix.toLin' (Matrix.of p.2))) = k := by
    have := hpr.trace_eq
    rw [ht] at this
    exact_mod_cast this.symm
  have := Submodule.eq_of_le_of_finrank_eq hle (by rw [hk, hfr])
  exact ⟨hs, hi, this.symm⟩

private lemma Gam_unique {k : ℕ} {p q : Vec d × (Fin d → Fin d → ℝ)} (hp : p ∈ Gam w M k)
    (hq : q ∈ Gam w M k) (h : p.1 = q.1) : p = q := by
  have h1 := Gam_isProj hp
  have h2 := Gam_isProj hq
  rw [← h] at h2
  exact Prod.ext h (funext fun i => funext fun j => congrFun (congrFun (h1.unique h2) i) j)

/-- The chosen projection matrix onto `W(x)`, as a function. -/
private noncomputable def projField (w : ℕ → Vec d) (M : ℕ → ℕ → Set (Vec d)) (x : Vec d) :
    Fin d → Fin d → ℝ :=
  fun i j => (exists_isProj (selW w M x)).choose i j

private lemma projField_isProj (x : Vec d) :
    IsProj (Matrix.of (projField w M x)) (selW w M x) :=
  (exists_isProj (selW w M x)).choose_spec

private lemma mem_Gam_projField (x : Vec d) :
    (x, projField w M x) ∈ Gam w M (Module.finrank ℝ (selW w M x)) := by
  have h := projField_isProj (w := w) (M := M) x
  refine ⟨rfl, ⟨h.1, h.2.1⟩, ?_, fun v hv => ?_⟩
  · exact h.trace_eq
  · exact (h.mem_iff v).1 (Submodule.subset_span hv)

/-- Borel selection of the projection (Lusin–Souslin). -/
private lemma measurable_projField (hw : ∀ i, vecEuclideanNorm (w i) = 1)
    (hM : ∀ i n, MeasurableSet (M i n)) : Measurable (projField w M) := by
  refine measurable_of_isOpen fun U hU => ?_
  have : projField w M ⁻¹' U = ⋃ k : ℕ, Prod.fst '' (Gam w M k ∩ Prod.snd ⁻¹' U) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_image, mem_inter_iff]
    constructor
    · intro hx
      exact ⟨_, (x, projField w M x), ⟨mem_Gam_projField x, hx⟩, rfl⟩
    · rintro ⟨k, p, ⟨hp, hpU⟩, rfl⟩
      have hq := mem_Gam_projField (w := w) (M := M) p.1
      have hk : Module.finrank ℝ (selW w M p.1) = k := hp.1
      rw [hk] at hq
      have := Gam_unique hp hq rfl
      rw [this] at hpU
      exact hpU
  rw [this]
  refine MeasurableSet.iUnion fun k => ?_
  refine MeasurableSet.image_of_continuousOn_injOn
    ((measurableSet_Gam hw hM k).inter (hU.measurableSet.preimage measurable_snd))
    continuous_fst.continuousOn ?_
  intro p hp q hq h
  exact Gam_unique hp.1 hq.1 h

/-- The field `W(x) = span K(x)` is a Borel subspace field. Here `w i` are unit
axes and `M i n` measurable sets (`M i n = N_{i,n}ᶜ`, aperture `1 / (n + 2)`). -/
theorem opt_borel (hw : ∀ i, vecEuclideanNorm (w i) = 1) (hM : ∀ i n, MeasurableSet (M i n)) :
    IsBorelSubspaceField (selW w M) := by
  refine ⟨fun x => Matrix.of (projField w M x), fun i j => ?_, fun x => ?_⟩
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_projField hw hM))
  · exact projField_isProj x

end AFree.BundleTop
