module

public import AFree.Rademacher.X0

/-!
# The setting `(S)` of the single-stage perturbation

The hypotheses shared by the steps of the proof of [AM, Lemma 4.8].
-/

@[expose] public section

open PDE MeasureTheory

namespace AFree.Rademacher

variable {d : ℕ}

/-- The setting `(S)`: `d ≥ 1` (here witnessed by the index `i : Fin d`); `μ` a
finite measure on `ℝ^d`; `V` with `IsDecompTestField μ V`; `v = ε_i = basisVec i`; `m ∈ {1, …, d}`
and `δ > 0`; a compact `E` and a frame `e` such that for `x ∈ E` and `k < m` (one-based indexing would read `k ≤ m`): `e_k(x) ⊥ V(x)` and `∑_{k<m} (v · e_k(x))² ≥ δ²`. The
constant `D = δ / (3 √m)` is `setting_D δ m`, and `X₀ = X₀(e)` is `X0 e`. -/
structure Setting (μ : Measure (Vec d)) (V : Vec d → Submodule ℝ (Vec d)) (i : Fin d) (m : ℕ)
    (δ : ℝ) (E : Set (Vec d)) (e : Vec d → Fin d → Vec d) : Prop where
  finite : IsFiniteMeasure μ
  test : IsDecompTestField μ V
  m_pos : 1 ≤ m
  m_le : m ≤ d
  delta_pos : 0 < δ
  compact : IsCompact E
  frame : IsFrame e
  perp : ∀ x ∈ E, ∀ k : Fin d, (k : ℕ) < m → ∀ w ∈ V x, vecDot (e x k) w = 0
  sum_sq : ∀ x ∈ E,
    δ ^ 2 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin d => (k : ℕ) < m), vecDot (basisVec i) (e x k) ^ 2

/-- The constant `D = δ / (3 √m)` of the setting `(S)`. -/
noncomputable def settingD (δ : ℝ) (m : ℕ) : ℝ := δ / (3 * Real.sqrt m)

theorem Setting.settingD_pos {μ : Measure (Vec d)} {V : Vec d → Submodule ℝ (Vec d)} {i : Fin d}
    {m : ℕ} {δ : ℝ} {E : Set (Vec d)} {e : Vec d → Fin d → Vec d}
    (h : Setting μ V i m δ E e) : 0 < settingD δ m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast h.m_pos
  unfold settingD
  have := h.delta_pos
  positivity

end AFree.Rademacher
