module

public import AFree.Curves.BundleTop.Test

/-!
# Dense axes and robust tuples of axes
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ}

/-- A countable dense family of unit vectors (`d ≥ 1`), dense for the Euclidean norm. -/
lemma exists_dense_axes (hd : 0 < d) :
    ∃ w : ℕ → Vec d, (∀ i, vecEuclideanNorm (w i) = 1) ∧
      ∀ v, vecEuclideanNorm v = 1 → ∀ ε > 0, ∃ i, vecEuclideanNorm (w i - v) < ε := by
  set S : Set (Vec d) := {v | vecEuclideanNorm v = 1} with hS
  have hne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
    show vecEuclideanNorm (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) = 1
    simp [vecEuclideanNorm, vecNormSq, vecDot, Pi.single_apply]
  have : Nonempty S := hne.to_subtype
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  refine ⟨fun i => (u i : Vec d), fun i => (u i).2, fun v hv ε hε => ?_⟩
  have hδ : 0 < ε / (Real.sqrt d + 1) := by positivity
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 hu ⟨v, hv⟩ _ hδ
  refine ⟨i, ?_⟩
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at hi
  simp only at hi
  have h1 := vecEuclideanNorm_le_sqrt_natCast_mul_norm ((u i : Vec d) - v)
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  calc vecEuclideanNorm ((u i : Vec d) - v) ≤ Real.sqrt d * ‖(u i : Vec d) - v‖ := h1
    _ ≤ Real.sqrt d * (ε / (Real.sqrt d + 1)) := mul_le_mul_of_nonneg_left hi.le hs
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith

variable {w : ℕ → Vec d} {M : ℕ → ℕ → Set (Vec d)} {x : Vec d}

/-- If `W(x) = ℝ^d` there are `d` admissible axes `(i_j, n_j)` with `x ∈ M_{i_j, n_j}`,
margin `η` and `√d / (n_j + 2) < η`. -/
lemma exists_robust_tuple (hx : selW w M x = ⊤) :
    ∃ τ : Fin d → ℕ × ℕ, (∀ j, x ∈ M (τ j).1 (τ j).2) ∧ ∃ η : ℝ,
      (∀ a : Vec d, η * vecEuclideanNorm a ≤ vecEuclideanNorm (∑ j, a j • w (τ j).1)) ∧
      ∀ j, Real.sqrt d * (1 / (((τ j).2 : ℝ) + 2)) < η := by
  have hk : d ≤ Module.finrank ℝ (Submodule.span ℝ (selK w M x)) := by
    have : Submodule.span ℝ (selK w M x) = ⊤ := hx
    rw [this, finrank_top, Module.finrank_fin_fun]
  obtain ⟨v, hv, hli⟩ := exists_indep_of_le_finrank hk
  obtain ⟨η, hη, hmar⟩ := exists_margin_of_linearIndependent hli
  obtain ⟨m0, hm0⟩ := exists_nat_gt (4 * Real.sqrt d / η)
  have hε : 0 < η / (4 * ((d : ℝ) + 1)) := by positivity
  have hd4 : (d : ℝ) * (η / (4 * ((d : ℝ) + 1))) ≤ η / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : ∀ j, ∃ i ∈ selI M m0 x, vecEuclideanNorm (w i - v j) < η / (4 * ((d : ℝ) + 1)) :=
    fun j => exists_axis_near (hv j) m0 hε
  choose i hi hd using this
  have : ∀ j, ∃ n, m0 ≤ n ∧ x ∈ M (i j) n := fun j => hi j
  choose n hn hxn using this
  refine ⟨fun j => (i j, n j), hxn, 3 * η / 4, ?_, fun j => ?_⟩
  · exact Margin.perturb hmar hd4 (fun j => (hd j).le)
  · have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have h1 : (4 * Real.sqrt d / η) < (m0 : ℝ) + 2 := by linarith
    have h2 : (m0 : ℝ) ≤ n j := by exact_mod_cast hn j
    have h3 : 4 * Real.sqrt d < η * ((n j : ℝ) + 2) := by
      rw [div_lt_iff₀ hη] at h1; nlinarith
    show Real.sqrt d * (1 / ((n j : ℝ) + 2)) < 3 * η / 4
    have hpos : (0 : ℝ) < (n j : ℝ) + 2 := by positivity
    rw [← mul_div_assoc, mul_one, div_lt_iff₀ hpos]
    nlinarith

end AFree.BundleTop
