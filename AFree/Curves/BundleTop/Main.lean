module

public import AFree.Curves.BundleTop.Choice
public import AFree.Curves.Exhaust

/-!
# The decomposability bundle `⊤` implies absolute continuity

If `V = ℝ^d` `μ`-a.e. for a decomposability bundle `V`, then `μ ≪ vol^d`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace AFree

open PDE AFree.Curves AFree.BundleTop

private lemma volume_null_vec_zero (S : Set (Vec 0)) (hS : volume S = 0) : S = ∅ := by
  by_contra h
  obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 h
  have : (volume : Measure (Vec 0)) = Measure.dirac y := by
    rw [volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  rw [this, Measure.dirac_apply_of_mem hy] at hS
  exact one_ne_zero hS

/-- Let `μ` be a finite measure on `ℝ^d` and `V` a decomposability bundle of `μ`
with `V(x) = ⊤` for `μ`-a.e. `x`. Then `μ ≪ vol^d`. -/
theorem absolutelyContinuous_of_decompBundle_eq_top {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    (V : Vec d → Submodule ℝ (Vec d)) (hV : IsDecompBundle μ V) (htop : ∀ᵐ x ∂μ, V x = ⊤) :
    μ ≪ volume := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro S hS
    rw [volume_null_vec_zero S hS]; exact measure_empty
  obtain ⟨w, hw, hdense⟩ := exists_dense_axes hd
  have hα : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 2) := fun n => by positivity
  have hα2 : ∀ n : ℕ, 1 / ((n : ℝ) + 2) < Real.pi / 2 := fun n => by
    have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [Real.pi_gt_three]
  have hex := fun (i n : ℕ) => exhaust_prop (hw i) (hα n) (hα2 n) μ
  choose ρ N hρ hNm hNnull hac using hex
  have : ∀ i n, IsFiniteMeasure (ρ i n) := hρ
  set M : ℕ → ℕ → Set (Vec d) := fun i n => (N i n)ᶜ with hM
  have hMm : ∀ i n, MeasurableSet (M i n) := fun i n => (hNm i n).compl
  have hMn : ∀ i n : ℕ, IsCNull (cone (w i) (1 / ((n : ℝ) + 2))) (M i n)ᶜ := fun i n => by
    simpa [hM] using hNnull i n
  -- `W` passes the arc test, so `V ≤ W`, hence `W = ⊤` a.e.
  have htest := (opt_test hw hdense hMm hMn).2 μ
  have hVW : ∀ᵐ x ∂μ, V x ≤ selW w M x := hV.2 _ htest
  have hWtop : ∀ᵐ x ∂μ, selW w M x = ⊤ := by
    filter_upwards [hVW, htop] with x h1 h2
    rw [h2] at h1; exact top_le_iff.1 h1
  -- On a robust tuple of `d` axes the cones are independent, and curve currents give absolute continuity.
  set Adm : (Fin d → ℕ × ℕ) → Prop := fun τ => ∃ η : ℝ,
      (∀ a : Vec d, η * vecEuclideanNorm a ≤ vecEuclideanNorm (∑ j, a j • w (τ j).1)) ∧
      ∀ j, Real.sqrt d * (1 / (((τ j).2 : ℝ) + 2)) < η with hAdm
  set P : (Fin d → ℕ × ℕ) → Set (Vec d) := fun τ => ⋂ j, M (τ j).1 (τ j).2 with hP
  have hPm : ∀ τ, MeasurableSet (P τ) := fun τ => MeasurableSet.iInter fun j => hMm _ _
  have hacP : ∀ τ, Adm τ → μ.restrict (P τ) ≪ volume := by
    rintro τ ⟨η, hlow, hβη⟩
    refine spanac_prop (w := fun j => w (τ j).1) (fun j => hw _) hlow
      (β := fun j => 1 / (((τ j).2 : ℝ) + 2)) (fun j => ⟨hα _, hα2 _⟩) hβη
      (fun j => ρ (τ j).1 (τ j).2) (fun j => ?_)
    refine Measure.AbsolutelyContinuous.trans ?_ (hac (τ j).1 (τ j).2)
    exact Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (iInter_subset _ j) le_rfl)
  intro S hS
  have hsub : S ⊆ {x | selW w M x ≠ ⊤} ∪ ⋃ τ : {τ // Adm τ}, S ∩ P τ.1 := by
    intro x hxS
    by_cases hx : selW w M x = ⊤
    · right
      obtain ⟨τ, hxτ, η, hlow, hβη⟩ := exists_robust_tuple hx
      exact mem_iUnion.2 ⟨⟨τ, η, hlow, hβη⟩, hxS, mem_iInter.2 hxτ⟩
    · left; exact hx
  refine measure_mono_null hsub (measure_union_null (ae_iff.1 hWtop) ?_)
  refine measure_iUnion_null fun τ => ?_
  have := hacP τ.1 τ.2 hS
  rwa [Measure.restrict_apply' (hPm τ.1)] at this

end AFree
