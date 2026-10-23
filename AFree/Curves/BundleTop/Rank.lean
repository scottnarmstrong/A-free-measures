module

public import AFree.Curves.BundleTop.Margin
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The rank of `W`

`k ≤ dim W(x)` iff there is a rational `η > 0` such that for every `m` there are `k` axes of
`A_m(x)` with margin `η`; this is a countable combination of the measurable sets `{i ∈ I_m(x)}`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ} {w : ℕ → Vec d} {M : ℕ → ℕ → Set (Vec d)} {x : Vec d}

lemma exists_indep_of_le_finrank {K : Set (Vec d)} {k : ℕ}
    (hk : k ≤ Module.finrank ℝ (Submodule.span ℝ K)) :
    ∃ v : Fin k → Vec d, (∀ j, v j ∈ K) ∧ LinearIndependent ℝ v := by
  obtain ⟨b, hbK, hspan, hli⟩ := exists_linearIndependent ℝ K
  have := hli.finite
  have := Fintype.ofFinite b
  have hcard : Module.finrank ℝ (Submodule.span ℝ K) = Fintype.card b := by
    have h := finrank_span_eq_card hli
    rw [Subtype.range_coe] at h
    rw [← hspan]; exact h
  rw [hcard] at hk
  refine ⟨fun j => ((Fintype.equivFin b).symm (Fin.castLE hk j) : Vec d), fun j => hbK (Subtype.mem _), ?_⟩
  exact hli.comp _ ((Equiv.injective _).comp (Fin.castLE_injective hk))

lemma le_finrank_of_indep {K : Set (Vec d)} {k : ℕ} {v : Fin k → Vec d} (hv : ∀ j, v j ∈ K)
    (hli : LinearIndependent ℝ v) : k ≤ Module.finrank ℝ (Submodule.span ℝ K) := by
  have h1 := finrank_span_eq_card hli
  have h2 : Submodule.span ℝ (range v) ≤ Submodule.span ℝ K :=
    Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hv j)
  have := Submodule.finrank_mono h2
  simp only [Fintype.card_fin] at h1
  omega

/-- The rank condition. -/
def RankCond (w : ℕ → Vec d) (M : ℕ → ℕ → Set (Vec d)) (k : ℕ) (x : Vec d) : Prop :=
  ∃ q : ℚ, 0 < q ∧ ∀ m, ∃ t : Fin k → ℕ, (∀ j, t j ∈ selI M m x) ∧
    Margin (q : ℝ) (fun j => w (t j))

/-- `k ≤ dim W(x)` iff the rank condition holds. -/
lemma rankCond_iff (hw : ∀ i, vecEuclideanNorm (w i) = 1) (k : ℕ) :
    RankCond w M k x ↔ k ≤ Module.finrank ℝ (selW w M x) := by
  constructor
  · rintro ⟨q, hq, h⟩
    choose t ht hmar using h
    obtain ⟨v, hv, φ, hφ, hlim⟩ := exists_limit_selK (ι := Fin k) hw
      (fun m j => w (t m j)) fun m j => mem_selA (ht m j)
    have hmv : Margin (q : ℝ) v := by
      refine (isClosed_margin (q : ℝ)).mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
      exact hmar (φ n)
    exact le_finrank_of_indep hv (hmv.linearIndependent (by exact_mod_cast hq))
  · intro hk
    obtain ⟨v, hv, hli⟩ := exists_indep_of_le_finrank hk
    obtain ⟨η, hη, hmar⟩ := exists_margin_of_linearIndependent hli
    obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (show (0 : ℝ) < 3 * η / 4 by positivity)
    refine ⟨q, by exact_mod_cast hq0, fun m => ?_⟩
    have hk4 : (k : ℝ) * (η / (4 * (k + 1))) ≤ η / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hpos : 0 < η / (4 * (k + 1)) := by positivity
    have : ∀ j, ∃ i ∈ selI M m x, vecEuclideanNorm (w i - v j) < η / (4 * (k + 1)) :=
      fun j => exists_axis_near (hv j) m hpos
    choose t ht hd using this
    refine ⟨t, ht, ?_⟩
    exact (Margin.perturb hmar hk4 fun j => (hd j).le).mono hq1.le

lemma measurableSet_mem_selI (hM : ∀ i n, MeasurableSet (M i n)) (m i : ℕ) :
    MeasurableSet {x | i ∈ selI M m x} := by
  have : {x | i ∈ selI M m x} = ⋃ n, ⋃ (_ : m ≤ n), M i n := by
    ext x; simp [selI]
  rw [this]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hM i n

lemma measurableSet_rankCond (hM : ∀ i n, MeasurableSet (M i n)) (k : ℕ) :
    MeasurableSet {x | RankCond w M k x} := by
  have : {x | RankCond w M k x} = ⋃ q : ℚ, ⋃ (_ : 0 < q), ⋂ m : ℕ,
      ⋃ t : Fin k → ℕ, ⋃ (_ : Margin (q : ℝ) (fun j => w (t j))), ⋂ j, {x | t j ∈ selI M m x} := by
    ext x; simp [RankCond, and_comm]
  rw [this]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun m =>
    MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iInter fun j => measurableSet_mem_selI hM m (t j)

/-- `R_k = {dim W = k}` is Borel. -/
lemma measurableSet_finrank_eq (hw : ∀ i, vecEuclideanNorm (w i) = 1)
    (hM : ∀ i n, MeasurableSet (M i n)) (k : ℕ) :
    MeasurableSet {x | Module.finrank ℝ (selW w M x) = k} := by
  have h1 : ∀ k, MeasurableSet {x | k ≤ Module.finrank ℝ (selW w M x)} := fun k => by
    have : {x | k ≤ Module.finrank ℝ (selW w M x)} = {x | RankCond w M k x} := by
      ext x; exact (rankCond_iff hw k).symm
    rw [this]; exact measurableSet_rankCond hM k
  have : {x | Module.finrank ℝ (selW w M x) = k} =
      {x | k ≤ Module.finrank ℝ (selW w M x)} \ {x | k + 1 ≤ Module.finrank ℝ (selW w M x)} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_sdiff]; omega
  rw [this]
  exact (h1 k).diff (h1 (k + 1))

end AFree.BundleTop
