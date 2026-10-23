module

public import AFree.Curves.Perturb.GraphFn

/-!
# Euclidean neighbourhoods of a compact set
-/

@[expose] public section

open Set

namespace AFree

open PDE AFree.Curves

variable {d : ℕ}

/-- `{x : dist(x, K) ≤ δ}` for the Euclidean distance. -/
def perturbClosedNbhd (K : Set (Vec d)) (δ : ℝ) : Set (Vec d) :=
  {x | ∃ k ∈ K, vecEuclideanNorm (x - k) ≤ δ}

/-- `{x : dist(x, K) < δ}` for the Euclidean distance. -/
def perturbOpenNbhd (K : Set (Vec d)) (δ : ℝ) : Set (Vec d) :=
  {x | ∃ k ∈ K, vecEuclideanNorm (x - k) < δ}

lemma isOpen_perturbOpenNbhd (K : Set (Vec d)) (δ : ℝ) : IsOpen (perturbOpenNbhd K δ) := by
  have : perturbOpenNbhd K δ = ⋃ k ∈ K, {x | vecEuclideanNorm (x - k) < δ} := by
    ext x; simp [perturbOpenNbhd]
  rw [this]
  exact isOpen_biUnion fun k _ =>
    isOpen_lt (continuous_vecEuclideanNorm.comp (continuous_id.sub continuous_const)) continuous_const

lemma subset_perturbOpenNbhd (K : Set (Vec d)) {δ : ℝ} (hδ : 0 < δ) : K ⊆ perturbOpenNbhd K δ :=
  fun k hk => ⟨k, hk, by
    have : vecEuclideanNorm (k - k) = 0 := vecEuclideanNorm_eq_zero_iff.mpr (sub_self k)
    rw [this]; exact hδ⟩

lemma perturbOpenNbhd_subset_closed (K : Set (Vec d)) {δ δ' : ℝ} (h : δ ≤ δ') :
    perturbOpenNbhd K δ ⊆ perturbClosedNbhd K δ' :=
  fun _ ⟨k, hk, hx⟩ => ⟨k, hk, hx.le.trans h⟩

lemma isClosed_perturbClosedNbhd {K : Set (Vec d)} (hK : IsCompact K) (δ : ℝ) :
    IsClosed (perturbClosedNbhd K δ) := by
  have hB : IsCompact {v : Vec d | vecEuclideanNorm v ≤ δ} := by
    refine (isCompact_closedBall (0 : Vec d) δ).of_isClosed_subset
      (isClosed_le continuous_vecEuclideanNorm continuous_const) fun v hv => ?_
    rw [mem_closedBall_zero_iff]
    exact (norm_le_vecEuclideanNorm v).trans hv
  have : perturbClosedNbhd K δ =
      (fun p : Vec d × Vec d => p.1 + p.2) '' (K ×ˢ {v : Vec d | vecEuclideanNorm v ≤ δ}) := by
    ext x
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨(k, x - k), ⟨hk, h⟩, by simp⟩
    · rintro ⟨⟨k, v⟩, ⟨hk, hv⟩, rfl⟩; exact ⟨k, hk, by simpa using hv⟩
  rw [this]
  exact (hK.prod hB).image (continuous_fst.add continuous_snd) |>.isClosed

end AFree
