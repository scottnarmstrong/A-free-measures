module

public import AFree.Curves.Defs
public import AFree.Curves.Vec
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The cone selection field `W`

The axes are `w i` and the sets `M i n` (`= N_{i,n}ᶜ`) are indexed by `n : ℕ`, the aperture being `1 / (n + 2)`.
-/

@[expose] public section

open Set Filter Topology

namespace AFree.BundleTop

open PDE AFree.Curves

variable {d : ℕ}

/-- `I_m(x) = {i : ∃ n ≥ m, x ∈ M_{i,n}}`. -/
def selI (M : ℕ → ℕ → Set (Vec d)) (m : ℕ) (x : Vec d) : Set ℕ :=
  {i | ∃ n, m ≤ n ∧ x ∈ M i n}

/-- `A_m(x) = {w_i : i ∈ I_m(x)}`. -/
def selA (w : ℕ → Vec d) (M : ℕ → ℕ → Set (Vec d)) (m : ℕ) (x : Vec d) : Set (Vec d) :=
  w '' selI M m x

/-- `K(x) = ⋂_m closure A_m(x)`. -/
def selK (w : ℕ → Vec d) (M : ℕ → ℕ → Set (Vec d)) (x : Vec d) : Set (Vec d) :=
  ⋂ m, closure (selA w M m x)

/-- `W(x) = span K(x)`. -/
def selW (w : ℕ → Vec d) (M : ℕ → ℕ → Set (Vec d)) (x : Vec d) : Submodule ℝ (Vec d) :=
  Submodule.span ℝ (selK w M x)

variable {w : ℕ → Vec d} {M : ℕ → ℕ → Set (Vec d)} {x : Vec d}

lemma selI_anti {m m' : ℕ} (h : m ≤ m') : selI M m' x ⊆ selI M m x :=
  fun _ ⟨n, hn, hx⟩ => ⟨n, h.trans hn, hx⟩

lemma selA_anti {m m' : ℕ} (h : m ≤ m') : selA w M m' x ⊆ selA w M m x :=
  image_mono (selI_anti h)

lemma mem_selK : ∀ {v}, v ∈ selK w M x ↔ ∀ m, v ∈ closure (selA w M m x) := by
  intro v; simp [selK]

lemma mem_selA {m : ℕ} {i : ℕ} (hi : i ∈ selI M m x) : w i ∈ selA w M m x := ⟨i, hi, rfl⟩

/-- The Euclidean unit sphere is compact. -/
lemma isCompact_sphere : IsCompact {v : Vec d | vecEuclideanNorm v = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq continuous_vecEuclideanNorm continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Vec d)) (r := 1)).subset fun v hv => ?_
  rw [mem_closedBall_zero_iff]
  exact (norm_le_vecEuclideanNorm v).trans hv.le

/-- (Kc)(i), tuple form: a family of tuples with `u m j ∈ A_m(x)` has a subsequence converging to
a tuple in `K(x)`. -/
lemma exists_limit_selK {ι : Type*} [Finite ι] (hw : ∀ i, vecEuclideanNorm (w i) = 1)
    (u : ℕ → ι → Vec d) (hu : ∀ m j, u m j ∈ selA w M m x) :
    ∃ v : ι → Vec d, (∀ j, v j ∈ selK w M x) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => u (φ k)) atTop (𝓝 v) := by
  have := Fintype.ofFinite ι
  have hS : IsCompact (Set.pi univ fun _ : ι => {v : Vec d | vecEuclideanNorm v = 1}) :=
    isCompact_univ_pi fun _ => isCompact_sphere
  have hmem : ∀ m, u m ∈ Set.pi univ fun _ : ι => {v : Vec d | vecEuclideanNorm v = 1} := by
    intro m j _
    obtain ⟨i, -, hi⟩ := hu m j
    rw [← hi]; exact hw i
  obtain ⟨v, -, φ, hφ, hlim⟩ := hS.tendsto_subseq hmem
  refine ⟨v, fun j => mem_selK.2 fun m => ?_, φ, hφ, hlim⟩
  refine mem_closure_of_tendsto ((continuous_apply j).continuousAt.tendsto.comp hlim) ?_
  filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop m] with k hk
  exact selA_anti hk (hu (φ k) j)

/-- (Kc)(ii): a point of `K(x)` is approximated in the Euclidean norm by axes in every `A_m(x)`. -/
lemma exists_axis_near {v : Vec d} (hv : v ∈ selK w M x) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ i ∈ selI M m x, vecEuclideanNorm (w i - v) < ε := by
  have h := Metric.mem_closure_iff.1 (mem_selK.1 hv m) (ε / (Real.sqrt d + 1)) (by positivity)
  obtain ⟨a, ⟨i, hi, rfl⟩, hd⟩ := h
  refine ⟨i, hi, ?_⟩
  rw [dist_eq_norm] at hd
  have h1 := vecEuclideanNorm_le_sqrt_natCast_mul_norm (w i - v)
  have h2 : v - w i = -(w i - v) := by abel
  rw [h2, norm_neg] at hd
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  calc vecEuclideanNorm (w i - v) ≤ Real.sqrt d * ‖w i - v‖ := h1
    _ ≤ Real.sqrt d * (ε / (Real.sqrt d + 1)) := by
        exact mul_le_mul_of_nonneg_left hd.le hs
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith

end AFree.BundleTop
