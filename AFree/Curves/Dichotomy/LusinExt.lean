module

public import AFree.Curves.Dichotomy.LusinHermite
public import Mathlib.Topology.Order.Compact

/-!
# The Whitney extension

For a compact `S ⊆ ℝ` and data `φ, ψ : ℝ → E` on `S`, `ext S φ ψ` equals `φ` on `S`, is the affine
function with slope `ψ(min S)` (resp. `ψ(max S)`) on the left (resp. right) ray and is the cubic
Hermite interpolant on every gap `(p, q)` of `S`; the endpoints `p, q` of the gap containing `y` are
`sSup (S ∩ (-∞, y])` and `sInf (S ∩ [y, ∞))`.
-/

@[expose] public section

open Set

namespace AFree

namespace Lusin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- The Whitney extension of the data `(φ, ψ)` on `S`. -/
noncomputable def ext (S : Set ℝ) (φ ψ : ℝ → E) (y : ℝ) : E :=
  if y ∈ S then φ y
  else if y < sInf S then φ (sInf S) + (y - sInf S) • ψ (sInf S)
  else if sSup S < y then φ (sSup S) + (y - sSup S) • ψ (sSup S)
  else herm (sSup (S ∩ Iic y)) (sInf (S ∩ Ici y)) (φ (sSup (S ∩ Iic y))) (φ (sInf (S ∩ Ici y)))
    (ψ (sSup (S ∩ Iic y))) (ψ (sInf (S ∩ Ici y))) y

variable {S : Set ℝ} {φ ψ : ℝ → E}

lemma ext_of_mem {y : ℝ} (hy : y ∈ S) : ext S φ ψ y = φ y := by
  simp [ext, hy]

lemma ext_left (hS : IsCompact S) (hne : S.Nonempty) {y : ℝ} (hy : y ≤ sInf S) :
    ext S φ ψ y = φ (sInf S) + (y - sInf S) • ψ (sInf S) := by
  rcases hy.lt_or_eq with h | h
  · have hyS : y ∉ S := fun hm => (csInf_le hS.bddBelow hm).not_gt h
    simp [ext, hyS, h]
  · rw [h, ext_of_mem (hS.sInf_mem hne)]
    simp

lemma ext_right (hS : IsCompact S) (hne : S.Nonempty) {y : ℝ} (hy : sSup S ≤ y) :
    ext S φ ψ y = φ (sSup S) + (y - sSup S) • ψ (sSup S) := by
  rcases hy.lt_or_eq with h | h
  · have hyS : y ∉ S := fun hm => (le_csSup hS.bddAbove hm).not_gt h
    have h1 : ¬ y < sInf S := fun h' =>
      (((csInf_le hS.bddBelow hne.some_mem).trans (le_csSup hS.bddAbove hne.some_mem)).trans h.le).not_gt h'
    simp [ext, hyS, h1, h]
  · rw [← h, ext_of_mem (hS.sSup_mem hne)]
    simp

/-- On the closure of a gap `(p, q)` of `S` the extension is the Hermite cubic. -/
lemma ext_gap (hS : IsCompact S) {p q : ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p < q)
    (hgap : ∀ s ∈ S, s ∉ Ioo p q) {t : ℝ} (ht : t ∈ Icc p q) :
    ext S φ ψ t = herm p q (φ p) (φ q) (ψ p) (ψ q) t := by
  rcases ht.1.eq_or_lt with rfl | h1
  · rw [ext_of_mem hp, herm_left]
  rcases ht.2.eq_or_lt with rfl | h2
  · rw [ext_of_mem hq, herm_right hpq]
  have htS : t ∉ S := fun hm => hgap t hm ⟨h1, h2⟩
  have hne : S.Nonempty := ⟨p, hp⟩
  have h3 : ¬ t < sInf S := not_lt.2 ((csInf_le hS.bddBelow hp).trans h1.le)
  have h4 : ¬ sSup S < t := not_lt.2 (h2.le.trans (le_csSup hS.bddAbove hq))
  have hlo : sSup (S ∩ Iic t) = p := by
    refine IsGreatest.csSup_eq ⟨⟨hp, h1.le⟩, fun s ⟨hs, hst⟩ => ?_⟩
    by_contra hsp
    exact hgap s hs ⟨not_le.1 hsp, lt_of_le_of_lt hst h2⟩
  have hup : sInf (S ∩ Ici t) = q := by
    refine IsLeast.csInf_eq ⟨⟨hq, h2.le⟩, fun s ⟨hs, hst⟩ => ?_⟩
    by_contra hsq
    exact hgap s hs ⟨lt_of_lt_of_le h1 hst, not_le.1 hsq⟩
  simp only [ext, htS, h3, h4, hlo, hup, ite_false]

end Lusin

end AFree
