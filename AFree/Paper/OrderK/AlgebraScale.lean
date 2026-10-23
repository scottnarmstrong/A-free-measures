module

public import AFree.Paper.OrderK.AlgebraMulti

/-!
# Affine changes of variables

Scaling rule: for `T z = c • z + b`, `∂^α (f ∘ T) = c^{|α|} (∂^α f) ∘ T` on
`T⁻¹ U`, for `f` smooth on `U`.
-/

@[expose] public section

open MeasureTheory PDE

namespace AFree

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}

/-- The affine map `z ↦ c z + b`. -/
def affMap (c : ℝ) (b : Vec d) : Vec d → Vec d := fun z => c • z + b

theorem continuous_affMap (c : ℝ) (b : Vec d) : Continuous (affMap c b) := by
  unfold affMap; fun_prop

theorem hasFDerivAt_affMap (c : ℝ) (b : Vec d) (z : Vec d) :
    HasFDerivAt (affMap c b) (c • ContinuousLinearMap.id ℝ (Vec d)) z := by
  unfold affMap
  exact ((hasFDerivAt_id z).const_smul c).add_const b

theorem SmOn.comp_affMap (hf : SmOn U f) (c : ℝ) (b : Vec d) :
    SmOn (affMap c b ⁻¹' U) (fun z => f (affMap c b z)) := fun z hz =>
  (hf _ hz).comp z (by unfold affMap; fun_prop)

theorem D_comp_affMap (hf : SmOn U f) (c : ℝ) (b : Vec d) (i : Fin d) :
    Set.EqOn (euclideanCoordDeriv i (fun z => f (affMap c b z)))
      (fun z => c * euclideanCoordDeriv i f (affMap c b z)) (affMap c b ⁻¹' U) := by
  intro z hz
  have hd : DifferentiableAt ℝ f (affMap c b z) := differentiableAt_of_smOn hf hz
  unfold euclideanCoordDeriv
  have := (hd.hasFDerivAt.comp z (hasFDerivAt_affMap c b z)).fderiv
  rw [show (fun z => f (affMap c b z)) = f ∘ affMap c b from rfl, this]
  simp

theorem iterD_comp_affMap (hU : IsOpen U) (hf : SmOn U f) (c : ℝ) (b : Vec d) (i : Fin d)
    (n : ℕ) :
    Set.EqOn ((euclideanCoordDeriv i)^[n] (fun z => f (affMap c b z)))
      (fun z => c ^ n * (euclideanCoordDeriv i)^[n] f (affMap c b z)) (affMap c b ⁻¹' U) := by
  have hV : IsOpen (affMap c b ⁻¹' U) := hU.preimage (continuous_affMap c b)
  induction n with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    rw [Function.iterate_succ_apply', eqOn_D hV ih i hz]
    have h1 := D_const_mul (c ^ n) ((hf.iterD i n).comp_affMap c b) i hz
    dsimp only at h1
    rw [h1, D_comp_affMap (hf.iterD i n) c b i hz, Function.iterate_succ_apply']
    ring

theorem foldDeriv_comp_affMap (hU : IsOpen U) (hf : SmOn U f) (c : ℝ) (b : Vec d)
    (α : Fin d → ℕ) (l : List (Fin d)) :
    Set.EqOn (foldDeriv l α (fun z => f (affMap c b z)))
      (fun z => c ^ (l.map α).sum * foldDeriv l α f (affMap c b z)) (affMap c b ⁻¹' U) := by
  have hV : IsOpen (affMap c b ⁻¹' U) := hU.preimage (continuous_affMap c b)
  induction l with
  | nil => intro z _; simp [foldDeriv]
  | cons j l ih =>
    intro z hz
    show (euclideanCoordDeriv j)^[α j] (foldDeriv l α (fun z => f (affMap c b z))) z = _
    rw [eqOn_iterD hV ih j (α j) hz]
    have hsm : SmOn U (foldDeriv l α f) := hf.foldr α l
    have h1 := iterD_const_mul hV (c ^ (l.map α).sum) (hsm.comp_affMap c b) j (α j) hz
    dsimp only at h1
    rw [h1, iterD_comp_affMap hU hsm c b j (α j) hz]
    simp only [List.map_cons, List.sum_cons, pow_add]
    show _ = c ^ α j * c ^ (l.map α).sum * (euclideanCoordDeriv j)^[α j] (foldDeriv l α f) (affMap c b z)
    ring

/-- Scaling rule: `∂^α (f ∘ T) = c^{|α|} (∂^α f) ∘ T` for `T z = c z + b`,
on `T⁻¹ U`. -/
theorem multiCoordDeriv_comp_affMap (hU : IsOpen U) (hf : SmOn U f) (c : ℝ) (b : Vec d)
    (α : Fin d → ℕ) :
    Set.EqOn (multiCoordDeriv α (fun z => f (affMap c b z)))
      (fun z => c ^ multiAbs α * multiCoordDeriv α f (affMap c b z)) (affMap c b ⁻¹' U) := by
  intro z hz
  have := foldDeriv_comp_affMap hU hf c b α (List.finRange d) hz
  have hs : ((List.finRange d).map α).sum = multiAbs α := by
    unfold multiAbs; rw [Fin.sum_univ_def]
  rw [hs] at this
  exact this

end

end AFree
