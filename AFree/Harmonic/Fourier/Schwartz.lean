module

public import AFree.Analysis.ConvCompact
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Smooth compactly supported functions are Schwartz
-/

@[expose] public section

open PDE
open scoped SchwartzMap

namespace AFree

noncomputable section

variable {d : ℕ}

/-- A smooth compactly supported real function on `Vec d`, as a Schwartz function. -/
def toSchwartz (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    𝓢(Vec d, ℝ) :=
  hc.toSchwartzMap (by exact_mod_cast hf)

/-- The complex-valued version. -/
def toSchwartzC (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    𝓢(Vec d, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (toSchwartz f hf hc)

@[simp] theorem toSchwartzC_apply (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (x : Vec d) : toSchwartzC f hf hc x = (f x : ℂ) := rfl

end

end AFree
