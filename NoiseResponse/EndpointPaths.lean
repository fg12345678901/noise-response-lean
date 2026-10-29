/- Added by cx on 2026-10-29: explicit admissible approaches to both
   endpoints, so the sequence hypotheses have a concrete witness. -/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
namespace NoiseResponse.Classification

def positiveEndpointPath (n : ℕ) : ℝ := 1-1/((n : ℝ)+1)
def negativeEndpointPath (n : ℕ) : ℝ := -positiveEndpointPath n

theorem positiveEndpointPath_bounds (n : ℕ) :
    0 ≤ positiveEndpointPath n ∧ positiveEndpointPath n < 1 := by
  have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hn : 1/((n : ℝ)+1) ≤ 1 := (div_le_one hp).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hq : (0 : ℝ) < 1/((n : ℝ)+1) := one_div_pos.mpr hp
  unfold positiveEndpointPath
  constructor <;> linarith

theorem positiveEndpointPath_mem (n : ℕ) : positiveEndpointPath n ∈ Ioo (-1 : ℝ) 1 :=
  ⟨lt_of_lt_of_le (by norm_num) (positiveEndpointPath_bounds n).1,
    (positiveEndpointPath_bounds n).2⟩

theorem negativeEndpointPath_mem (n : ℕ) : negativeEndpointPath n ∈ Ioo (-1 : ℝ) 1 := by
  have h := positiveEndpointPath_mem n
  unfold negativeEndpointPath
  constructor <;> linarith [h.1, h.2]

theorem positiveEndpointPath_tendsto : Tendsto positiveEndpointPath atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1-1/((n : ℝ)+1)) atTop (𝓝 1)
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat

theorem negativeEndpointPath_tendsto : Tendsto negativeEndpointPath atTop (𝓝 (-1)) :=
  positiveEndpointPath_tendsto.neg

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.positiveEndpointPath_tendsto
