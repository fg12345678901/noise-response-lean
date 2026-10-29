/- Added by cx on 2026-10-29.
   V6 Appendix A.4 algebraic steps. The closure-to-axis and endpoint-limit
   hypotheses are connected by separate calculus/measure modules.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix

namespace NoiseResponse
namespace Classification

/-- The two radial/tangential closedness evaluations isolate the skew ODE
    and the symmetric trace-free ODE. No division by 1-a is used here. -/
theorem axis_closedness_implies_ode
    (a s t sp tp g : ℝ) (ha : 1 + a ≠ 0)
    (hi : -2 * t - 2 * (1 - a) * (sp - tp) +
      2 * (g + 2 * a * s) / (1 + a) = 0)
    (hj : -2 * t + 2 * (1 - a) * (sp + tp) -
      2 * (g + 2 * a * s) / (1 + a) = 0) :
    (1 - a) * tp - t = 0 ∧
      (1 - a ^ 2) * sp - 2 * a * s = g := by
  have ht : (1 - a) * tp - t = 0 := by nlinarith [hi, hj]
  have hs : (g + 2 * a * s) / (1 + a) = (1 - a) * sp := by
    have hi' : -2 * t - 2 * (1 - a) * (sp - tp) +
        2 * ((g + 2 * a * s) / (1 + a)) = 0 := by
      simpa only [mul_div_assoc] using hi
    nlinarith [hi', ht]
  have hq := div_mul_cancel₀ (g + 2 * a * s) ha
  rw [hs] at hq
  exact ⟨ht, by nlinarith [hq]⟩

/-- Endpoint matching identifies both constants in (B5). -/
theorem endpoint_constants (g d m0 mpi : ℝ)
    (hp : (g + d) / 2 = m0) (hm : (-g + d) / 2 = -mpi) :
    g = m0 + mpi ∧ d = m0 - mpi := by
  constructor <;> linarith

/-- The resulting partial fractions are exactly the two endpoint atoms. -/
theorem endpoint_partial_fractions (a m0 mpi : ℝ)
    (hp : 1 - a ≠ 0) (hm : 1 + a ≠ 0) :
    (a * (m0 + mpi) + (m0 - mpi)) / (1 - a ^ 2) =
      m0 / (1 - a) - mpi / (1 + a) := by
  have h : 1 - a ^ 2 ≠ 0 := by
    have : 1 - a ^ 2 = (1 - a) * (1 + a) := by ring
    rw [this]
    exact mul_ne_zero hp hm
  field_simp
  <;> ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coordinate form of the scalar-matrix step after equation (B4). -/
theorem scalar_of_all_wedges_zero [Nonempty n] (N : Matrix n n ℝ)
    (h : ∀ (z : n → ℝ) (i j : n),
      z i * (N *ᵥ z) j - z j * (N *ᵥ z) i = 0) :
    ∃ c : ℝ, N = c • (1 : Matrix n n ℝ) := by
  classical
  have off : ∀ i j : n, i ≠ j → N i j = 0 := by
    intro i j hij
    have hz := h (Pi.single j 1) j i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hij, Ne.symm hij] using hz
  have diag : ∀ i j : n, N i i = N j j := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hz := h (Pi.single i 1 + Pi.single j 1) i j
      simp [Matrix.mulVec_add, Matrix.mulVec_single, Pi.single_apply,
        hij, Ne.symm hij, Matrix.col, off i j hij, off j i (Ne.symm hij)] at hz
      linarith
  let k : n := Classical.arbitrary n
  refine ⟨N k k, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using diag i k
  · simp [hij, off i j hij]

end Classification
end NoiseResponse

#print axioms NoiseResponse.Classification.axis_closedness_implies_ode
#print axioms NoiseResponse.Classification.endpoint_constants
#print axioms NoiseResponse.Classification.endpoint_partial_fractions
#print axioms NoiseResponse.Classification.scalar_of_all_wedges_zero
