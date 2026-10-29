/- Added by cx on 2026-10-29: integrating a positive matrix density
   preserves positivity; in particular the actual endpoint masses are PSD. -/
module

public import NoiseResponse.SpectralDensityTools
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

def quadraticTestCLM (w : m →₀ ℂ) : Matrix m m ℂ →L[ℂ] ℂ :=
  ∑ i ∈ w.support, ∑ j ∈ w.support, (star (w i)*w j) • matrixEntryCLM i j

theorem quadraticTestCLM_apply (w : m →₀ ℂ) (A : Matrix m m ℂ) :
    quadraticTestCLM w A = w.sum (fun i wi => w.sum (fun j wj => star wi*A i j*wj)) := by
  simp only [quadraticTestCLM, Finsupp.sum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, matrixEntryCLM, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (star (w i)*w j)*A i j = star (w i)*A i j*w j
  ring

theorem positive_matrix_integral
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (hpositive : ∀ᵐ x ∂μ, (F x).PosSemidef) :
    (∫ x, F x ∂μ).PosSemidef := by
  constructor
  · exact hermitian_integral μ F hF (hpositive.mono (fun x hx => hx.isHermitian.eq))
  · intro w
    have hi : 0 ≤ ∫ x, quadraticTestCLM w (F x) ∂μ :=
      integral_nonneg_of_ae (hpositive.mono (fun x hx => by
        change (0 : ℂ) ≤ quadraticTestCLM w (F x)
        rw [quadraticTestCLM_apply]
        exact hx.2 w))
    rw [(quadraticTestCLM w).integral_comp_comm hF, quadraticTestCLM_apply] at hi
    exact hi

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.positive_matrix_integral
