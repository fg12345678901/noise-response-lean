/- Added by cx on 2026-10-29: connect actual matrix-valued measures
   to the existing integral-spectrum interface through the trace RN density. -/
module

public import NoiseResponse.MatrixSpectralMeasure
public import NoiseResponse.MatrixDensityPositivity
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder MeasureTheory
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] [DecidableEq m] [Nonempty m]
namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure Ω m)

theorem density_matrix_integral (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x in s, M.density x ∂M.traceMeasure) = M.value s := by
  ext i j
  have he := (matrixEntryCLM i j).integral_comp_comm (M.density_integrable.integrableOn (s := s))
  change (∫ x in s, M.density x i j ∂M.traceMeasure) =
    (∫ x in s, M.density x ∂M.traceMeasure) i j at he
  rw [← he, M.density_entry_integral i j s hs]
  rfl

theorem density_positive : ∀ᵐ x ∂M.traceMeasure, (M.density x).PosSemidef := by
  apply density_positive_of_setIntegrals M.traceMeasure M.density M.density_integrable
  intro s hs
  rw [M.density_matrix_integral s hs]
  exact M.positive s hs

/-- A genuine representation theorem for every finite PSD matrix
    measure, including arbitrary atomic and singular measures. -/
theorem trace_density_representation :
    ∃ μ : Measure Ω, IsFiniteMeasure μ ∧ ∃ F : Ω → Matrix m m ℂ,
      Integrable F μ ∧ (∀ᵐ x ∂μ, (F x).PosSemidef) ∧
      ∀ s : Set Ω, MeasurableSet s → (∫ x in s, F x ∂μ)=M.value s :=
  ⟨M.traceMeasure, M.traceMeasure_finite, M.density, M.density_integrable,
    M.density_positive, M.density_matrix_integral⟩

theorem trace_density_unique (F : Ω → Matrix m m ℂ)
    (hF : Integrable F M.traceMeasure)
    (hsets : ∀ s : Set Ω, MeasurableSet s → (∫ x in s, F x ∂M.traceMeasure)=M.value s) :
    F =ᵐ[M.traceMeasure] M.density := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hF M.density_integrable
  intro s hs hfin
  rw [hsets s hs, M.density_matrix_integral s hs]

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.trace_density_representation
