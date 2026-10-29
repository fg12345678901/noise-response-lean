/- Added by cx on 2026-10-29: an actual finite PSD matrix measure,
   its finite trace control measure, and entrywise absolute continuity. -/
module

public import NoiseResponse.SpectralNecessity
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder MeasureTheory ENNReal
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] [DecidableEq m] [Nonempty m]

structure PSDMatrixMeasure (Ω : Type*) (m : Type*) [MeasurableSpace Ω]
    [Fintype m] [DecidableEq m] where
  entry : Matrix m m (ComplexMeasure Ω)
  positive : ∀ s : Set Ω, MeasurableSet s → Matrix.PosSemidef (fun i j => entry i j s)

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure Ω m)

def value (s : Set Ω) : Matrix m m ℂ := fun i j => M.entry i j s
def traceSigned : SignedMeasure Ω := ∑ i, (M.entry i i).re

theorem traceSigned_apply (s : Set Ω) : M.traceSigned s = (M.value s).trace.re := by
  calc
    _ = ∑ i, (M.entry i i).re s := by simp only [traceSigned, _root_.sum_apply]
    _ = ∑ i, (M.entry i i s).re := by rfl
    _ = (∑ i, M.entry i i s).re := by rw [Complex.re_sum]
    _ = _ := rfl

theorem traceSigned_nonneg : 0 ≤ M.traceSigned := by
  intro s hs
  change 0 ≤ M.traceSigned s
  rw [traceSigned_apply]
  change 0 ≤ (∑ i, M.entry i i s).re
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i hi
  exact (Complex.nonneg_iff.mp ((M.positive s hs).diag_nonneg (i := i))).1

def traceMeasure : Measure Ω := M.traceSigned.toMeasureOfZeroLE Set.univ MeasurableSet.univ
  (VectorMeasure.le_restrict_univ_iff_le _ _ |>.mpr M.traceSigned_nonneg)

instance traceMeasure_finite : IsFiniteMeasure M.traceMeasure := by
  unfold traceMeasure
  infer_instance

theorem traceMeasure_real (s : Set Ω) (hs : MeasurableSet s) :
    M.traceMeasure.real s = (M.value s).trace.re := by
  rw [traceMeasure, SignedMeasure.toMeasureOfZeroLE_real_apply]
  simp only [Set.univ_inter, traceSigned_apply]
  exact hs

theorem null_of_trace_null (s : Set Ω) (hs : MeasurableSet s)
    (hz : M.traceMeasure s=0) : M.value s=0 := by
  have hr : (M.value s).trace.re=0 := by
    rw [← traceMeasure_real M s hs, measureReal_def, hz, ENNReal.toReal_zero]
  have hi : (M.value s).trace.im=0 := by
    change (∑ i, M.entry i i s).im=0
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro i hi
    exact (Complex.nonneg_iff.mp ((M.positive s hs).diag_nonneg (i := i))).2.symm
  apply (M.positive s hs).trace_eq_zero_iff.mp
  exact Complex.ext hr hi

theorem entry_absolutelyContinuous (i j : m) :
    M.entry i j ≪ᵥ M.traceMeasure.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hz
  have hzero := M.null_of_trace_null s hs (by simpa [hs] using hz)
  exact congrArg (fun A : Matrix m m ℂ => A i j) hzero

/-- A complex-measure RN statement obtained from the two genuine
    signed-measure RN derivatives. No density-existence assumption. -/
theorem complex_withDensity_rnDeriv
    (c : ComplexMeasure Ω) (μ : Measure Ω) [SigmaFinite μ]
    (h : c ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (c.rnDeriv μ)=c := by
  have hparts := (ComplexMeasure.absolutelyContinuous_ennreal_iff c _).mp h
  have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq c.re μ hparts.1
  have him := SignedMeasure.withDensityᵥ_rnDeriv_eq c.im μ hparts.2
  ext s hs
  rw [withDensityᵥ_apply (c.integrable_rnDeriv μ) hs]
  apply Complex.ext
  · have he := congrArg (fun v : SignedMeasure Ω => v s) hre
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at he
    calc
      _ = ∫ x in s, (c.rnDeriv μ x).re ∂μ :=
        (Complex.reCLM.integral_comp_comm (c.integrable_rnDeriv μ).integrableOn).symm
      _ = _ := he
  · have he := congrArg (fun v : SignedMeasure Ω => v s) him
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at he
    calc
      _ = ∫ x in s, (c.rnDeriv μ x).im ∂μ :=
        (Complex.imCLM.integral_comp_comm (c.integrable_rnDeriv μ).integrableOn).symm
      _ = _ := he

def density (x : Ω) : Matrix m m ℂ := fun i j => (M.entry i j).rnDeriv M.traceMeasure x

theorem density_integrable : Integrable M.density M.traceMeasure := by
  apply integrable_pi_iff.mpr
  intro i
  apply integrable_pi_iff.mpr
  intro j
  exact (M.entry i j).integrable_rnDeriv _

theorem density_entry_integral (i j : m) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x in s, M.density x i j ∂M.traceMeasure) = M.entry i j s := by
  have he := complex_withDensity_rnDeriv (M.entry i j) M.traceMeasure (M.entry_absolutelyContinuous i j)
  have he' := congrArg (fun v : ComplexMeasure Ω => v s) he
  rw [withDensityᵥ_apply ((M.entry i j).integrable_rnDeriv _) hs] at he'
  exact he'

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.entry_absolutelyContinuous
#print axioms NoiseResponse.Classification.PSDMatrixMeasure.density_entry_integral
