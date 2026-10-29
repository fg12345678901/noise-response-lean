/- Added by cx on 2026-10-29: literal matrix-measure classification
   splits every bounded measurable response test into scalar and endpoint parts. -/
module

public import NoiseResponse.SpectralIntegralDetermination
public import NoiseResponse.MatrixMeasureClassification
public import NoiseResponse.EndpointPotentialCalculus
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 6000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.Elementwise Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {Ω m : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [Fintype m] [DecidableEq m] [Nonempty m]

def tracePairCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℂ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Matrix m m ℂ) (Matrix m m ℂ) ℝ) traceRealCLM).comp
    (NoiseResponse.MatrixCalculus.mulCLM (l := m) (m := m) (n := m))

@[simp] theorem tracePairCLM_apply (A B : Matrix m m ℂ) : tracePairCLM A B=(A*B).trace.re := rfl

namespace PSDMatrixMeasure

theorem classified_test_integral (M : PSDMatrixMeasure Ω m)
    (ν : Measure Ω) [IsFiniteMeasure ν] (a b : Ω) (M0 Mpi : Matrix m m ℂ)
    (hdec : ∀ s : Set Ω, MeasurableSet s →
      M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
        (if a ∈ s then M0 else 0)+(if b ∈ s then Mpi else 0))
    (C : Ω → Matrix m m ℂ) (hC : StronglyMeasurable C)
    (c : ℝ) (hc : 0 ≤ c) (hb : ∀ x, ‖C x‖ ≤ c) :
    (∫ x, (C x*M.density x).trace.re ∂M.traceMeasure)=
      (∫ x, (C x).trace.re ∂ν)+(C a*M0).trace.re+(C b*Mpi).trace.re := by
  classical
  let measures : Fin 3 → Measure Ω := ![ν,Measure.dirac a,Measure.dirac b]
  let fields : Fin 3 → Ω → Matrix m m ℂ := ![fun _ => 1,fun _ => M0,fun _ => Mpi]
  have hf (i : Fin 3) : IsFiniteMeasure (measures i) := by fin_cases i <;> dsimp [measures] <;> infer_instance
  have hfields (i : Fin 3) : Integrable (fields i) (measures i) := by
    letI := hf i
    fin_cases i <;> exact integrable_const _
  have hsets (s : Set Ω) (hs : MeasurableSet s) :
      (∫ x in s, M.density x ∂M.traceMeasure)=∑ i, ∫ x in s, fields i x ∂measures i := by
    rw [M.density_matrix_integral s hs,hdec s hs]
    simp only [Fin.sum_univ_three,measures,fields,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
      simp [integral_const,Measure.real,measureReal_def,Measure.restrict_apply,
        hs,Complex.real_smul,ha,hb,Set.indicator_apply,Matrix.cons_val_two]
  have hh := NoiseResponse.SpectralIntegral.bounded_pairing_finite_split tracePairCLM
    M.traceMeasure M.density M.density_integrable measures fields hfields hsets C hC c hc hb
  simpa [tracePairCLM_apply,Fin.sum_univ_three,
    measures,fields,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Matrix.mul_one,integral_dirac,add_assoc] using hh

theorem classified_continuous_test_integral [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
    (M : PSDMatrixMeasure Ω m) (ν : Measure Ω) [IsFiniteMeasure ν]
    (a b : Ω) (M0 Mpi : Matrix m m ℂ)
    (hdec : ∀ s : Set Ω, MeasurableSet s →
      M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
        (if a ∈ s then M0 else 0)+(if b ∈ s then Mpi else 0))
    (C : Ω → Matrix m m ℂ) (hC : Continuous C) :
    (∫ x, (C x*M.density x).trace.re ∂M.traceMeasure)=
      (∫ x, (C x).trace.re ∂ν)+(C a*M0).trace.re+(C b*Mpi).trace.re := by
  have hb : BddAbove (Set.range (fun x => ‖C x‖)) := by
    simpa only [Set.image_univ] using isCompact_univ.bddAbove_image hC.norm.continuousOn
  obtain ⟨c,hc⟩ := hb
  exact M.classified_test_integral ν a b M0 Mpi hdec C hC.stronglyMeasurable
    (max c 0) (le_max_right _ _) (fun x => (hc ⟨x,rfl⟩).trans (le_max_left _ _))

end PSDMatrixMeasure
end NoiseResponse.Classification
