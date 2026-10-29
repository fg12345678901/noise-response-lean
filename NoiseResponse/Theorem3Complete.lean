/- Added by cx on 2026-10-29: final manuscript Theorem 3 entry points,
   with a single chart-independent potential in every finite dimension. -/
module

public import NoiseResponse.Theorem3GeometryIdentities
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2400
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Classical Topology Matrix.Norms.L2Operator
namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Classification
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n]
variable {T : ℝ} [Fact (0 < T)]

/-- A single potential on parameter space works in every admissible
    clean chart of the same residual, not a separate chartwise choice.
    Positive-dimensional cases use the explicit potential (13); the
    zero-dimensional case has the zero potential and zero response. -/
theorem classified_global_potential
    (M : PSDMatrixMeasure (AddCircle T) m) (hclass : M.HasClassifiedSpectrum)
    (η : ℝ) (hη : 0<η) (f : (n → ℝ) → (m → ℝ)) :
    ∃ U : (n → ℝ) → ℝ,
      ∀ (d : ℕ) (ι : (Fin d → ℝ) → (n → ℝ)) (x : Fin d → ℝ),
        AdmissibleAt η f ι x →
          ContDiffAt ℝ 2 (fun y => U (ι y)) x ∧
            ∀ v, fderiv ℝ (fun y => U (ι y)) x v= -response M η f ι x v := by
  cases isEmpty_or_nonempty n with
  | inl hempty =>
      letI := hempty
      refine ⟨fun _ => 0,?_⟩
      intro d ι x hgood
      refine ⟨contDiffAt_const,?_⟩
      intro v
      rw [empty_parameters_response M η f ι x v,neg_zero]
      simpa only [ContinuousLinearMap.zero_apply] using
        congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L v) (hasFDerivAt_const (0 : ℝ) x).fderiv
  | inr hnonempty =>
      letI := hnonempty
      obtain ⟨ν,M0,Mpi,hfinite,h0,hpi,href,hM0,hMpi,hdec⟩ := hclass
      letI := hfinite
      refine ⟨globalPotential ν (fun w => fourier 1 w) η (complexifyMatrix M0)
        (complexifyMatrix Mpi) f,?_⟩
      intro d ι x hgood
      exact globalPotential_response M ν (complexifyMatrix M0) (complexifyMatrix Mpi)
        hdec η hη f ι x hgood

end NoiseResponse.ResidualGeometry

#print axioms NoiseResponse.ResidualGeometry.theorem3_universal_spectral_classification
#print axioms NoiseResponse.ManuscriptPotential.manuscript_potential_formula
#print axioms NoiseResponse.IsotropicSpectrum.phi_derivative
#print axioms NoiseResponse.ResidualGeometry.classified_global_potential
