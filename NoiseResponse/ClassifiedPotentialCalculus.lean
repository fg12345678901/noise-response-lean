/- Added by cx on 2026-10-29: the genuine three-part C2 potential
   and its response identity on a stable supported Jacobian field. -/
module

public import NoiseResponse.CanonicalMatrixGeometry
public import NoiseResponse.ClassifiedSpectralIntegral
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2100
set_option maxHeartbeats 8000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.Sufficiency
open NoiseResponse.IsotropicSpectrum NoiseResponse.RankSafe
variable {Ω m n : Type*} [MeasurableSpace Ω]
variable [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAlgebra ℝ (Matrix m m ℂ) where
  norm_smul_le := norm_smul_le
local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le

def IsNormalProjectorField (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) : Prop :=
  ∀ y, (P y)ᴴ=P y ∧ P y*P y=P y ∧ A y*P y=A y ∧ P y*(A y)ᴴ=(A y)ᴴ

def scalarPart (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) : E → ℝ :=
  isotropicPotential ν z η P (fun y => (A y)ᴴ*A y)

def zeroPart (η : ℝ) (M0 : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) : E → ℝ :=
  NoiseResponse.GeneralEndpoint.zeroPotential η M0 (fun y => outputProjector η (A y) (P y))

def nyquistPart (η : ℝ) (Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) : E → ℝ :=
  NoiseResponse.Classification.nyquistPotential Mpi (fun y => A y*(A y)ᴴ)
    (fun y => nyquistOutputInverse η (A y) (P y))

def fullPotential (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x : E) : ℝ :=
  scalarPart ν z η A P x+zeroPart η M0 A P x+nyquistPart η Mpi A P x

def frequencyCoefficient (η : ℝ) (A Ai : Matrix m n ℂ) (P : Matrix n n ℂ) (z : ℂ) : Matrix m m ℂ :=
  NoiseResponse.Curvature.response η (transfer η A P z) Ai (Aiᴴ*A+Aᴴ*Ai)

def splitResponse (ν : Measure Ω) (z : Ω → ℂ) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x v : E) : ℝ :=
  isotropicFrozenResponse ν z η A P x v+
    (frequencyCoefficient η (A x) (fderiv ℝ A x v) (P x) 1*M0).trace.re+
    (frequencyCoefficient η (A x) (fderiv ℝ A x v) (P x) (-1)*Mpi).trace.re

theorem complexMul_contDiffAt {l r s : Type*} [Fintype l] [DecidableEq l]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (A : E → Matrix l r ℂ) (B : E → Matrix r s ℂ) (x : E)
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x) :
    ContDiffAt ℝ 2 (fun y => A y*B y) x := by
  simpa only [Function.comp_def,complexMulCLM_apply] using!
    ((complexMulCLM (l := l) (m := r) (n := s)).contDiff.contDiffAt.comp x hA).clm_apply hB

theorem parts_contDiffAt (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ w, ‖z w‖=1) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x : E)
    (hA : ContDiffAt ℝ 2 A x) (hP : ContDiffAt ℝ 2 P x)
    (hb : ‖normalFilter η (A x) (P x)‖<1) :
    ContDiffAt ℝ 2 (scalarPart ν z η A P) x ∧
      ContDiffAt ℝ 2 (zeroPart η M0 A P) x ∧ ContDiffAt ℝ 2 (nyquistPart η Mpi A P) x := by
  have hAH : ContDiffAt ℝ 2 (fun y => (A y)ᴴ) x := by
    simpa only [Function.comp_def,adjointRealCLM_apply] using!
      (adjointRealCLM (m := m) (n := n)).contDiff.contDiffAt.comp x hA
  have hH := complexMul_contDiffAt _ _ x hAH hA
  have hPE := complexMul_contDiffAt _ _ x hA (transfer_contDiffAt η A P x hA hP hb 1 (by simp))
  have hT := nyquistOutputInverse_contDiffAt η A P x hA hP hb
  have hHT := complexMul_contDiffAt _ _ x (complexMul_contDiffAt _ _ x hA hAH) hT
  refine ⟨isotropicPotential_contDiffAt ν z hu η P _ x hP hH hb,?_,?_⟩
  · let L := NoiseResponse.TraceSeries.traceLeftCLM matrixTrace M0
    have hh := (L.contDiff.contDiffAt.comp x hPE).const_smul (-(2*η)⁻¹)
    simpa only [Function.comp_def,L,NoiseResponse.TraceSeries.traceLeftCLM_apply,matrixTrace_apply,
      zeroPart,NoiseResponse.GeneralEndpoint.zeroPotential,outputProjector,smul_eq_mul] using! hh
  · let L := NoiseResponse.TraceSeries.traceLeftCLM matrixTrace Mpi
    have hh := (L.contDiff.contDiffAt.comp x hHT).const_smul (1/2 : ℝ)
    simpa only [Function.comp_def,L,NoiseResponse.TraceSeries.traceLeftCLM_apply,matrixTrace_apply,
      nyquistPart,NoiseResponse.Classification.nyquistPotential,
      NoiseResponse.Classification.traceRealCLM_apply,smul_eq_mul] using! hh

theorem fullPotential_contDiffAt (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ w, ‖z w‖=1) (η : ℝ) (M0 Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x : E)
    (hA : ContDiffAt ℝ 2 A x) (hP : ContDiffAt ℝ 2 P x)
    (hb : ‖normalFilter η (A x) (P x)‖<1) :
    ContDiffAt ℝ 2 (fullPotential ν z η M0 Mpi A P) x := by
  obtain ⟨h1,h2,h3⟩ := parts_contDiffAt ν z hu η M0 Mpi A P x hA hP hb
  exact (h1.add h2).add h3

theorem fullPotential_gradient_identity (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hz : Measurable z) (hu : ∀ w, ‖z w‖=1)
    (η : ℝ) (hη : η ≠ 0) (M0 Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x v : E)
    (hA : ContDiffAt ℝ 2 A x) (hP : ContDiffAt ℝ 2 P x)
    (hproj : IsNormalProjectorField A P)
    (hAt : (A x)ᴴ=(A x)ᵀ) (hAit : (fderiv ℝ A x v)ᴴ=(fderiv ℝ A x v)ᵀ)
    (hPt : (P x)ᵀ=P x) (hb : ‖normalFilter η (A x) (P x)‖<1) :
    fderiv ℝ (fullPotential ν z η M0 Mpi A P) x v=
      -splitResponse ν z η M0 Mpi A P x v := by
  obtain ⟨h1,h2,h3⟩ := parts_contDiffAt ν z hu η M0 Mpi A P x hA hP hb
  have hdA := hA.differentiableAt (by norm_num)
  have hdP := hP.differentiableAt (by norm_num)
  have hgap : ∀ᶠ y in 𝓝 x, ‖normalFilter η (A y) (P y)‖<1 :=
    ((normalFilter_contDiffAt η A P x hA hP).continuousAt.norm.eventually_lt_const hb)
  have hPE := complexMul_contDiffAt _ _ x hA (transfer_contDiffAt η A P x hA hP hb 1 (by simp))
  have hPEprops : ∀ᶠ y in 𝓝 x,
      (outputProjector η (A y) (P y))ᴴ=outputProjector η (A y) (P y) ∧
        outputProjector η (A y) (P y)*outputProjector η (A y) (P y)=outputProjector η (A y) (P y) ∧
          outputProjector η (A y) (P y)*A y=A y := by
    filter_upwards [hgap] with y hy
    have hp := hproj y
    have he := zero_output_projector η (A y) (P y) hp.2.1 hp.1 hp.2.2.1 hp.2.2.2 hy
    exact ⟨he.1,he.2.1,he.2.2.1⟩
  have hPP : ∀ᶠ y in 𝓝 x, P y*P y=P y := Eventually.of_forall (fun y => (hproj y).2.1)
  have hi := isotropic_gradient_identity ν z hz hu η hη A P x v hdA hdP hPP hAt hAit hPt
    (hproj x).1 (hproj x).2.2.1 (by simpa only [hAt] using (hproj x).2.2.2) hb
  have hz0 := NoiseResponse.GeneralEndpoint.zero_gradient_identity η M0 A
    (fun y => outputProjector η (A y) (P y)) (transfer η (A x) (P x) 1) x v hdA
    (hPE.differentiableAt (by norm_num))
    (hPEprops.mono (fun y hy => hy.2.1)) (hPEprops.mono (fun y hy => hy.1))
    (hPEprops.mono (fun y hy => hy.2.2)) rfl
  have hT := nyquistOutputInverse_contDiffAt η A P x hA hP hb
  have hden : ∀ᶠ y in 𝓝 x, NoiseResponse.Classification.nyquistResolventDen η
      (A y*(A y)ᴴ)*nyquistOutputInverse η (A y) (P y)=1 := by
    filter_upwards [hgap] with y hy
    exact nyquistOutputInverse_right η (A y) (P y) (hproj y).2.2.1 hy
  have hpi := NoiseResponse.Classification.nyquist_gradient_identity η hη Mpi A
    (fun y => nyquistOutputInverse η (A y) (P y)) x v hdA
    (hT.differentiableAt (by norm_num)) hden
  rw [← nyquist_transfer_eq η (A x) (P x) (hproj x).2.2.1 (hproj x).2.2.2 hb] at hpi
  have hd1 := NoiseResponse.MatrixCalculus.hasDerivAt_line (h1.differentiableAt (by norm_num)) v
  have hd2 := NoiseResponse.MatrixCalculus.hasDerivAt_line (h2.differentiableAt (by norm_num)) v
  have hd3 := NoiseResponse.MatrixCalculus.hasDerivAt_line (h3.differentiableAt (by norm_num)) v
  have hh := ((hd1.add hd2).add hd3).deriv
  have htot := NoiseResponse.MatrixCalculus.hasDerivAt_line
    ((fullPotential_contDiffAt ν z hu η M0 Mpi A P x hA hP hb).differentiableAt (by norm_num)) v
  change deriv (fun t : ℝ => fullPotential ν z η M0 Mpi A P (x+t • v)) 0=_ at hh
  rw [htot.deriv] at hh
  change deriv (fun t : ℝ => scalarPart ν z η A P (x+t • v)) 0=_ at hi
  rw [hd1.deriv] at hi
  change deriv (fun t : ℝ => zeroPart η M0 A P (x+t • v)) 0=_ at hz0
  rw [hd2.deriv] at hz0
  change deriv (fun t : ℝ => nyquistPart η Mpi A P (x+t • v)) 0=_ at hpi
  rw [hd3.deriv] at hpi
  have hi' : fderiv ℝ (scalarPart ν z η A P) x v=-isotropicFrozenResponse ν z η A P x v := by
    exact hi
  have hz' : fderiv ℝ (zeroPart η M0 A P) x v=
      -(frequencyCoefficient η (A x) (fderiv ℝ A x v) (P x) 1*M0).trace.re := by
    simpa only [frequencyCoefficient] using! hz0
  have hp' : fderiv ℝ (nyquistPart η Mpi A P) x v=
      -(frequencyCoefficient η (A x) (fderiv ℝ A x v) (P x) (-1)*Mpi).trace.re := by
    simpa only [frequencyCoefficient] using! hpi
  rw [hh,hi',hz',hp',splitResponse]
  ring

end NoiseResponse.Sufficiency
