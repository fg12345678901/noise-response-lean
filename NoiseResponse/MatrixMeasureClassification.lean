/- Added by cx on 2026-10-29: the necessary classification in the
   original measurable-set representation, including real PSD endpoints. -/
module

public import NoiseResponse.FlatSpectralResponse
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1200
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

theorem realPart_posSemidef (A : Matrix m m ℂ) (hA : A.PosSemidef) :
    (matrixRealCLM A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have he := congrArg (fun B : Matrix m m ℂ => (B i j).re) hA.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, matrixRealCLM_apply,
      Complex.star_def, Complex.conj_re, star_trivial] using he
  · intro x
    have hp := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (fun i => (x i : ℂ)))).1
    simpa only [dotProduct, Matrix.mulVec, Complex.re_sum, Pi.star_apply,
      Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, zero_mul, mul_zero, sub_zero, zero_add,
      add_zero, Matrix.smul_apply, matrixRealCLM_apply, star_trivial] using hp

namespace PSDMatrixMeasure
variable (M : PSDMatrixMeasure (AddCircle T) m)

def endpoint0 : Matrix m m ℝ := matrixRealCLM (M.value {0})
def endpointPi : Matrix m m ℝ := matrixRealCLM (M.value {nyquistPoint T})

theorem endpoint0_positive : M.endpoint0.PosSemidef :=
  realPart_posSemidef _ (M.positive _ (measurableSet_singleton _))

theorem endpointPi_positive : M.endpointPi.PosSemidef :=
  realPart_posSemidef _ (M.positive _ (measurableSet_singleton _))

theorem endpoints_real (hr : M.RealReflection) :
    complexifyMatrix M.endpoint0=M.value {0} ∧
      complexifyMatrix M.endpointPi=M.value {nyquistPoint T} := by
  let S := M.toRealMatrixSpectrum hr
  have h0 : S.atom0=M.value {0} := M.integral_spectrum_represents hr _ (measurableSet_singleton _)
  have hpi : S.atomPi=M.value {nyquistPoint T} :=
    M.integral_spectrum_represents hr _ (measurableSet_singleton _)
  have he := S.atoms_real
  change complexifyMatrix (matrixRealCLM S.atom0)=S.atom0 ∧
    complexifyMatrix (matrixRealCLM S.atomPi)=S.atomPi at he
  simpa only [h0, hpi, endpoint0, endpointPi] using he

/-- Literal condition (3) of the paper, for an original finite PSD matrix
    measure. Endpoint matrices are actual real PSD matrices, and equality
    holds on every measurable set. -/
def HasClassifiedSpectrum : Prop :=
  ∃ (ν : Measure (AddCircle T)) (M0 Mpi : Matrix m m ℝ),
    IsFiniteMeasure ν ∧ ν {(0 : AddCircle T)}=0 ∧ ν {nyquistPoint T}=0 ∧
      ν.map (fun x => -x)=ν ∧ M0.PosSemidef ∧ Mpi.PosSemidef ∧
      ∀ s : Set (AddCircle T), MeasurableSet s →
        M.value s=(ν.real s : ℂ) • (1 : Matrix m m ℂ)+
          (if (0 : AddCircle T) ∈ s then complexifyMatrix M0 else 0)+
          (if nyquistPoint T ∈ s then complexifyMatrix Mpi else 0)

theorem flat_spectral_necessity_complete (hr : M.RealReflection)
    (η : ℝ) (hη : 0 < η)
    (hp : (M.toRealMatrixSpectrum hr).AllFlatSpectralPotentials η) :
    M.HasClassifiedSpectrum := by
  obtain ⟨ν,hfinite,h0,hpi,href,hs⟩ := M.flat_spectral_measure_necessity hr η hη hp
  refine ⟨ν,M.endpoint0,M.endpointPi,hfinite,h0,hpi,href,
    M.endpoint0_positive,M.endpointPi_positive,?_⟩
  intro s hmeas
  rw [(M.endpoints_real hr).1, (M.endpoints_real hr).2]
  exact hs s hmeas

end PSDMatrixMeasure
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.PSDMatrixMeasure.flat_spectral_necessity_complete
