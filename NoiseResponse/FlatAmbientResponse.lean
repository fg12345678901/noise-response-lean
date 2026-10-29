/- Added by cx on 2026-10-29: the full three-column ambient response
   equals the original rank-one flat response; zero tangent columns are retained. -/
module

public import NoiseResponse.FlatAmbientGeometry
public import NoiseResponse.TransferIsometry
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2200
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.AmbientFlat
open NoiseResponse.Classification NoiseResponse.Geometry NoiseResponse.RankSafe
open NoiseResponse.Sufficiency NoiseResponse.IsotropicSpectrum
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def inclusion : Matrix (Fin 3) Unit ℂ := fun i _ => (normalAxis i : ℂ)

theorem inclusion_isometry : inclusionᴴ*inclusion=1 := by
  ext i j
  norm_num [inclusion,normalAxis,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_three,Pi.single_apply,Matrix.one_apply]

theorem inclusion_column (u : m → ℝ) : normalColumn u*inclusionᴴ=complexify (column u) := by
  ext i j
  fin_cases j <;> simp [normalColumn,inclusion,normalAxis,column,complexify,
    Matrix.vecMulVec_apply,Matrix.mul_apply,Fintype.sum_unique,Pi.single_apply,Matrix.conjTranspose_apply]

theorem inclusion_projector : inclusion*(1 : Matrix Unit Unit ℂ)*inclusionᴴ=complexify projector := by
  rw [Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [inclusion,projector,normalAxis,complexify,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_unique,Pi.single_apply]

theorem ambient_transfer (η : ℝ) (u : m → ℝ)
    (ha : ‖1-η*probe (1 : Matrix m m ℝ) u u‖<1) (z : ℂ) (hz : ‖z‖=1) :
    transfer η (complexify (column u)) (complexify projector) z=
      inclusion*transfer η (normalColumn u) 1 z := by
  have hb := NoiseResponse.FlatBridge.column_filter_stable η u ha
  have hbig : ‖normalFilter η (normalColumn u*inclusionᴴ)
      (inclusion*(1 : Matrix Unit Unit ℂ)*inclusionᴴ)‖<1 := by
    rw [inclusion_column,inclusion_projector]
    exact column_stable η u ha
  simpa only [inclusion_column,inclusion_projector] using
    transfer_isometry η (normalColumn u) 1 inclusion inclusion_isometry hb hbig z hz

theorem ambient_coefficient (η : ℝ) (u v : m → ℝ)
    (ha : ‖1-η*probe (1 : Matrix m m ℝ) u u‖<1) (z : ℂ) (hz : ‖z‖=1) :
    frequencyCoefficient η (complexify (column u)) (complexify (column v)) (complexify projector) z=
      NoiseResponse.Curvature.response η (rankOneTransfer η (1-η*probe (1 : Matrix m m ℝ) u u) z u)
        (normalColumn v) (normalGramVariation u v) := by
  unfold frequencyCoefficient
  rw [ambient_transfer η u ha z hz]
  have he := response_isometry η (normalColumn u) (normalColumn v)
    (transfer η (normalColumn u) 1 z) inclusion inclusion_isometry
  simpa only [inclusion_column,NoiseResponse.FlatBridge.column_transfer η u ha z hz,
    ← normalGramVariation_actual] using! he

def complexColumnCLM : (m → ℝ) →L[ℝ] Matrix m (Fin 3) ℂ := complexifyCLM.comp columnCLM

@[simp] theorem complexColumnCLM_apply (u : m → ℝ) : complexColumnCLM u=complexify (column u) := rfl

theorem column_field_fderiv (A : Plane → m → ℝ) (p v : Plane) (hA : DifferentiableAt ℝ A p) :
    fderiv ℝ (fun q => complexify (column (A q))) p v=complexify (column (fderiv ℝ A p v)) := by
  have hh := complexColumnCLM.hasFDerivAt.comp p hA.hasFDerivAt
  have he := congrArg (fun L : Plane →L[ℝ] Matrix m (Fin 3) ℂ => L v) hh.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,complexColumnCLM_apply] using! he

variable {T : ℝ} [Fact (0 < T)]

theorem measured_ambient_eq_flat (M : PSDMatrixMeasure (AddCircle T) m) (hr : M.RealReflection)
    (η : ℝ) (A : Plane → m → ℝ) (p : Plane) (i : Fin 2)
    (hA : DifferentiableAt ℝ A p) (hn : A p ≠ 0)
    (ha : (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1) :
    measuredFrozenResponse M η (fun q => complexify (column (A q)))
      (fun q => NoiseResponse.Geometry.normalProjector (column (A q))) p (planeAxis i)=
      (M.toRealMatrixSpectrum hr).flatMatrixResponse η A i p := by
  have ha' : ‖1-η*probe (1 : Matrix m m ℝ) (A p) (A p)‖<1 := by
    simpa only [Real.norm_eq_abs] using abs_lt.mpr ha
  unfold measuredFrozenResponse RealMatrixSpectrum.flatMatrixResponse
  simp only [column_field_fderiv A p _ hA,canonical_projector _ hn]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  dsimp only
  rw [ambient_coefficient η (A p) (fderiv ℝ A p (planeAxis i)) ha' (fourier 1 w) (Circle.norm_coe _)]
  rfl

end NoiseResponse.AmbientFlat
