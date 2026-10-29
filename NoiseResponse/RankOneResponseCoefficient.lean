/- Added by cx on 2026-10-29: the actual rectangular-matrix A4 response
   coefficient reduces to the stable rank-one transfer response. -/
module

public import NoiseResponse.MatrixMeasureClassification
public import NoiseResponse.FlatUpdateGeometry
public import NoiseResponse.CurvatureAlgebra
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1500
set_option maxHeartbeats 5000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder ComplexConjugate Classical
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

def realVector (u : m → ℝ) : m → ℂ := fun i => (u i : ℂ)
def normalColumn (u : m → ℝ) : Matrix m Unit ℂ := fun i _ => (u i : ℂ)
def normalGramVariation (u v : m → ℝ) : Matrix Unit Unit ℂ :=
  fun _ _ => (2*probe (1 : Matrix m m ℝ) u v : ℝ)
def rankOneTransfer (η a : ℝ) (z : ℂ) (u : m → ℝ) : Matrix Unit m ℂ :=
  fun _ j => (η : ℂ)*normalTransfer a z*(u j : ℂ)

theorem rankOneTransfer_equation (η a : ℝ) (ha : ‖a‖<1) (z : ℂ) (hz : ‖z‖=1)
    (u : m → ℝ) :
    ((z-(a : ℂ)) • (1 : Matrix Unit Unit ℂ))*rankOneTransfer η a z u=
      η • (normalColumn u)ᴴ := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, rankOneTransfer, normalColumn, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (η : ℂ)*((z-(a : ℂ))*normalTransfer a z)*(u j : ℂ) := by ring
    _ = _ := by rw [normalTransfer_equation a ha z hz]; simp

theorem normalGramVariation_actual (u v : m → ℝ) :
    normalGramVariation u v=(normalColumn v)ᴴ*normalColumn u+
      (normalColumn u)ᴴ*normalColumn v := by
  ext i j
  simp only [normalGramVariation, Matrix.add_apply, Matrix.mul_apply,
    normalColumn, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal,
    probe_identity_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rankOne_response_matrix (η a : ℝ) (hη : η ≠ 0) (ha : ‖a‖<1)
    (z : ℂ) (hz : ‖z‖=1) (u v : m → ℝ) :
    NoiseResponse.Curvature.response η (rankOneTransfer η a z u)
      (normalColumn v) (normalGramVariation u v)=
      (1/2 : ℂ) • (star (normalTransfer a z) •
        Matrix.vecMulVec (realVector u) (realVector v)+
        normalTransfer a z • Matrix.vecMulVec (realVector v) (realVector u))-
        ((η*probe (1 : Matrix m m ℝ) u v : ℝ) : ℂ) •
          (normalPowerKernel a z • Matrix.vecMulVec (realVector u) (realVector u)) := by
  have he : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  rw [← normalTransfer_power a ha z hz]
  ext i j
  simp [NoiseResponse.Curvature.response, rankOneTransfer, normalColumn,
    normalGramVariation, Matrix.mul_apply, Matrix.vecMulVec, realVector,
    Matrix.conjTranspose_apply, normalTransfer_power a ha z hz, Complex.real_smul,
    mul_comm, mul_left_comm, mul_assoc]
  field_simp
  <;> ring

def complexProbe (D : Matrix m m ℂ) (u v : m → ℝ) : ℂ :=
  realVector u ⬝ᵥ (D *ᵥ realVector v)

theorem trace_outer_mul (D : Matrix m m ℂ) (u v : m → ℝ) :
    Matrix.trace (Matrix.vecMulVec (realVector u) (realVector v)*D)=complexProbe D v u := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    complexProbe, dotProduct, Matrix.mulVec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem complexProbe_real (D : Matrix m m ℂ) (u v : m → ℝ) :
    (complexProbe D u v).re=probe (matrixRealCLM D) u v := by
  simp only [complexProbe, dotProduct, Matrix.mulVec, Complex.re_sum, realVector,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, probe, Matrix.toBilin'_apply, matrixRealCLM_apply, Finset.mul_sum,
    mul_assoc]

theorem complexProbe_smul (D : Matrix m m ℂ) (c : ℂ) (u v : m → ℝ) :
    complexProbe (c • D) u v=c*complexProbe D u v := by
  simp only [complexProbe, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem complexProbe_hermitian (D : Matrix m m ℂ) (hD : Dᴴ=D) (u v : m → ℝ) :
    complexProbe D v u=star (complexProbe D u v) := by
  simp only [complexProbe, dotProduct, Matrix.mulVec, realVector, Finset.mul_sum,
    Complex.star_def, map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg (fun A : Matrix m m ℂ => A j i) hD
  change (starRingEnd ℂ) (D i j)=D j i at he
  rw [he]
  ring

theorem rankOne_response_readout (η a : ℝ) (hη : η ≠ 0) (ha : ‖a‖<1)
    (z : ℂ) (hz : ‖z‖=1) (u v : m → ℝ) (D : Matrix m m ℂ) (hD : Dᴴ=D) :
    (Matrix.trace (NoiseResponse.Curvature.response η (rankOneTransfer η a z u)
      (normalColumn v) (normalGramVariation u v)*D)).re=
      probe (matrixRealCLM (causalCrossKernel a z • D)) v u-
        η*probe (matrixRealCLM (normalPowerKernel a z • D)) u u*probe 1 v u := by
  rw [rankOne_response_matrix η a hη ha z hz u v]
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, trace_outer_mul,
    complexProbe_hermitian D hD u v, ← normalTransfer_star a ha z hz,
    ← complexProbe_real, complexProbe_smul]
  have hp := probe_symmetric (1 : Matrix m m ℝ) (by simp) u v
  rw [hp]
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  <;> ring

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.rankOne_response_readout
