/- Added by cx on 2026-10-29: full integer Fourier identification of
   the matrix spectral test functional after two actual atom terms.
   Positivity and measure representation of the scalar functional are
   separate from this identification theorem. -/
module

public import NoiseResponse.SpectralIdentification
public import NoiseResponse.MatrixCalculus
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

def matrixEntryCLM (i j : m) : Matrix m m ℂ →L[ℂ] ℂ :=
  (show Matrix m m ℂ →ₗ[ℂ] ℂ from
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).toContinuousLinearMap

def scalarMatrixCLM : ℂ →L[ℂ] Matrix m m ℂ :=
  (show ℂ →ₗ[ℂ] Matrix m m ℂ from
    { toFun := fun c => c • (1 : Matrix m m ℂ)
      map_add' := by intros; exact add_smul _ _ _
      map_smul' := by intros; simp only [smul_eq_mul, smul_smul, RingHom.id_apply] }).toContinuousLinearMap

def pointMatrixTest (p : AddCircle T) (M : Matrix m m ℂ) :
    C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f p • M
      map_add' := by intros; simp only [ContinuousMap.add_apply, add_smul]
      map_smul' := by intros; simp only [ContinuousMap.smul_apply,
        RingHom.id_apply, smul_eq_mul, smul_smul] }
    ‖M‖ (by
      intro f
      change ‖f p • M‖ ≤ ‖M‖*‖f‖
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm p) (norm_nonneg M))

@[simp] theorem pointMatrixTest_apply (p : AddCircle T) (M : Matrix m m ℂ)
    (f : C(AddCircle T, ℂ)) : pointMatrixTest p M f = f p • M := rfl

theorem isotropic_functional_of_scalar_fourier
    (L : C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ)
    (h : ∀ n : ℤ, ∃ cn : ℂ, L (fourier n) = cn • (1 : Matrix m m ℂ)) :
    ∃ ν : C(AddCircle T, ℂ) →L[ℂ] ℂ,
      L = scalarMatrixCLM.comp ν := by
  let i : m := Classical.arbitrary m
  refine ⟨(matrixEntryCLM i i).comp L, ?_⟩
  apply continuousLinearMap_eq_of_fourier
  intro n
  obtain ⟨c, hc⟩ := h n
  simp only [ContinuousLinearMap.comp_apply, hc]
  change c • (1 : Matrix m m ℂ) = ((c • (1 : Matrix m m ℂ)) i i) • 1
  simp

/-- This is the spectral-uniqueness step for all integer modes, not a
    finite-lag test. The two atom matrices are retained verbatim. -/
theorem full_spectral_test_decomposition
    (L : C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ)
    (p0 ppi : AddCircle T) (M0 Mpi : Matrix m m ℂ)
    (h : ∀ n : ℤ, ∃ cn : ℂ,
      L (fourier n) - fourier n p0 • M0 - fourier n ppi • Mpi =
        cn • (1 : Matrix m m ℂ)) :
    ∃ ν : C(AddCircle T, ℂ) →L[ℂ] ℂ,
      L = scalarMatrixCLM.comp ν + pointMatrixTest p0 M0 + pointMatrixTest ppi Mpi := by
  let R := L-pointMatrixTest p0 M0-pointMatrixTest ppi Mpi
  have hr : ∀ n : ℤ, ∃ cn : ℂ, R (fourier n) = cn • (1 : Matrix m m ℂ) := by
    simpa only [R, ContinuousLinearMap.sub_apply, pointMatrixTest_apply] using h
  obtain ⟨ν, hν⟩ := isotropic_functional_of_scalar_fourier R hr
  refine ⟨ν, ?_⟩
  rw [← hν]
  dsimp [R]
  abel

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.isotropic_functional_of_scalar_fourier
#print axioms NoiseResponse.Classification.full_spectral_test_decomposition
