/- Added by cx on 2026-10-29: assemble zero, positive, and negative
   covariance coefficients into the full spectral-test identity. -/
module

public import NoiseResponse.SpectralIsotropy
public import NoiseResponse.NativeCovarianceNecessity
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

def complexifyMatrix (M : Matrix m m ℝ) : Matrix m m ℂ :=
  fun i j => (M i j : ℂ)

@[simp] theorem complexifyMatrix_add (M N : Matrix m m ℝ) :
    complexifyMatrix (M+N) = complexifyMatrix M+complexifyMatrix N := by
  ext i j
  exact Complex.ofReal_add _ _

@[simp] theorem complexifyMatrix_sub (M N : Matrix m m ℝ) :
    complexifyMatrix (M-N) = complexifyMatrix M-complexifyMatrix N := by
  ext i j
  exact Complex.ofReal_sub _ _

@[simp] theorem complexifyMatrix_smul (c : ℝ) (M : Matrix m m ℝ) :
    complexifyMatrix (c • M) = (c : ℂ) • complexifyMatrix M := by
  ext i j
  exact Complex.ofReal_mul _ _

@[simp] theorem complexifyMatrix_one :
    complexifyMatrix (1 : Matrix m m ℝ) = (1 : Matrix m m ℂ) := by
  ext i j
  by_cases h : i=j <;> simp [complexifyMatrix, Matrix.one_apply, h]

@[simp] theorem complexifyMatrix_adjoint (M : Matrix m m ℝ) :
    (complexifyMatrix M)ᴴ = complexifyMatrix Mᵀ := by
  ext i j
  simp [complexifyMatrix, Matrix.conjTranspose_apply]

/-- The negative modes use Hermitian symmetry of a positive matrix
    spectrum; the zero mode is included separately. The conclusion is
    an identity on every continuous test function, not finite lags. -/
theorem covariance_to_full_spectral_tests
    (L : C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ)
    (Γ : ℕ → Matrix m m ℝ) (Γ0 M0 Mpi : Matrix m m ℝ)
    (hM0 : M0ᵀ=M0) (hMpi : Mpiᵀ=Mpi)
    (p0 ppi : AddCircle T)
    (hp0 : ∀ n : ℤ, fourier n p0 = 1)
    (hppi : ∀ n : ℕ, fourier (n : ℤ) ppi = (-1 : ℂ)^n)
    (hzero : L (fourier 0) = complexifyMatrix Γ0)
    (hpositive : ∀ n : ℕ, L (fourier ((n+1 : ℕ) : ℤ)) = complexifyMatrix (Γ n))
    (hnegative : ∀ n : ℤ, L (fourier (-n)) = (L (fourier n))ᴴ)
    (hc0 : ∃ c0 : ℝ, Γ0=M0+Mpi+c0 • (1 : Matrix m m ℝ))
    (hcn : ∀ n, ∃ cn : ℝ, Γ n=M0-((-1 : ℝ)^n) • Mpi+cn • (1 : Matrix m m ℝ)) :
    ∃ ν : C(AddCircle T, ℂ) →L[ℂ] ℂ,
      L = scalarMatrixCLM.comp ν + pointMatrixTest p0 (complexifyMatrix M0) +
        pointMatrixTest ppi (complexifyMatrix Mpi) := by
  have hpos (n : ℕ) : ∃ c : ℂ, L (fourier (n : ℤ)) =
      complexifyMatrix M0+(-1 : ℂ)^n • complexifyMatrix Mpi+c • (1 : Matrix m m ℂ) := by
    cases n with
    | zero =>
        obtain ⟨c, hc⟩ := hc0
        refine ⟨(c : ℂ), ?_⟩
        change L (fourier (0 : ℤ)) = _
        rw [hzero, hc]
        simp
    | succ n =>
        obtain ⟨c, hc⟩ := hcn n
        refine ⟨(c : ℂ), ?_⟩
        rw [hpositive n, hc]
        simp only [complexifyMatrix_add, complexifyMatrix_sub, complexifyMatrix_smul,
          complexifyMatrix_one, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
          pow_succ, mul_neg, mul_one, neg_smul]
        module
  apply full_spectral_test_decomposition L p0 ppi (complexifyMatrix M0) (complexifyMatrix Mpi)
  intro n
  cases n with
  | ofNat n =>
      obtain ⟨c, hc⟩ := hpos n
      refine ⟨c, ?_⟩
      change L (fourier (n : ℤ)) - fourier (n : ℤ) p0 • _ - fourier (n : ℤ) ppi • _ = _
      rw [hc, hp0, hppi, one_smul]
      module
  | negSucc n =>
      obtain ⟨c, hc⟩ := hpos (n+1)
      refine ⟨star c, ?_⟩
      have he : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
      rw [he, hnegative, hc, hp0, fourier_neg, hppi]
      simp only [one_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        complexifyMatrix_adjoint, hM0, hMpi, Matrix.conjTranspose_one, map_pow,
        map_neg, map_one, star_pow, star_neg, star_one, pow_succ]
      simp only [starRingEnd_apply]
      module

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.covariance_to_full_spectral_tests
