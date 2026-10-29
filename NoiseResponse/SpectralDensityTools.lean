/- Added by cx on 2026-10-29: covariance, Hermitian symmetry, and
   actual atom removal for an integrable matrix spectrum. -/
module

public import NoiseResponse.SpectralNativeBridge
public import NoiseResponse.CircleEndpoints
public import NoiseResponse.SpectralIsotropy
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]

theorem fourier_nat_power (n : ℕ) (x : AddCircle T) :
    fourier (n : ℤ) x = (fourier 1 x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem spectralCovariance_fourier
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (n : ℕ) :
    spectralCovariance μ F (fun x => fourier 1 x) n =
      densityTest μ F hF (fourier ((n+1 : ℕ) : ℤ)) := by
  change (∫ x, (fourier 1 x)^(n+1) • F x ∂μ) =
    ∫ x, fourier ((n+1 : ℕ) : ℤ) x • F x ∂μ
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (fourier 1 x)^(n+1) • F x = fourier ((n+1 : ℕ) : ℤ) x • F x
    rw [fourier_nat_power])

theorem hermitian_integral
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (hH : ∀ᵐ x ∂μ, (F x)ᴴ=F x) :
    (∫ x, F x ∂μ)ᴴ = ∫ x, F x ∂μ := by
  rw [← NoiseResponse.MatrixCalculus.adjCLM_apply,
    ← NoiseResponse.MatrixCalculus.adjCLM.integral_comp_comm hF]
  apply integral_congr_ae
  exact hH

theorem realPart_hermitian_symmetric (A : Matrix m m ℂ) (hA : Aᴴ=A) :
    (matrixRealCLM A)ᵀ=matrixRealCLM A := by
  ext i j
  have he := congrArg (fun M : Matrix m m ℂ => (M i j).re) hA
  simpa only [matrixRealCLM_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.conj_re] using he

theorem hermitian_spectrum_negative
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (hH : ∀ᵐ x ∂μ, (F x)ᴴ=F x) (n : ℤ) :
    densityTest μ F hF (fourier (-n)) = (densityTest μ F hF (fourier n))ᴴ := by
  change (∫ x, fourier (-n) x • F x ∂μ) = (∫ x, fourier n x • F x ∂μ)ᴴ
  rw [← NoiseResponse.MatrixCalculus.adjCLM_apply,
    ← NoiseResponse.MatrixCalculus.adjCLM.integral_comp_comm (integrable_test_smul μ F hF (fourier n))]
  apply integral_congr_ae
  filter_upwards [hH] with x hx
  simp only [NoiseResponse.MatrixCalculus.adjCLM_apply, Matrix.conjTranspose_smul,
    hx, fourier_neg, starRingEnd_apply]

theorem singleton_test_integral
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (p : AddCircle T) (φ : C(AddCircle T, ℂ)) :
    (∫ x in {p}, φ x • F x ∂μ) = φ p • (∫ x in {p}, F x ∂μ) := by
  rw [← integral_smul]
  apply setIntegral_congr_fun (measurableSet_singleton p)
  intro x hx
  simpa only [mem_singleton_iff.mp hx]

theorem remove_actual_atoms_test
    (μ : Measure (AddCircle T)) (F : AddCircle T → Matrix m m ℂ)
    (hF : Integrable F μ) (p0 ppi : AddCircle T) (hne : p0 ≠ ppi)
    (φ : C(AddCircle T, ℂ)) :
    (∫ x, φ x • F x ∂μ.restrict ({p0, ppi}ᶜ)) =
      (∫ x, φ x • F x ∂μ) - φ p0 • (∫ x in {p0}, F x ∂μ) -
        φ ppi • (∫ x in {ppi}, F x ∂μ) := by
  have hφ := integrable_test_smul μ F hF φ
  have hsplit := integral_add_compl (μ := μ) (s := ({p0, ppi} : Set (AddCircle T)))
    (by measurability) hφ
  have hunion : (∫ x in {p0, ppi}, φ x • F x ∂μ) =
      φ p0 • (∫ x in {p0}, F x ∂μ)+φ ppi • (∫ x in {ppi}, F x ∂μ) := by
    rw [show ({p0, ppi} : Set (AddCircle T)) = {p0} ∪ {ppi} by rfl,
      setIntegral_union (by simpa using hne) (measurableSet_singleton ppi)
        hφ.integrableOn hφ.integrableOn,
      singleton_test_integral, singleton_test_integral]
  rw [hunion] at hsplit
  rw [← hsplit]
  abel

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.remove_actual_atoms_test
