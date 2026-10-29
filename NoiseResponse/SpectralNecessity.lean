/- Added by cx on 2026-10-29: necessity from rank-one local potentials
   to the spectral decomposition for positive real stationary spectra
   represented by an integrable density against an arbitrary base measure. -/
module

public import NoiseResponse.SpectralReality
public import NoiseResponse.SpectralDensityTools
public import NoiseResponse.ScalarReflection
public import NoiseResponse.MatrixPositiveIntegral
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1000
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Set Matrix Complex
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable (T : ℝ) (m : Type*) [Fact (0 < T)] [Fintype m] [DecidableEq m] [Nonempty m]

/-- This representation allows atomic and singular spectra: the base
    measure is arbitrary, and is not required to be Lebesgue measure.
    The reality condition is the reality of every covariance matrix. -/
structure RealMatrixSpectrum where
  μ : Measure (AddCircle T)
  F : AddCircle T → Matrix m m ℂ
  integrable : Integrable F μ
  positive : ∀ᵐ x ∂μ, (F x).PosSemidef
  real_moments : ∀ n : ℤ,
    realityProjection (densityTest μ F integrable (fourier n)) =
      densityTest μ F integrable (fourier n)

namespace RealMatrixSpectrum
variable {T m} (S : RealMatrixSpectrum T m)

def L := densityTest S.μ S.F S.integrable
def Γ (n : ℕ) := matrixRealCLM (spectralCovariance S.μ S.F (fun x => fourier 1 x) n)
def Γ0 := matrixRealCLM (∫ x, S.F x ∂S.μ)
def atom0 := ∫ x in {(0 : AddCircle T)}, S.F x ∂S.μ
def atomPi := ∫ x in {nyquistPoint T}, S.F x ∂S.μ
def M0 := matrixRealCLM S.atom0
def Mpi := matrixRealCLM S.atomPi
def bound := ‖(matrixRealCLM : Matrix m m ℂ →L[ℝ] Matrix m m ℝ)‖ * ∫ x, ‖S.F x‖ ∂S.μ

theorem bounded (n : ℕ) : ‖S.Γ n‖ ≤ S.bound :=
  le_trans (matrixRealCLM.le_opNorm _) (mul_le_mul_of_nonneg_left
    (spectral_covariance_bound S.μ S.F S.integrable _
      (fourier 1).continuous.measurable (fun x => Circle.norm_coe _) n) (norm_nonneg _))

def pair (u v : m → ℝ) : PairCovariances :=
  covariancePair S.Γ S.Γ0 S.bound (by unfold bound; positivity) S.bounded u v

def AllRankOnePotentials (η : ℝ) : Prop :=
  ∀ u v, OrthonormalProbePair u v → (S.pair u v).AllAxisPotentials η

theorem hermitian : ∀ᵐ x ∂S.μ, (S.F x)ᴴ=S.F x :=
  S.positive.mono (fun x hx => hx.isHermitian.eq)

theorem atoms_real : complexifyMatrix S.M0=S.atom0 ∧ complexifyMatrix S.Mpi=S.atomPi := by
  have h := spectral_endpoint_masses_real S.μ S.F S.integrable
    (fun x => fourier 1 x) (fourier 1).continuous.measurable
    (fun x => Circle.norm_coe _) (fun n => by
      rw [spectralCovariance_fourier S.μ S.F S.integrable n]
      exact S.real_moments _)
  simpa only [realityProjection_apply, zero_endpoint_preimage, nyquist_endpoint_preimage,
    M0, Mpi, atom0, atomPi] using h

theorem zero_symmetric : S.Γ0ᵀ=S.Γ0 :=
  realPart_hermitian_symmetric _ (hermitian_integral S.μ S.F S.integrable S.hermitian)

theorem atoms_symmetric : S.M0ᵀ=S.M0 ∧ S.Mpiᵀ=S.Mpi := by
  constructor
  · exact realPart_hermitian_symmetric _
      (hermitian_integral _ _ S.integrable.integrableOn (ae_restrict_of_ae S.hermitian))
  · exact realPart_hermitian_symmetric _
      (hermitian_integral _ _ S.integrable.integrableOn (ae_restrict_of_ae S.hermitian))

theorem covariance_necessity (η : ℝ) (hη : 0 < η) (hp : S.AllRankOnePotentials η) :
    (∃ c0 : ℝ, S.Γ0=S.M0+S.Mpi+c0 • (1 : Matrix m m ℝ)) ∧
      ∀ n, ∃ cn : ℝ, S.Γ n=S.M0-((-1 : ℝ)^n) • S.Mpi+cn • (1 : Matrix m m ℝ) := by
  have h := spectral_integral_covariance_necessity S.μ S.F S.integrable
    (fun x => fourier 1 x) (fourier 1).continuous.measurable (fun x => Circle.norm_coe _)
    η hη S.zero_symmetric
    (by simpa only [zero_endpoint_preimage, M0, atom0] using S.atoms_symmetric.1)
    (by simpa only [nyquist_endpoint_preimage, Mpi, atomPi] using S.atoms_symmetric.2) hp
  simpa only [zero_endpoint_preimage, nyquist_endpoint_preimage, Γ0, Γ, M0, Mpi, atom0, atomPi] using h

theorem spectral_test_necessity (η : ℝ) (hη : 0 < η) (hp : S.AllRankOnePotentials η) :
    ∃ l : C(AddCircle T, ℂ) →L[ℂ] ℂ,
      S.L = scalarMatrixCLM.comp l + pointMatrixTest 0 S.atom0 +
        pointMatrixTest (nyquistPoint T) S.atomPi := by
  have hc := S.covariance_necessity η hη hp
  have hz : S.L (fourier 0) = complexifyMatrix S.Γ0 := by
    have he := S.real_moments 0
    have hf : densityTest S.μ S.F S.integrable (fourier 0) = ∫ x, S.F x ∂S.μ := by
      change (∫ x, fourier 0 x • S.F x ∂S.μ) = _
      simp only [fourier_zero, one_smul]
    rw [hf] at he
    simpa only [L, hf, realityProjection_apply, Γ0] using he.symm
  have hpos (n : ℕ) : S.L (fourier ((n+1 : ℕ) : ℤ)) = complexifyMatrix (S.Γ n) := by
    have he := S.real_moments ((n+1 : ℕ) : ℤ)
    rw [← spectralCovariance_fourier S.μ S.F S.integrable n] at he
    dsimp only [L, Γ]
    rw [← spectralCovariance_fourier S.μ S.F S.integrable n]
    simpa only [realityProjection_apply] using he.symm
  obtain ⟨l, hl⟩ := covariance_to_full_spectral_tests S.L S.Γ S.Γ0 S.M0 S.Mpi
    S.atoms_symmetric.1 S.atoms_symmetric.2 0 (nyquistPoint T)
    fourier_eval_zero fourier_nat_nyquist hz hpos
    (hermitian_spectrum_negative S.μ S.F S.integrable S.hermitian) hc.1 hc.2
  exact ⟨l, by simpa only [S.atoms_real.1, S.atoms_real.2] using hl⟩

/-- The measure conclusion includes positivity, finite mass, absence of
    endpoint atoms, reflection symmetry, and equality on every continuous
    test. The only potential hypotheses are genuine local potentials of
    the rank-one response subfamily. -/
theorem positive_measure_necessity (η : ℝ) (hη : 0 < η) (hp : S.AllRankOnePotentials η) :
    ∃ ν : Measure (AddCircle T), IsFiniteMeasure ν ∧
      ν {(0 : AddCircle T)}=0 ∧ ν {nyquistPoint T}=0 ∧ ν.map (fun x => -x)=ν ∧
      ∀ φ : C(AddCircle T, ℂ),
        (∫ x, φ x • S.F x ∂S.μ) =
          (∫ x, φ x ∂ν) • (1 : Matrix m m ℂ) + φ 0 • S.atom0 + φ (nyquistPoint T) • S.atomPi := by
  obtain ⟨l, hl⟩ := S.spectral_test_necessity η hη hp
  let μr := S.μ.restrict ({(0 : AddCircle T), nyquistPoint T}ᶜ)
  have hFr : Integrable S.F μr := S.integrable.integrableOn
  have hsplit (φ : C(AddCircle T, ℂ)) :
      (∫ x, φ x • S.F x ∂μr) = l φ • (1 : Matrix m m ℂ) := by
    rw [remove_actual_atoms_test S.μ S.F S.integrable 0 (nyquistPoint T) nyquist_ne_zero.symm]
    have he := congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] Matrix m m ℂ => L φ) hl
    change (∫ x, φ x • S.F x ∂S.μ) =
      l φ • (1 : Matrix m m ℂ)+φ 0 • S.atom0+φ (nyquistPoint T) • S.atomPi at he
    rw [he]
    change _ - _ • (∫ x in {0}, S.F x ∂S.μ) -
      _ • (∫ x in {nyquistPoint T}, S.F x ∂S.μ) = _
    change _ - _ • S.atom0 - _ • S.atomPi = _
    abel
  have hdiag : ∀ᵐ x ∂μr, ∀ i, 0 ≤ (S.F x i i).re ∧ (S.F x i i).im=0 := by
    filter_upwards [ae_restrict_of_ae S.positive] with x hx
    intro i
    have hi := Complex.nonneg_iff.mp (hx.diag_nonneg (i := i))
    exact ⟨hi.1, hi.2.symm⟩
  obtain ⟨ν, hfinite, hac, hν⟩ := scalar_spectrum_is_positive_measure μr S.F hFr hdiag
    (fun n => ⟨l (fourier n), hsplit (fourier n)⟩)
  letI : IsFiniteMeasure ν := hfinite
  have hν0 : ν {(0 : AddCircle T)}=0 := by
    apply hac
    change S.μ.restrict ({(0 : AddCircle T), nyquistPoint T}ᶜ) {0}=0
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    simp
  have hνpi : ν {nyquistPoint T}=0 := by
    apply hac
    change S.μ.restrict ({(0 : AddCircle T), nyquistPoint T}ᶜ) {nyquistPoint T}=0
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    simp
  have hfull (φ : C(AddCircle T, ℂ)) : (∫ x, φ x • S.F x ∂S.μ) =
      (∫ x, φ x ∂ν) • (1 : Matrix m m ℂ)+φ 0 • S.atom0+φ (nyquistPoint T) • S.atomPi := by
    have he := remove_actual_atoms_test S.μ S.F S.integrable 0 (nyquistPoint T) nyquist_ne_zero.symm φ
    rw [hν φ] at he
    change _ = _ - φ 0 • S.atom0 - φ (nyquistPoint T) • S.atomPi at he
    rw [he]
    abel
  have hpiIm (n : ℤ) : (fourier n (nyquistPoint T)).im=0 := by
    cases n with
    | ofNat n =>
        change (fourier (n : ℤ) (nyquistPoint T)).im=0
        rw [fourier_nat_nyquist]
        have he : (-1 : ℂ)^n = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp
        rw [he]
        exact Complex.ofReal_im _
    | negSucc n =>
        rw [show Int.negSucc n = -((n+1 : ℕ) : ℤ) by omega,
          fourier_neg, fourier_nat_nyquist]
        have he : (-1 : ℂ)^(n+1) = (((-1 : ℝ)^(n+1) : ℝ) : ℂ) := by simp
        rw [he]
        simp only [map_pow, map_neg, map_one, Complex.conj_ofReal, Complex.ofReal_im]
  have hcoeff (n : ℤ) : (∫ x, fourier n x ∂ν).im=0 := by
    let i : m := Classical.arbitrary m
    have hr := congrArg (fun A : Matrix m m ℂ => (A i i).im) (S.real_moments n)
    have hz : (S.L (fourier n) i i).im=0 := by
      simpa only [L, realityProjection_apply, complexifyMatrix, Complex.ofReal_im] using hr.symm
    have he := congrArg (fun A : Matrix m m ℂ => (A i i).im) (hfull (fourier n))
    rw [← S.atoms_real.1, ← S.atoms_real.2] at he
    have hzero := fourier_eval_zero (T := T) n
    change (S.L (fourier n) i i).im = _ at he
    rw [hz] at he
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Complex.add_im, Complex.mul_im, complexifyMatrix, Complex.ofReal_re,
      Complex.ofReal_im, hzero, Complex.one_re, Complex.one_im, hpiIm,
      mul_one, mul_zero, zero_mul, zero_add, add_zero] at he
    exact he.symm
  exact ⟨ν, hfinite, hν0, hνpi, real_fourier_implies_reflection ν hcoeff, hfull⟩

theorem atoms_positive : S.atom0.PosSemidef ∧ S.atomPi.PosSemidef := by
  constructor
  · exact positive_matrix_integral _ _ S.integrable.integrableOn (ae_restrict_of_ae S.positive)
  · exact positive_matrix_integral _ _ S.integrable.integrableOn (ae_restrict_of_ae S.positive)

/-- Public necessity entry point, in the continuous-test representation
    of finite matrix spectra. Both atom masses are the actual masses;
    their reality and positivity, and all scalar measure conditions,
    are conclusions rather than extra premises. -/
theorem rank_one_spectral_necessity (η : ℝ) (hη : 0 < η) (hp : S.AllRankOnePotentials η) :
    S.atom0.PosSemidef ∧ S.atomPi.PosSemidef ∧
      complexifyMatrix S.M0=S.atom0 ∧ complexifyMatrix S.Mpi=S.atomPi ∧
    ∃ ν : Measure (AddCircle T), IsFiniteMeasure ν ∧
      ν {(0 : AddCircle T)}=0 ∧ ν {nyquistPoint T}=0 ∧ ν.map (fun x => -x)=ν ∧
      ∀ φ : C(AddCircle T, ℂ),
        (∫ x, φ x • S.F x ∂S.μ) =
          (∫ x, φ x ∂ν) • (1 : Matrix m m ℂ) + φ 0 • S.atom0 + φ (nyquistPoint T) • S.atomPi :=
  ⟨S.atoms_positive.1, S.atoms_positive.2, S.atoms_real.1, S.atoms_real.2,
    S.positive_measure_necessity η hη hp⟩

end RealMatrixSpectrum
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.RealMatrixSpectrum.spectral_test_necessity
#print axioms NoiseResponse.Classification.RealMatrixSpectrum.positive_measure_necessity
#print axioms NoiseResponse.Classification.RealMatrixSpectrum.rank_one_spectral_necessity
