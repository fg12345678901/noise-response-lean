/- Added by cx on 2026-10-29: identify the constructed global trace
   potential with equations (13)--(14), using the positive eigenvalues
   of the output Gram matrix, including rectangular and rank-deficient J. -/
module

public import NoiseResponse.GramSpectralPotential
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2300
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory Polynomial
open scoped Topology Matrix.Norms.L2Operator ComplexOrder
namespace NoiseResponse.ManuscriptPotential
open NoiseResponse.IsotropicSpectrum NoiseResponse.RankSafe NoiseResponse.Sufficiency
variable {Ω m n : Type*} [MeasurableSpace Ω]
variable [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]

theorem gram_eigenvalue_sum (A : Matrix m n ℂ) (ψ : ℝ → ℝ) (hψ : ψ 0=0) :
    (∑ i, ψ ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i))=
      ∑ j, ψ ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) := by
  have hH := Matrix.isHermitian_mul_conjTranspose_self A
  have hK := Matrix.isHermitian_conjTranspose_mul_self A
  have hh := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A Aᴴ)
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (A*Aᴴ).charpoly_monic.ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Aᴴ*A).charpoly_monic.ne_zero),
    Polynomial.roots_X_pow,Polynomial.roots_X_pow,hH.roots_charpoly_eq_eigenvalues,
    hK.roots_charpoly_eq_eigenvalues] at hh
  have he := congrArg (fun s : Multiset ℂ => (s.map (fun w => ψ w.re)).sum) hh
  simpa only [Multiset.map_add,Multiset.sum_add,Multiset.map_nsmul,Multiset.map_singleton,
    Multiset.sum_nsmul,Multiset.sum_singleton,Complex.zero_re,hψ,nsmul_zero,zero_add,
    Multiset.map_map,Function.comp_def,Complex.ofReal_re] using! he

theorem isotropic_positive_output_formula (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ w, ‖z w‖=1) (η : ℝ) (hη : η ≠ 0)
    (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) :
    -(2*η)⁻¹*NoiseResponse.TraceSeries.tracePrimitive matrixTrace (spectralCoeff ν z) (normalFilter η A P)=
      (1/2 : ℝ)*∑ i, if 0<(Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i then
        phi ν z η ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i) else 0 := by
  rw [isotropic_positive_input_formula ν z hu η hη A P hPP hAP hPA hb]
  congr 1
  exact (gram_eigenvalue_sum A (fun h => if 0<h then phi ν z η h else 0) (by simp)).symm

theorem nyquist_inverse_formula (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hAP : A*P=A) (hb : ‖normalFilter η A P‖<1) :
    nyquistOutputInverse η A P=((2 : ℝ) • (1 : Matrix m m ℂ)-η • (A*Aᴴ))⁻¹ :=
  (Matrix.inv_eq_right_inv (nyquistOutputInverse_right η A P hAP hb)).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le

/-- The actual globally defined potential, evaluated in the manuscript's
    output-positive-eigenvalue notation. It applies at repeated and zero
    eigenvalues and uses the actual output range projector and matrix inverse. -/
theorem manuscript_potential_formula (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ w, ‖z w‖=1) (η : ℝ) (hη : η ≠ 0) (M0 Mpi : Matrix m m ℂ)
    (A : E → Matrix m n ℂ) (P : E → Matrix n n ℂ) (x : E)
    (hPP : P x*P x=P x) (hAP : A x*P x=A x) (hPA : P x*(A x)ᴴ=(A x)ᴴ)
    (hb : ‖normalFilter η (A x) (P x)‖<1) :
    fullPotential ν z η M0 Mpi A P x=
      (1/2 : ℝ)*(∑ i, if 0<(Matrix.isHermitian_mul_conjTranspose_self (A x)).eigenvalues i then
        phi ν z η ((Matrix.isHermitian_mul_conjTranspose_self (A x)).eigenvalues i) else 0)-
      (2*η)⁻¹*(M0*outputProjector η (A x) (P x)).trace.re+
      (1/2 : ℝ)*(Mpi*((A x*(A x)ᴴ)*((2 : ℝ) • (1 : Matrix m m ℂ)-η • (A x*(A x)ᴴ))⁻¹)).trace.re := by
  unfold fullPotential scalarPart zeroPart nyquistPart isotropicPotential
  unfold NoiseResponse.TraceSeries.supportedPotential NoiseResponse.GeneralEndpoint.zeroPotential
  dsimp only
  have hi := isotropic_positive_output_formula ν z hu η hη (A x) (P x) hPP hAP hPA hb
  simp only [normalFilter] at hi
  rw [hi]
  unfold NoiseResponse.Classification.nyquistPotential
  simp only [NoiseResponse.Classification.traceRealCLM_apply]
  rw [nyquist_inverse_formula η (A x) (P x) hAP hb]
  ring

end NoiseResponse.ManuscriptPotential
