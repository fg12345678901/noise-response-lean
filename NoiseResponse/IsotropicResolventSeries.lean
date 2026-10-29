/- Added by cx on 2026-10-29: the isotropic matrix coefficient series
   equals the actual product of stable frequency resolvents. -/
module

public import NoiseResponse.MatrixIsotropicPrimitive
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1800
set_option maxHeartbeats 7000000
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.IsotropicSpectrum

theorem doubleCoeff_real (z : ℂ) (n : ℕ) : star (doubleCoeff z n)=doubleCoeff z n := by
  unfold doubleCoeff
  simp only [star_sum,star_mul,star_pow,star_star]
  rw [← Finset.sum_range_reflect (fun k => z^(n-k)*(star z)^k) (n+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  simp only [Nat.add_sub_cancel_right,Nat.sub_sub_self hk',mul_comm]

theorem poissonCoeff_complex (z : ℂ) (n : ℕ) :
    (poissonCoeff z n : ℂ)=(1-(z.re : ℂ))*doubleCoeff z n := by
  have hi : (doubleCoeff z n).im=0 := by
    have h := congrArg Complex.im (doubleCoeff_real z n)
    simp only [Complex.star_def,Complex.conj_im] at h
    linarith
  have hr : ((doubleCoeff z n).re : ℂ)=doubleCoeff z n := by
    apply Complex.ext <;> simp [hi]
  simp only [poissonCoeff,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,hr]

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def matrixResolvent (B : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := Ring.inverse (1-z • B)

theorem matrixResolvent_hasSum (B : Matrix n n ℂ) (hB : ‖B‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun k : ℕ => z^k • B^k) (matrixResolvent B z) := by
  have hn : ‖z • B‖<1 := by simpa only [norm_smul,hz,one_mul] using hB
  simpa only [matrixResolvent,smul_pow] using hasSum_geom_series_inverse (z • B) hn

theorem matrixResolvent_inverse (B : Matrix n n ℂ) (hB : ‖B‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    (1-z • B)*matrixResolvent B z=1 ∧ matrixResolvent B z*(1-z • B)=1 := by
  have hu : IsUnit (1-z • B) := isUnit_one_sub_of_norm_lt_one
    (by simpa only [norm_smul,hz,one_mul] using hB)
  exact ⟨Ring.mul_inverse_cancel _ hu,Ring.inverse_mul_cancel _ hu⟩

theorem matrixResolvent_adjoint (B : Matrix n n ℂ) (hB : Bᴴ=B) (z : ℂ) :
    (matrixResolvent B z)ᴴ=matrixResolvent B (star z) := by
  change star (Ring.inverse (1-z • B))=Ring.inverse (1-star z • B)
  rw [← Ring.inverse_star]
  congr 1
  simp only [star_sub,star_one,star_smul,Matrix.star_eq_conjTranspose,hB]

theorem matrixResolvent_transpose (B : Matrix n n ℂ) (hB : Bᵀ=B) (z : ℂ) :
    (matrixResolvent B z)ᵀ=matrixResolvent B z := by
  simp only [matrixResolvent,← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.transpose_nonsing_inv,Matrix.transpose_sub,Matrix.transpose_one,
    Matrix.transpose_smul,hB]

theorem matrixResolvent_product_hasSum (B : Matrix n n ℂ) (hB : ‖B‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun k => doubleCoeff z k • B^k)
      (matrixResolvent B z*matrixResolvent B (star z)) := by
  have hn (w : ℂ) (hw : ‖w‖=1) :
      Summable (fun k : ℕ => ‖w^k • B^k‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => show ‖w^k • B^k‖ ≤ ‖B‖^k by
        simpa only [norm_smul,norm_pow,hw,one_pow,one_mul] using norm_pow_le B k)
      (summable_geometric_of_lt_one (norm_nonneg B) hB)
  have hc := hasSum_sum_range_mul_of_summable_norm (hn z hz)
    (hn (star z) (by simpa only [norm_star] using hz))
  have he (k : ℕ) :
      (∑ j ∈ Finset.range (k+1), (z^j • B^j)*((star z)^(k-j) • B^(k-j)))=
        doubleCoeff z k • B^k := by
    unfold doubleCoeff
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j hj
    have hkj : j+(k-j)=k := Nat.add_sub_of_le
      (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj)
    rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,← pow_add,hkj]
  simpa only [he,(matrixResolvent_hasSum B hB z hz).tsum_eq,
    (matrixResolvent_hasSum B hB (star z) (by simpa only [norm_star] using hz)).tsum_eq] using hc

theorem poisson_matrix_hasSum (B : Matrix n n ℂ) (hB : ‖B‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    HasSum (fun k => (poissonCoeff z k : ℂ) • B^k)
      ((1-(z.re : ℂ)) • (matrixResolvent B z*matrixResolvent B (star z))) := by
  simpa only [smul_smul,poissonCoeff_complex] using
    (matrixResolvent_product_hasSum B hB z hz).const_smul (1-(z.re : ℂ))

end NoiseResponse.IsotropicSpectrum
