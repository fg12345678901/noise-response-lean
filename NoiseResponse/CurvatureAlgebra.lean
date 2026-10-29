/- Added by cx on 2026-10-29.
   V6 Appendix A.2: arbitrary finite rectangular matrices, not numerical examples.
   This module proves the algebraic jet identity. The calculus wrapper is separate.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 800
set_option maxHeartbeats 1000000

noncomputable section
open Matrix
open scoped Matrix

namespace NoiseResponse
namespace Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Hermitian part, using real scalar multiplication. -/
def herm (X : Matrix m m ℂ) : Matrix m m ℂ :=
  (2 : ℝ)⁻¹ • (X + Xᴴ)

/-- The response coefficient F_i in equation (A4). -/
def response (η : ℝ) (G : Matrix n m ℂ)
    (A_i : Matrix m n ℂ) (K_i : Matrix n n ℂ) : Matrix m m ℂ :=
  (η⁻¹ * (2 : ℝ)⁻¹) •
    (Gᴴ * A_iᴴ + A_i * G - Gᴴ * K_i * G)

/-- Its product-rule variation; A_ij and K_ij are the genuine mixed jets
    supplied by the separate calculus theorem. -/
def variation (η : ℝ) (G G_j : Matrix n m ℂ)
    (A_i A_ij : Matrix m n ℂ) (K_i K_ij : Matrix n n ℂ) : Matrix m m ℂ :=
  (η⁻¹ * (2 : ℝ)⁻¹) •
    (G_jᴴ * A_iᴴ + Gᴴ * A_ijᴴ + A_ij * G + A_i * G_j -
      G_jᴴ * K_i * G - Gᴴ * K_ij * G - Gᴴ * K_i * G_j)

/-- The second mixed jets cancel in the antisymmetric derivative.
    Symmetry of K_i and K_j follows from differentiating Aᴴ A. -/
theorem mixed_jets_cancel
    (η : ℝ) (G G_i G_j : Matrix n m ℂ)
    (A_i A_j A_ij : Matrix m n ℂ) (K_i K_j K_ij : Matrix n n ℂ)
    (hKi : K_iᴴ = K_i) (hKj : K_jᴴ = K_j) :
    variation η G G_i A_j A_ij K_j K_ij -
        variation η G G_j A_i A_ij K_i K_ij =
      η⁻¹ • herm (G_iᴴ * (A_jᴴ - K_j * G) -
        G_jᴴ * (A_iᴴ - K_i * G)) := by
  simp only [variation, herm, smul_smul, ← smul_sub]
  congr 1
  simp only [conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, hKi, hKj, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem herm_real_smul (r : ℝ) (X : Matrix m m ℂ) :
    herm (r • X) = r • herm X := by
  simp only [herm, conjTranspose_smul, star_trivial, ← smul_add, smul_smul]
  rw [mul_comm]

theorem herm_commutator (R : Matrix n n ℂ) (G_i G_j : Matrix n m ℂ) :
    herm (G_iᴴ * (R * G_j) - G_jᴴ * (R * G_i)) =
      (2 : ℝ)⁻¹ •
        (G_iᴴ * (R - Rᴴ) * G_j - G_jᴴ * (R - Rᴴ) * G_i) := by
  unfold herm
  congr 1
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- The derivatives of Aᴴ A are Hermitian without any eigenvalue choices. -/
theorem gram_jet_hermitian (A A_i : Matrix m n ℂ) :
    (A_iᴴ * A + Aᴴ * A_i)ᴴ = A_iᴴ * A + Aᴴ * A_i := by
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose]
  abel

/-- Skew part of a resolvent denominator z I + η K. -/
theorem resolvent_skew (z : ℂ) (η : ℝ) (K : Matrix n n ℂ)
    (hK : Kᴴ = K) :
    (z • (1 : Matrix n n ℂ) + η • K) -
        (z • (1 : Matrix n n ℂ) + η • K)ᴴ =
      (z - star z) • (1 : Matrix n n ℂ) := by
  simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one,
    star_trivial, hK, sub_smul]
  abel

/-- Convert the linearized transfer equation into the E_i representation. -/
theorem transfer_jet_solve (η : ℝ) (hη : η ≠ 0)
    (R : Matrix n n ℂ) (G_i E_i : Matrix n m ℂ)
    (h : R * G_i = η • E_i) :
    E_i = η⁻¹ • (R * G_i) := by
  rw [h, smul_smul, inv_mul_cancel₀ hη, one_smul]

/-- Antisymmetrization exposes R - Rᴴ. This retains rectangular dimensions. -/
theorem herm_transfer
    (η : ℝ) (hη : η ≠ 0) (R : Matrix n n ℂ)
    (G_i G_j E_i E_j : Matrix n m ℂ)
    (hi : R * G_i = η • E_i) (hj : R * G_j = η • E_j) :
    η⁻¹ • herm (G_iᴴ * E_j - G_jᴴ * E_i) =
      (η⁻¹ * η⁻¹ * (2 : ℝ)⁻¹) •
        (G_iᴴ * (R - Rᴴ) * G_j - G_jᴴ * (R - Rᴴ) * G_i) := by
  rw [transfer_jet_solve η hη R G_i E_i hi,
      transfer_jet_solve η hη R G_j E_j hj]
  simp only [Matrix.mul_smul, ← smul_sub, herm_real_smul, herm_commutator,
    smul_smul, mul_assoc]

/-- Substitute the imaginary scalar skew part into the curvature kernel. -/
theorem curvature_kernel
    (η : ℝ) (hη : η ≠ 0) (c : ℂ) (R : Matrix n n ℂ)
    (G_i G_j E_i E_j : Matrix n m ℂ)
    (hi : R * G_i = η • E_i) (hj : R * G_j = η • E_j)
    (hR : R - Rᴴ = (2 : ℝ) • (c • (1 : Matrix n n ℂ))) :
    η⁻¹ • herm (G_iᴴ * E_j - G_jᴴ * E_i) =
      (η ^ 2)⁻¹ • (c • (G_iᴴ * G_j - G_jᴴ * G_i)) := by
  rw [herm_transfer η hη R G_i G_j E_i E_j hi hj, hR]
  have hmul (X Y : Matrix n m ℂ) :
      Xᴴ * ((2 : ℝ) • (c • (1 : Matrix n n ℂ))) * Y =
        (2 : ℝ) • (c • (Xᴴ * Y)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hmul, hmul, ← smul_sub, ← smul_sub, smul_smul]
  have hc : η⁻¹ * η⁻¹ * (2 : ℝ)⁻¹ * 2 = (η ^ 2)⁻¹ := by
    simp only [inv_pow, pow_two]
    ring
  rw [hc]

/-- Complete algebraic jet form of equation (10), with all mixed second
    jets cancelled and the two first transfer equations used explicitly. -/
theorem local_curvature_jet
    (η : ℝ) (hη : η ≠ 0) (c : ℂ) (R : Matrix n n ℂ)
    (G G_i G_j : Matrix n m ℂ)
    (A_i A_j A_ij : Matrix m n ℂ) (K_i K_j K_ij : Matrix n n ℂ)
    (hKi : K_iᴴ = K_i) (hKj : K_jᴴ = K_j)
    (hi : R * G_i = η • (A_iᴴ - K_i * G))
    (hj : R * G_j = η • (A_jᴴ - K_j * G))
    (hR : R - Rᴴ = (2 : ℝ) • (c • (1 : Matrix n n ℂ))) :
    variation η G G_i A_j A_ij K_j K_ij -
        variation η G G_j A_i A_ij K_i K_ij =
      (η ^ 2)⁻¹ • (c • (G_iᴴ * G_j - G_jᴴ * G_i)) := by
  rw [mixed_jets_cancel η G G_i G_j A_i A_j A_ij K_i K_j K_ij hKi hKj]
  exact curvature_kernel η hη c R G_i G_j _ _ hi hj hR

end Curvature
end NoiseResponse

#print axioms NoiseResponse.Curvature.mixed_jets_cancel
#print axioms NoiseResponse.Curvature.gram_jet_hermitian
#print axioms NoiseResponse.Curvature.resolvent_skew
#print axioms NoiseResponse.Curvature.herm_transfer
#print axioms NoiseResponse.Curvature.curvature_kernel
#print axioms NoiseResponse.Curvature.local_curvature_jet
