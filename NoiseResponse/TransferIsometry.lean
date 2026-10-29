/- Added by cx on 2026-10-29: actual rank-safe transfers and response
   coefficients respect a fixed isometric inclusion of parameter coordinates. -/
module

public import NoiseResponse.RankSafeTransfer
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2000
set_option maxHeartbeats 7000000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace NoiseResponse.RankSafe
open NoiseResponse.IsotropicSpectrum
variable {m n N : Type*} [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable [Fintype N] [DecidableEq N] [Nonempty N]

theorem transfer_equation (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hb : ‖normalFilter η A P‖<1) (z : ℂ) (hz : ‖z‖=1) :
    (1-star z • normalFilter η A P)*transfer η A P z=η • (star z • Aᴴ) := by
  have hh := congrArg (fun D : Matrix n n ℂ => η • (star z • (D*Aᴴ)))
    (matrixResolvent_inverse (normalFilter η A P) hb (star z)
      (by simpa only [norm_star] using hz)).1
  simpa only [transfer,Matrix.mul_smul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc] using! hh

theorem transfer_unique (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hb : ‖normalFilter η A P‖<1) (z : ℂ) (hz : ‖z‖=1) (G : Matrix n m ℂ)
    (hG : (1-star z • normalFilter η A P)*G=η • (star z • Aᴴ)) : transfer η A P z=G := by
  let R := matrixResolvent (normalFilter η A P) (star z)
  calc
    _ = R*(η • (star z • Aᴴ)) := by simp only [transfer,R,Matrix.mul_smul,Matrix.smul_mul]
    _ = R*((1-star z • normalFilter η A P)*G) := by rw [hG]
    _ = G := by
      rw [← Matrix.mul_assoc,(matrixResolvent_inverse (normalFilter η A P) hb (star z)
        (by simpa only [norm_star] using hz)).2,Matrix.one_mul]

theorem filter_isometry_intertwines (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (Q : Matrix N n ℂ) (hQ : Qᴴ*Q=1) :
    normalFilter η (A*Qᴴ) (Q*P*Qᴴ)*Q=Q*normalFilter η A P := by
  have hc : Qᴴ*(Q*(Aᴴ*A))=Aᴴ*A := by rw [← Matrix.mul_assoc,hQ,Matrix.one_mul]
  simp only [normalFilter,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul]
  have h1 : Q*P*Qᴴ*Q=Q*P := by
    calc
      _ = Q*(P*(Qᴴ*Q)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ,Matrix.mul_one]
  have h2 : (Q*Aᴴ*(A*Qᴴ))*Q=Q*(Aᴴ*A) := by
    calc
      _ = Q*(Aᴴ*A)*(Qᴴ*Q) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ,Matrix.mul_one]
  rw [h1,h2]

theorem transfer_isometry (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (Q : Matrix N n ℂ) (hQ : Qᴴ*Q=1)
    (hb : ‖normalFilter η A P‖<1)
    (hbig : ‖normalFilter η (A*Qᴴ) (Q*P*Qᴴ)‖<1)
    (z : ℂ) (hz : ‖z‖=1) :
    transfer η (A*Qᴴ) (Q*P*Qᴴ) z=Q*transfer η A P z := by
  apply transfer_unique η (A*Qᴴ) (Q*P*Qᴴ) hbig z hz
  calc
    _ = Q*((1-star z • normalFilter η A P)*transfer η A P z) := by
      simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_sub,
        Matrix.mul_smul,← Matrix.mul_assoc,filter_isometry_intertwines η A P Q hQ]
    _ = _ := by
      rw [transfer_equation η A P hb z hz]
      simp only [Matrix.mul_smul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem response_isometry (η : ℝ) (A Ai : Matrix m n ℂ) (G : Matrix n m ℂ)
    (Q : Matrix N n ℂ) (hQ : Qᴴ*Q=1) :
    NoiseResponse.Curvature.response η (Q*G) (Ai*Qᴴ)
      ((Ai*Qᴴ)ᴴ*(A*Qᴴ)+(A*Qᴴ)ᴴ*(Ai*Qᴴ))=
      NoiseResponse.Curvature.response η G Ai (Aiᴴ*A+Aᴴ*Ai) := by
  have hc (X : Matrix n m ℂ) : Qᴴ*(Q*X)=X := by
    rw [← Matrix.mul_assoc,hQ,Matrix.one_mul]
  unfold NoiseResponse.Curvature.response
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_add,
    Matrix.add_mul,Matrix.mul_assoc,hc]

end NoiseResponse.RankSafe
