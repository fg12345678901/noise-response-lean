/- Added by cx on 2026-10-29: exact transfer, Moore--Penrose and
   local uniform-gap identities for the manuscript geometry interface. -/
module

public import NoiseResponse.GlobalResidualPotential
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2200
set_option maxHeartbeats 8000000
noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator
namespace NoiseResponse.RankSafe
open NoiseResponse.IsotropicSpectrum
variable {m n : Type*} [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n] [Nonempty n]

theorem transfer_normal_range (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ)
    (hb : ‖normalFilter η A P‖<1) (z : ℂ) (hz : ‖z‖=1) :
    P*transfer η A P z=transfer η A P z := by
  have hPB : P*normalFilter η A P=normalFilter η A P := by
    simp only [normalFilter,Matrix.mul_sub,Matrix.mul_smul,← Matrix.mul_assoc,hPP,hPA]
  have hBP : normalFilter η A P*P=normalFilter η A P := by
    simp only [normalFilter,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_assoc,hPP,hAP]
  have hc : (1-star z • normalFilter η A P)*P=P*(1-star z • normalFilter η A P) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hPB,hBP]
  have he : (1-star z • normalFilter η A P)*(P*transfer η A P z)=η • (star z • Aᴴ) := by
    rw [← Matrix.mul_assoc,hc,Matrix.mul_assoc,transfer_equation η A P hb z hz,
      Matrix.mul_smul,Matrix.mul_smul,hPA]
  exact (transfer_unique η A P hb z hz (P*transfer η A P z) he).symm

theorem transfer_original_equation (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hb : ‖normalFilter η A P‖<1) (z : ℂ) (hz : ‖z‖=1) :
    (z • (1 : Matrix n n ℂ)-normalFilter η A P)*transfer η A P z=η • Aᴴ := by
  have hzz : z*star z=1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hh := congrArg (fun D : Matrix n m ℂ => z • D) (transfer_equation η A P hb z hz)
  simpa only [← Matrix.smul_mul,smul_sub,smul_smul,hzz,one_smul,
    smul_comm z η] using! hh

/-- All four Moore--Penrose equations for the actual zero-frequency
    transfer, including rank-deficient and rectangular residual Jacobians. -/
theorem zero_transfer_penrose (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hPH : Pᴴ=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ)
    (hb : ‖normalFilter η A P‖<1) :
    A*transfer η A P 1*A=A ∧
      transfer η A P 1*A*transfer η A P 1=transfer η A P 1 ∧
      (A*transfer η A P 1)ᴴ=A*transfer η A P 1 ∧
      (transfer η A P 1*A)ᴴ=transfer η A P 1*A := by
  have hGA := zero_transfer_right η A P hPP hAP hPA hb
  refine ⟨?_,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,hGA,hAP]
  · rw [hGA]
    exact transfer_normal_range η A P hPP hAP hPA hb 1 (by simp)
  · exact (zero_output_projector η A P hPP hPH hAP hPA hb).1
  · rw [hGA,hPH]

end NoiseResponse.RankSafe

namespace NoiseResponse.ResidualGeometry
open NoiseResponse.Sufficiency NoiseResponse.Geometry NoiseResponse.RankSafe
variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise stability used by the local-germ formulation gives
    the manuscript's uniform normal margin on an actual open neighborhood. -/
theorem admissible_uniform_margin (η : ℝ) (f : (n → ℝ) → (m → ℝ))
    (ι : E → (n → ℝ)) (x : E) (hgood : AdmissibleAt η f ι x) :
    ∃ (U : Set E) (q : ℝ), IsOpen U ∧ x ∈ U ∧ 0≤q ∧ q<1 ∧
      ∀ y ∈ U, ‖normalFilter η (complexify (jacobian f ι y))
        (normalProjector (jacobian f ι y))‖≤q := by
  let A := jacobian f ι
  have hg := admissible_jacobian η f ι x hgood
  have hAc := complexify_contDiffAt A x hg.1
  have hP := normalProjector_contDiffAt A x hg.1 hg.2.1
  have hc := (normalFilter_contDiffAt η _ _ x hAc hP).continuousAt.norm
  let q := (‖normalFilter η (complexify (A x)) (normalProjector (A x))‖+1)/2
  have hq0 : 0≤q := by dsimp only [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; linarith [hg.2.2]
  have hlt : ‖normalFilter η (complexify (A x)) (normalProjector (A x))‖<q := by
    dsimp only [q]; linarith [hg.2.2]
  have hn := hc.eventually_lt_const hlt
  obtain ⟨U,hsub,hU,hUx⟩ := mem_nhds_iff.mp hn
  exact ⟨U,q,hU,hUx,hq0,hq1,fun y hy => (hsub hy).le⟩

end NoiseResponse.ResidualGeometry
