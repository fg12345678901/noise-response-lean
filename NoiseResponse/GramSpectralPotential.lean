/- Added by cx on 2026-10-29: the constructed isotropic trace primitive
   equals the manuscript's sum over positive Gram eigenvalues. Zero
   modes are removed explicitly; no eigenvalue differentiability is used. -/
module

public import NoiseResponse.Theorem3
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 2300
set_option maxHeartbeats 9000000
noncomputable section
open Matrix Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator ComplexOrder
namespace NoiseResponse.ManuscriptPotential
open NoiseResponse.IsotropicSpectrum NoiseResponse.RankSafe
variable {Ω m n : Type*} [MeasurableSpace Ω]
variable [Fintype m] [DecidableEq m] [Nonempty m]
variable [Fintype n] [DecidableEq n] [Nonempty n]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) where
  norm_smul_le := norm_smul_le

def normalEigenvalue (η h : ℝ) : ℝ := if h=0 then 0 else 1-η*h

theorem normal_projector_eigenvector (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) (i : n) :
    P*ᵥ⇑((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i)=
      if (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i=0 then 0 else
        ⇑((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i) := by
  let hK := Matrix.isHermitian_conjTranspose_mul_self A
  let w : n → ℂ := ⇑(hK.eigenvectorBasis i)
  have he := hK.mulVec_eigenvectorBasis i
  by_cases hz : hK.eigenvalues i=0
  · simp only [hz,if_pos] at he ⊢
    have hAw : A*ᵥw=0 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero A w).mp
      (by simpa only [hz,zero_smul] using he)
    rw [← zero_transfer_right η A P hPP hAP hPA hb,← Matrix.mulVec_mulVec,hAw,Matrix.mulVec_zero]
  · simp only [hz,if_false]
    have hPK : P*(Aᴴ*A)=Aᴴ*A := by rw [← Matrix.mul_assoc,hPA]
    have hh := congrArg (fun D : Matrix n n ℂ => D*ᵥw) hPK
    rw [← Matrix.mulVec_mulVec,he,Matrix.mulVec_smul] at hh
    have hc := congrArg (fun v : n → ℂ => (hK.eigenvalues i)⁻¹ • v) hh
    simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul] using! hc

theorem normal_filter_eigenvector (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) (i : n) :
    normalFilter η A P*ᵥ⇑((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i)=
      normalEigenvalue η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) •
        ⇑((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i) := by
  rw [normalFilter,Matrix.sub_mulVec,Matrix.smul_mulVec,
    normal_projector_eigenvector η A P hPP hAP hPA hb i,
    (Matrix.isHermitian_conjTranspose_mul_self A).mulVec_eigenvectorBasis i]
  unfold normalEigenvalue
  split_ifs with hz
  · simp only [hz,zero_smul,smul_zero,sub_zero]
  · simp only [sub_smul,one_smul,smul_smul]

theorem normal_filter_diagonal (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) :
    normalFilter η A P=Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
      (Matrix.diagonal (fun i => (normalEigenvalue η
        ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) : ℂ))) := by
  let hK := Matrix.isHermitian_conjTranspose_mul_self A
  let U := hK.eigenvectorUnitary
  let β : n → ℂ := fun i => normalEigenvalue η (hK.eigenvalues i)
  have he : normalFilter η A P*(U : Matrix n n ℂ)=(U : Matrix n n ℂ)*Matrix.diagonal β := by
    ext i j
    change ((normalFilter η A P*(U : Matrix n n ℂ)).col j) i= _
    rw [Matrix.col_mul_eq_mulVec_col]
    change (normalFilter η A P*ᵥ⇑(hK.eigenvectorBasis j)) i=_
    rw [normal_filter_eigenvector η A P hPP hAP hPA hb j]
    simp only [Matrix.mul_diagonal,Pi.smul_apply,Complex.real_smul,U,β,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
    ring
  have hh := congrArg (fun D : Matrix n n ℂ => D*(star U : Matrix n n ℂ)) he
  simpa only [← Unitary.coe_star,Matrix.mul_assoc,Unitary.coe_mul_star_self,Matrix.mul_one,
    Unitary.conjStarAlgAut_apply,U,β] using! hh

theorem normal_eigenvalue_bound (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) (i : n) :
    ‖normalEigenvalue η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)‖ ≤
      ‖normalFilter η A P‖ := by
  have hn : ‖normalFilter η A P‖=‖Matrix.diagonal (fun j =>
      (normalEigenvalue η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) : ℂ))‖ := by
    rw [normal_filter_diagonal η A P hPP hAP hPA hb,Unitary.conjStarAlgAut_apply,← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  rw [hn,Matrix.l2_opNorm_diagonal]
  simpa only [Complex.norm_real] using
    norm_le_pi_norm (fun j => (normalEigenvalue η
      ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) : ℂ)) i

theorem normal_filter_trace_power (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) (k : ℕ) :
    (normalFilter η A P^k).trace=∑ i,
      (normalEigenvalue η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) : ℂ)^k := by
  conv_lhs => rw [normal_filter_diagonal η A P hPP hAP hPA hb,← map_pow,
    Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul]
  simp [Matrix.diagonal_pow]

theorem normal_primitive_eigenvalues (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ w, ‖z w‖=1) (η : ℝ) (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) :
    NoiseResponse.TraceSeries.tracePrimitive matrixTrace (spectralCoeff ν z) (normalFilter η A P)=
      ∑ i, scalarPrimitive ν z (normalEigenvalue η
        ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) := by
  let q := (‖normalFilter η A P‖+1)/2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q<1 := by dsimp only [q]; linarith
  have hBq : ‖normalFilter η A P‖<q := by dsimp only [q]; linarith
  have hs (i : n) := NoiseResponse.TraceSeries.primitiveTerm_summable
    (ContinuousLinearMap.id ℝ ℝ) (spectralCoeff ν z)
    (normalEigenvalue η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) q hq0
      ((normal_eigenvalue_bound η A P hPP hAP hPA hb i).trans hBq.le)
      (spectralCoeff_summable ν z hu q hq0 hq1)
  change (∑' k, spectralCoeff ν z k/(k+1 : ℝ)*matrixTrace (normalFilter η A P^(k+1)))=
    ∑ i, ∑' k, spectralCoeff ν z k/(k+1 : ℝ)*
      (normalEigenvalue η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i))^(k+1)
  simp only [matrixTrace_apply,normal_filter_trace_power η A P hPP hAP hPA hb,map_sum,
    ← Complex.ofReal_pow,Complex.ofReal_re,Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => hs i)

theorem scalarPrimitive_zero (ν : Measure Ω) (z : Ω → ℂ) : scalarPrimitive ν z 0=0 := by
  simp [scalarPrimitive,NoiseResponse.TraceSeries.tracePrimitive,NoiseResponse.TraceSeries.primitiveTerm]

theorem isotropic_positive_input_formula (ν : Measure Ω) [IsFiniteMeasure ν]
    (z : Ω → ℂ) (hu : ∀ w, ‖z w‖=1) (η : ℝ) (hη : η ≠ 0)
    (A : Matrix m n ℂ) (P : Matrix n n ℂ)
    (hPP : P*P=P) (hAP : A*P=A) (hPA : P*Aᴴ=Aᴴ) (hb : ‖normalFilter η A P‖<1) :
    -(2*η)⁻¹*NoiseResponse.TraceSeries.tracePrimitive matrixTrace (spectralCoeff ν z) (normalFilter η A P)=
      (1/2 : ℝ)*∑ i, if 0<(Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i then
        phi ν z η ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) else 0 := by
  rw [normal_primitive_eigenvalues ν z hu η A P hPP hAP hPA hb,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  by_cases hpos : 0<(Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i
  · rw [if_pos hpos,normalEigenvalue,if_neg (ne_of_gt hpos),phi]
    field_simp
    <;> ring
  · have hz : (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i=0 := le_antisymm (le_of_not_gt hpos) hn
    simp [normalEigenvalue,hz,scalarPrimitive_zero]

end NoiseResponse.ManuscriptPotential
