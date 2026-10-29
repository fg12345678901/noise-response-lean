/- Added by cx on 2026-10-29: the local curvature pilot, with actual
   real derivatives. No mixed-jet cancellation is assumed as a hypothesis. -/
module

public import NoiseResponse.CurvatureAlgebra
public import NoiseResponse.MatrixCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Filter
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology

namespace NoiseResponse.Curvature
open MatrixCalculus
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Actual product rule for the coefficient F_i in (A4). -/
theorem response_hasDerivAt
    (η : ℝ) {G : ℝ → Matrix n m ℂ} {Ai : ℝ → Matrix m n ℂ}
    {Ki : ℝ → Matrix n n ℂ} {x : ℝ}
    {Gj : Matrix n m ℂ} {Aij : Matrix m n ℂ} {Kij : Matrix n n ℂ}
    (hG : HasDerivAt G Gj x) (hA : HasDerivAt Ai Aij x)
    (hK : HasDerivAt Ki Kij x) :
    HasDerivAt (fun t => response η (G t) (Ai t) (Ki t))
      (variation η (G x) Gj (Ai x) Aij (Ki x) Kij) x := by
  have h1 := hasDerivAt_mul (hasDerivAt_adj hG) (hasDerivAt_adj hA)
  have h2 := hasDerivAt_mul hA hG
  have h3 := hasDerivAt_mul (hasDerivAt_mul (hasDerivAt_adj hG) hK) hG
  have h := ((h1.fun_add h2).fun_sub h3).const_smul (η⁻¹ * (2 : ℝ)⁻¹)
  convert h using 1
  · rfl
  · unfold variation
    congr 1
    simp only [Matrix.add_mul]
    abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coefficient (η : ℝ) (A : E → Matrix m n ℂ)
    (K : E → Matrix n n ℂ) (G : E → Matrix n m ℂ) (v x : E) :=
  response η (G x) (fderiv ℝ A x v) (fderiv ℝ K x v)

theorem fderiv_line_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x+t • u) v)
      (fderiv ℝ (fderiv ℝ f) x u v) 0 := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have he := (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hdf.hasFDerivAt
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using he.differentiableAt
  have hline := hasDerivAt_line hd u
  have hval : fderiv ℝ (fun y => fderiv ℝ f y v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
    have h := congrArg (fun L : E →L[ℝ] F => L u) he.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply] using h
  simpa only [hval] using hline

/-- Differentiate the implicit transfer equation; no inverse derivative
    or preassigned first transfer jet is assumed. -/
theorem transfer_differentiated
    (η : ℝ) (z : ℂ) (A : E → Matrix m n ℂ) (K : E → Matrix n n ℂ)
    (G : E → Matrix n m ℂ) {x : E}
    (hA : DifferentiableAt ℝ A x) (hK : DifferentiableAt ℝ K x)
    (hG : DifferentiableAt ℝ G x)
    (hRG : ∀ᶠ y in 𝓝 x, (z • (1 : Matrix n n ℂ) + η • K y) * G y = η • (A y)ᴴ)
    (v : E) :
    (z • (1 : Matrix n n ℂ) + η • K x) * (fderiv ℝ G x v) =
      η • ((fderiv ℝ A x v)ᴴ - fderiv ℝ K x v * G x) := by
  have hKl := hasDerivAt_line hK v
  have hGl := hasDerivAt_line hG v
  have hAl := hasDerivAt_line hA v
  have hR := (hKl.const_smul η).const_add (z • (1 : Matrix n n ℂ))
  have hleft := hasDerivAt_mul hR hGl
  have hright := (hasDerivAt_adj hAl).const_smul η
  have hline : ∀ᶠ t : ℝ in 𝓝 0,
      (z • (1 : Matrix n n ℂ) + η • K (x+t • v)) * G (x+t • v) =
        η • (A (x+t • v))ᴴ := by
    have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    exact ht hRG
  have he := hleft.unique (hright.congr_of_eventuallyEq hline)
  simp only [Pi.smul_apply, zero_smul, add_zero, Matrix.smul_mul] at he
  rw [smul_sub]
  exact eq_sub_of_add_eq (by simpa only [add_comm] using he)

/-- Local matrix curvature from genuine C2 coefficient functions and a
    differentiable implicit transfer. The paper's resolvent is one such
    transfer. C2 supplies mixed-derivative symmetry inside this proof. -/
theorem local_curvature
    (η : ℝ) (hη : η ≠ 0) (c z : ℂ)
    (A : E → Matrix m n ℂ) (K : E → Matrix n n ℂ)
    (G : E → Matrix n m ℂ) {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hK : ContDiffAt ℝ 2 K x)
    (hG : DifferentiableAt ℝ G x)
    (hgram : ∀ᶠ y in 𝓝 x, K y = (A y)ᴴ * A y)
    (hRG : ∀ᶠ y in 𝓝 x, (z • (1 : Matrix n n ℂ) + η • K y) * G y = η • (A y)ᴴ)
    (hz : z - star z = (2 : ℝ) • c) (u v : E) :
    deriv (fun t : ℝ => coefficient η A K G v (x+t • u)) 0 -
      deriv (fun t : ℝ => coefficient η A K G u (x+t • v)) 0 =
        (η^2)⁻¹ • (c • ((fderiv ℝ G x u)ᴴ * (fderiv ℝ G x v) -
          (fderiv ℝ G x v)ᴴ * (fderiv ℝ G x u))) := by
  have hAd := hA.differentiableAt (by norm_num)
  have hKd := hK.differentiableAt (by norm_num)
  have hgg : K =ᶠ[𝓝 x] (fun y => (A y)ᴴ * A y) := hgram
  have hc (i j : E) := response_hasDerivAt η (hasDerivAt_line hG i)
    (fderiv_line_hasDerivAt hA i j) (fderiv_line_hasDerivAt hK i j)
  have hAi := hA.isSymmSndFDerivAt (by simp)
  have hKi := hK.isSymmSndFDerivAt (by simp)
  have hgramD (w : E) : fderiv ℝ K x w =
      (fderiv ℝ A x w)ᴴ * A x + (A x)ᴴ * fderiv ℝ A x w := by
    have heq := hgg.fderiv_eq (𝕜 := ℝ)
    rw [heq]
    have haH : HasFDerivAt (fun y => (A y)ᴴ)
        (adjCLM.comp (fderiv ℝ A x)) x := by
      simpa only [Function.comp_def, adjCLM_apply] using
        adjCLM.hasFDerivAt.comp x hAd.hasFDerivAt
    rw [fderiv_mul_apply haH.differentiableAt hAd w, haH.fderiv]
    rfl
  have hh (w : E) : (fderiv ℝ K x w)ᴴ = fderiv ℝ K x w := by
    rw [hgramD]
    exact gram_jet_hermitian _ _
  have hKx : (K x)ᴴ = K x := by
    rw [hgg.self_of_nhds]
    simp
  have hR : (z • (1 : Matrix n n ℂ) + η • K x) -
      (z • (1 : Matrix n n ℂ) + η • K x)ᴴ =
      (2 : ℝ) • (c • (1 : Matrix n n ℂ)) := by
    rw [resolvent_skew z η (K x) hKx, hz, smul_assoc]
  have hd (i j : E) :
      deriv (fun t : ℝ => coefficient η A K G j (x+t • i)) 0 =
        variation η (G x) (fderiv ℝ G x i) (fderiv ℝ A x j)
          (fderiv ℝ (fderiv ℝ A) x i j) (fderiv ℝ K x j)
          (fderiv ℝ (fderiv ℝ K) x i j) := by
    simpa only [coefficient, zero_smul, add_zero] using (hc i j).deriv
  rw [hd u v, hd v u, hAi v u, hKi v u]
  exact local_curvature_jet η hη c _ _ _ _ _ _ _ _ _ _ (hh u) (hh v)
    (transfer_differentiated η z A K G hAd hKd hG hRG u)
    (transfer_differentiated η z A K G hAd hKd hG hRG v) hR

/-- The real/imaginary decomposition of exp(i omega)-1 supplies the sine
    coefficient, including both zero-sine endpoints. -/
theorem frequency_skew (ω : ℝ) :
    ((Real.cos ω - 1 : ℝ) + (Real.sin ω : ℂ) * Complex.I) -
      star ((Real.cos ω - 1 : ℝ) + (Real.sin ω : ℂ) * Complex.I) =
        (2 : ℝ) • ((Real.sin ω : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im] <;> ring

def frequencyZ (ω : ℝ) : ℂ := Complex.exp ((ω : ℂ)*Complex.I)-1

theorem frequencyZ_skew (ω : ℝ) :
    frequencyZ ω - star (frequencyZ ω) =
      (2 : ℝ) • (Complex.I*(Real.sin ω : ℂ)) := by
  unfold frequencyZ
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;> simp <;> ring

/-- The pilot's exported formula uses exactly exp(i omega)-1 and
    i sin(omega)/eta^2 from the manuscript, with genuine derivatives. -/
theorem frequency_curvature
    (η : ℝ) (hη : η ≠ 0) (ω : ℝ)
    (A : E → Matrix m n ℂ) (K : E → Matrix n n ℂ)
    (G : E → Matrix n m ℂ) {x : E}
    (hA : ContDiffAt ℝ 2 A x) (hK : ContDiffAt ℝ 2 K x)
    (hG : DifferentiableAt ℝ G x)
    (hgram : ∀ᶠ y in 𝓝 x, K y = (A y)ᴴ * A y)
    (hRG : ∀ᶠ y in 𝓝 x,
      (frequencyZ ω • (1 : Matrix n n ℂ) + η • K y) * G y = η • (A y)ᴴ)
    (u v : E) :
    deriv (fun t : ℝ => coefficient η A K G v (x+t • u)) 0 -
      deriv (fun t : ℝ => coefficient η A K G u (x+t • v)) 0 =
        (η^2)⁻¹ • ((Complex.I*(Real.sin ω : ℂ)) •
          ((fderiv ℝ G x u)ᴴ * (fderiv ℝ G x v) -
            (fderiv ℝ G x v)ᴴ * (fderiv ℝ G x u))) :=
  local_curvature η hη _ _ A K G hA hK hG hgram hRG (frequencyZ_skew ω) u v

end NoiseResponse.Curvature

#print axioms NoiseResponse.Curvature.response_hasDerivAt
#print axioms NoiseResponse.Curvature.transfer_differentiated
#print axioms NoiseResponse.Curvature.local_curvature
#print axioms NoiseResponse.Curvature.frequency_curvature
