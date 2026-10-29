/- Added by cx on 2026-10-29: construct, rather than assume, bounded
   covariance-pair data and transport generating-function endpoint limits. -/
module

public import NoiseResponse.ScalarNecessity
public import NoiseResponse.MatrixCalculus
public import NoiseResponse.OrthonormalProbes
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 2000000
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem generating_map (Γ : ℕ → E) (B : ℝ) (hB : ∀ n, ‖Γ n‖ ≤ B)
    (L : E →L[ℝ] F) (a : ℝ) (ha : ‖a‖ < 1) :
    generating (fun n => L (Γ n)) a = L (generating Γ a) := by
  unfold generating
  rw [L.map_tsum (bounded_covariance_summable Γ B hB a ha)]
  simp only [map_smul]

theorem generating_endpoint_map (Γ : ℕ → E) (B : ℝ) (hB : ∀ n, ‖Γ n‖ ≤ B)
    (L : E →L[ℝ] F) (a : ℕ → ℝ) (ha : ∀ k, ‖a k‖ < 1)
    (w : ℕ → ℝ) (M : E)
    (hlim : Tendsto (fun k => w k • generating Γ (a k)) atTop (𝓝 M)) :
    Tendsto (fun k => w k • generating (fun n => L (Γ n)) (a k))
      atTop (𝓝 (L M)) := by
  have hl := L.continuous.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def, generating_map Γ B hB L _ (ha _), map_smul] using hl

def PairCovariances.fromLinearProbes
    (Γ : ℕ → E) (Γ0 : E) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ‖Γ n‖ ≤ B)
    (L00 L11 Ls Lt : E →L[ℝ] ℝ) : PairCovariances := by
  let C := ‖L00‖+‖L11‖+‖Ls‖+‖Lt‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ C) (n : ℕ) : ‖L (Γ n)‖ ≤ C*B := by
    calc
      _ ≤ ‖L‖*‖Γ n‖ := L.le_opNorm _
      _ ≤ C*B := mul_le_mul hL (hB n) (norm_nonneg _) hC
  refine
    { lag00 := fun n => L00 (Γ n)
      lag11 := fun n => L11 (Γ n)
      lagSym := fun n => Ls (Γ n)
      lagSkew := fun n => Lt (Γ n)
      zero00 := L00 Γ0
      zero11 := L11 Γ0
      zeroSym := Ls Γ0
      bound := C*B
      bounded00 := hb L00 ?_
      bounded11 := hb L11 ?_
      boundedSym := hb Ls ?_
      boundedSkew := hb Lt ?_ }
  all_goals dsimp [C]; linarith [norm_nonneg L00, norm_nonneg L11, norm_nonneg Ls, norm_nonneg Lt]

variable {m : Type*} [Fintype m] [DecidableEq m]

def realProbeCLM (u v : m → ℝ) : Matrix m m ℝ →L[ℝ] ℝ :=
  (show Matrix m m ℝ →ₗ[ℝ] ℝ from
    { toFun := fun A => probe A u v
      map_add' := by intros; exact probe_matrix_add _ _ _ _
      map_smul' := by intros; exact probe_matrix_smul _ _ _ _ }).toContinuousLinearMap

def symmetricProbeCLM (u v : m → ℝ) : Matrix m m ℝ →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (realProbeCLM u v+realProbeCLM v u)

def skewProbeCLM (u v : m → ℝ) : Matrix m m ℝ →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (realProbeCLM u v-realProbeCLM v u)

@[simp] theorem symmetricProbeCLM_apply (u v : m → ℝ) (M : Matrix m m ℝ) :
    symmetricProbeCLM u v M = (probe M u v+probe M v u)/2 := by
  simp only [symmetricProbeCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul]
  change (2 : ℝ)⁻¹*(probe M u v+probe M v u) = _
  ring

@[simp] theorem skewProbeCLM_apply (u v : m → ℝ) (M : Matrix m m ℝ) :
    skewProbeCLM u v M = (probe M u v-probe M v u)/2 := by
  simp only [skewProbeCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  change (2 : ℝ)⁻¹*(probe M u v-probe M v u) = _
  ring

def covariancePair (Γ : ℕ → Matrix m m ℝ) (Γ0 : Matrix m m ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ‖Γ n‖ ≤ B) (u v : m → ℝ) : PairCovariances :=
  PairCovariances.fromLinearProbes Γ Γ0 B hB0 hB
    (realProbeCLM u u) (realProbeCLM v v) (symmetricProbeCLM u v) (skewProbeCLM u v)

@[simp] theorem covariancePair_sym
    (Γ : ℕ → Matrix m m ℝ) (Γ0 : Matrix m m ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ‖Γ n‖ ≤ B) (u v : m → ℝ) (n : ℕ) :
    (covariancePair Γ Γ0 B hB0 hB u v).lagSym n = (probe (Γ n) u v+probe (Γ n) v u)/2 := by
  change symmetricProbeCLM u v (Γ n) = _
  simp only [symmetricProbeCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul]
  change (2 : ℝ)⁻¹*(probe (Γ n) u v+probe (Γ n) v u) = _
  ring

@[simp] theorem covariancePair_skew
    (Γ : ℕ → Matrix m m ℝ) (Γ0 : Matrix m m ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ‖Γ n‖ ≤ B) (u v : m → ℝ) (n : ℕ) :
    (covariancePair Γ Γ0 B hB0 hB u v).lagSkew n = (probe (Γ n) u v-probe (Γ n) v u)/2 := by
  change skewProbeCLM u v (Γ n) = _
  simp only [skewProbeCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  change (2 : ℝ)⁻¹*(probe (Γ n) u v-probe (Γ n) v u) = _
  ring

@[simp] theorem covariancePair_zero
    (Γ : ℕ → Matrix m m ℝ) (Γ0 : Matrix m m ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ‖Γ n‖ ≤ B) (u v : m → ℝ) :
    (covariancePair Γ Γ0 B hB0 hB u v).zeroSym = (probe Γ0 u v+probe Γ0 v u)/2 :=
  symmetricProbeCLM_apply _ _ _

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.generating_map
#print axioms NoiseResponse.Classification.generating_endpoint_map
#print axioms NoiseResponse.Classification.covariancePair_sym
#print axioms NoiseResponse.Classification.covariancePair_skew
