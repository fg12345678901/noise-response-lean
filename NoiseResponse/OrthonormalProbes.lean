/- Added by cx on 2026-10-29: reconstruct the full finite matrix from
   orthonormal two-coordinate probes. A rational 3-4-5 rotation also
   checks diagonal differences, which coordinate axes alone cannot see. -/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Tactic

@[expose] public section

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m]

def probe (M : Matrix m m ℝ) (u v : m → ℝ) : ℝ := Matrix.toBilin' M u v

@[simp] theorem probe_add_left (M : Matrix m m ℝ) (u v w : m → ℝ) :
    probe M (u+v) w = probe M u w + probe M v w := by
  unfold probe
  rw [map_add, LinearMap.add_apply]

@[simp] theorem probe_smul_left (M : Matrix m m ℝ) (c : ℝ) (u v : m → ℝ) :
    probe M (c • u) v = c * probe M u v := by
  unfold probe
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem probe_add_right (M : Matrix m m ℝ) (u v w : m → ℝ) :
    probe M u (v+w) = probe M u v + probe M u w := by
  exact map_add (Matrix.toBilin' M u) _ _

@[simp] theorem probe_smul_right (M : Matrix m m ℝ) (c : ℝ) (u v : m → ℝ) :
    probe M u (c • v) = c * probe M u v := by
  exact map_smul (Matrix.toBilin' M u) _ _

@[simp] theorem probe_neg_left (M : Matrix m m ℝ) (u v : m → ℝ) :
    probe M (-u) v = -probe M u v := by
  unfold probe
  simp only [map_neg, LinearMap.neg_apply]

@[simp] theorem probe_neg_right (M : Matrix m m ℝ) (u v : m → ℝ) :
    probe M u (-v) = -probe M u v := map_neg _ _

@[simp] theorem probe_single (M : Matrix m m ℝ) (i j : m) :
    probe M (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toBilin'_single _ _ _

@[simp] theorem probe_matrix_add (M N : Matrix m m ℝ) (u v : m → ℝ) :
    probe (M+N) u v = probe M u v + probe N u v := by
  unfold probe
  simp only [map_add, LinearMap.add_apply]

@[simp] theorem probe_matrix_sub (M N : Matrix m m ℝ) (u v : m → ℝ) :
    probe (M-N) u v = probe M u v - probe N u v := by
  unfold probe
  simp only [map_sub, LinearMap.sub_apply]

@[simp] theorem probe_matrix_smul (M : Matrix m m ℝ) (a : ℝ) (u v : m → ℝ) :
    probe (a • M) u v = a * probe M u v := by
  unfold probe
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem probe_transpose (M : Matrix m m ℝ) (u v : m → ℝ) :
    probe Mᵀ u v = probe M v u := by
  simp only [probe, Matrix.toBilin'_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem probe_symmetric (M : Matrix m m ℝ) (hM : Mᵀ = M) (u v : m → ℝ) :
    probe M u v = probe M v u := by
  rw [← hM, probe_transpose, hM]

def OrthonormalProbePair (u v : m → ℝ) : Prop :=
  probe 1 u u = 1 ∧ probe 1 v v = 1 ∧ probe 1 u v = 0

theorem scalar_of_orthonormal_probes [Nonempty m] (M : Matrix m m ℝ)
    (h : ∀ (u v : m → ℝ), OrthonormalProbePair u v → probe M u v = 0) :
    ∃ c : ℝ, M = c • (1 : Matrix m m ℝ) := by
  have hoff (i j : m) (hij : i ≠ j) : M i j = 0 := by
    have hp : OrthonormalProbePair (Pi.single i 1) (Pi.single j 1) := by
      simp [OrthonormalProbePair, hij]
    simpa using h _ _ hp
  have hdiag (i j : m) : M i i = M j j := by
    by_cases hij : i = j
    · subst j; rfl
    let u : m → ℝ := (3/5 : ℝ) • Pi.single i 1 + (4/5 : ℝ) • Pi.single j 1
    let v : m → ℝ := (-4/5 : ℝ) • Pi.single i 1 + (3/5 : ℝ) • Pi.single j 1
    have hp : OrthonormalProbePair u v := by
      norm_num [u, v, OrthonormalProbePair, probe_add_left, probe_add_right,
        probe_smul_left, probe_smul_right, probe_single, Matrix.one_apply,
        hij, Ne.symm hij]
    have he := h u v hp
    dsimp [u, v] at he
    simp only [probe_add_left, probe_add_right, probe_smul_left, probe_smul_right,
      probe_single, hoff i j hij, hoff j i (Ne.symm hij), mul_zero, add_zero, zero_add] at he
    linarith
  let k : m := Classical.arbitrary m
  refine ⟨M k k, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hdiag i k
  · simp [hij, hoff i j hij]

end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.scalar_of_orthonormal_probes
