/- Added by cx on 2026-10-29: the general rank-one moment response
   pulled back by an actual affine flat residual equals the audited
   pair response. This transports real local potentials, not curl hypotheses. -/
module

public import NoiseResponse.AffineFlatGeometry
public import Mathlib.Tactic

@[expose] public section
set_option maxRecDepth 1200
set_option maxHeartbeats 4000000
noncomputable section
open Filter Set Matrix
open scoped Topology Matrix.Norms.Elementwise
attribute [local instance] matrixNormTopology
namespace NoiseResponse.Classification
variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
variable {T : ℝ} [Fact (0 < T)]
namespace RealMatrixSpectrum
variable (S : RealMatrixSpectrum T m)

def rankOneK (a : ℝ) := generating S.Γ a
def rankOneC (a : ℝ) := S.Γ0+a • (S.rankOneK a+(S.rankOneK a)ᵀ)

def rankOneResponse (η : ℝ) (A : Plane → m → ℝ) (i : Fin 2) (p : Plane) : ℝ :=
  let z := A p
  let h := probe (1 : Matrix m m ℝ) z z
  let a := 1-η*h
  let zi := fderiv ℝ A p (planeAxis i)
  probe (S.rankOneK a) zi z - probe (S.rankOneC a) z z/(h*(1+a))*probe 1 zi z

def AllFlatLocalPotentials (η : ℝ) : Prop :=
  ∀ (A : Plane → m → ℝ) (p : Plane), ContDiffAt ℝ 3 A p → A p ≠ 0 →
    (1-η*probe (1 : Matrix m m ℝ) (A p) (A p)) ∈ Ioo (-1 : ℝ) 1 →
      HasLocalPlanePotential (S.rankOneResponse η A 0) (S.rankOneResponse η A 1) p

theorem rankOneC_symmetric (a : ℝ) : (S.rankOneC a)ᵀ=S.rankOneC a := by
  unfold rankOneC
  rw [Matrix.transpose_add, Matrix.transpose_smul, S.zero_symmetric,
    Matrix.transpose_add, Matrix.transpose_transpose]
  congr 1
  congr 1
  abel

theorem pair_moment_coefficients (u v : m → ℝ) (a : ℝ) (ha : ‖a‖<1) :
    (S.pair u v).k00 a=probe (S.rankOneK a) u u ∧
    (S.pair u v).sym a+(S.pair u v).skew a=probe (S.rankOneK a) u v ∧
    (S.pair u v).sym a-(S.pair u v).skew a=probe (S.rankOneK a) v u ∧
    (S.pair u v).k11 a=probe (S.rankOneK a) v v ∧
    (S.pair u v).c00 a=probe (S.rankOneC a) u u ∧
    (S.pair u v).zeroSym+2*a*(S.pair u v).sym a=probe (S.rankOneC a) u v ∧
    (S.pair u v).c11 a=probe (S.rankOneC a) v v := by
  have h00 : (S.pair u v).k00 a=probe (S.rankOneK a) u u := by
    exact generating_map S.Γ S.bound S.bounded (realProbeCLM u u) a ha
  have h11 : (S.pair u v).k11 a=probe (S.rankOneK a) v v := by
    exact generating_map S.Γ S.bound S.bounded (realProbeCLM v v) a ha
  have hs : (S.pair u v).sym a=(probe (S.rankOneK a) u v+probe (S.rankOneK a) v u)/2 := by
    have he := generating_map S.Γ S.bound S.bounded (symmetricProbeCLM u v) a ha
    change generating (fun n => symmetricProbeCLM u v (S.Γ n)) a = _
    simpa only [symmetricProbeCLM_apply, rankOneK] using he
  have ht : (S.pair u v).skew a=(probe (S.rankOneK a) u v-probe (S.rankOneK a) v u)/2 := by
    have he := generating_map S.Γ S.bound S.bounded (skewProbeCLM u v) a ha
    change generating (fun n => skewProbeCLM u v (S.Γ n)) a = _
    simpa only [skewProbeCLM_apply, rankOneK] using he
  have hz : (S.pair u v).zeroSym=probe S.Γ0 u v := by
    change symmetricProbeCLM u v S.Γ0=probe S.Γ0 u v
    rw [symmetricProbeCLM_apply, probe_symmetric _ S.zero_symmetric]
    ring
  refine ⟨h00, ?_, ?_, h11, ?_, ?_, ?_⟩
  · rw [hs, ht]; ring
  · rw [hs, ht]; ring
  · change (S.pair u v).zero00+2*a*(S.pair u v).k00 a= _
    rw [h00]
    change probe S.Γ0 u u+2*a*probe (S.rankOneK a) u u= _
    simp only [rankOneC, probe_matrix_add, probe_matrix_smul, probe_transpose]
    ring
  · rw [hz, hs]
    simp only [rankOneC, probe_matrix_add, probe_matrix_smul, probe_transpose]
    ring
  · change (S.pair u v).zero11+2*a*(S.pair u v).k11 a= _
    rw [h11]
    change probe S.Γ0 v v+2*a*probe (S.rankOneK a) v v= _
    simp only [rankOneC, probe_matrix_add, probe_matrix_smul, probe_transpose]
    ring

theorem affine_response_eq_pair (η : ℝ) (u v : m → ℝ) (huv : OrthonormalProbePair u v)
    (p : Plane) (ha : pairA η p ∈ Ioo (-1 : ℝ) 1) :
    S.rankOneResponse η (probeEmbedding u v) 0 p=
      pairAlpha0 (S.pair u v).k00 (fun a => (S.pair u v).sym a+(S.pair u v).skew a)
        (S.pair u v).c00 (fun a => (S.pair u v).zeroSym+2*a*(S.pair u v).sym a)
        (S.pair u v).c11 η p ∧
    S.rankOneResponse η (probeEmbedding u v) 1 p=
      pairAlpha1 (fun a => (S.pair u v).sym a-(S.pair u v).skew a) (S.pair u v).k11
        (S.pair u v).c00 (fun a => (S.pair u v).zeroSym+2*a*(S.pair u v).sym a)
        (S.pair u v).c11 η p := by
  have hnorm : ‖pairA η p‖<1 := by simpa only [Real.norm_eq_abs] using abs_lt.mpr ha
  obtain ⟨h00,h01,h10,h11,hc00,hc01,hc11⟩ := S.pair_moment_coefficients u v _ hnorm
  have hd0 : fderiv ℝ (probeEmbedding u v) p (planeAxis 0)=u := by
    rw [show probeEmbedding u v=fun x => probeEmbeddingCLM u v x by rfl,
      (probeEmbeddingCLM u v).hasFDerivAt.fderiv]
    ext i
    simp [probeEmbeddingCLM_apply, probeEmbedding, planeAxis]
  have hd1 : fderiv ℝ (probeEmbedding u v) p (planeAxis 1)=v := by
    rw [show probeEmbedding u v=fun x => probeEmbeddingCLM u v x by rfl,
      (probeEmbeddingCLM u v).hasFDerivAt.fderiv]
    ext i
    simp [probeEmbeddingCLM_apply, probeEmbedding, planeAxis]
  have hvu : probe (1 : Matrix m m ℝ) v u=0 := by
    rw [← probe_transpose, Matrix.transpose_one]; exact huv.2.2
  have hcvu : probe (S.rankOneC (pairA η p)) v u=probe (S.rankOneC (pairA η p)) u v :=
    probe_symmetric _ (S.rankOneC_symmetric _) v u
  have hpa : 1-η*((p 0)^2+(p 1)^2)=pairA η p := rfl
  constructor
  all_goals
    dsimp only [rankOneResponse]
    rw [probeEmbedding_length u v huv]
    simp only [hpa, hd0, hd1, probeEmbedding, pairAlpha0, pairAlpha1, pairPhi,
      h00, h01, h10, h11, hc00, hc01, hc11,
      probe_add_left, probe_add_right, probe_smul_left, probe_smul_right,
      huv.1, huv.2.1, huv.2.2, hvu, hcvu]
    ring

theorem all_flat_implies_rank_one (η : ℝ) (hp : S.AllFlatLocalPotentials η) :
    S.AllRankOnePotentials η := by
  intro u v huv r hr ha p hpr
  have hstable : pairA η p ∈ Ioo (-1 : ℝ) 1 := by
    rcases hpr with hp | hp
    · rw [hp]; simpa [pairA] using ha
    · rw [Set.mem_singleton_iff.mp hp]; simpa [pairA] using ha
  have hlocal := hp (probeEmbedding u v) p
    ((probeEmbedding_smooth u v).of_le (by norm_num)).contDiffAt
    (probeEmbedding_axis_nonzero u v huv r hr p hpr)
    (by simpa only [probeEmbedding_length u v huv, pairA] using hstable)
  obtain ⟨V,hV,hgrad⟩ := hlocal
  refine ⟨V,hV,?_⟩
  have hopen : {x : Plane | pairA η x ∈ Ioo (-1 : ℝ) 1} ∈ 𝓝 p := by
    apply (show Continuous (pairA η) by unfold pairA; fun_prop).continuousAt.preimage_mem_nhds
    exact isOpen_Ioo.mem_nhds hstable
  filter_upwards [hgrad, hopen] with x hx hs
  have he := S.affine_response_eq_pair η u v huv x hs
  exact ⟨hx.1.trans he.1, hx.2.trans he.2⟩

end RealMatrixSpectrum
end NoiseResponse.Classification

#print axioms NoiseResponse.Classification.RealMatrixSpectrum.all_flat_implies_rank_one
