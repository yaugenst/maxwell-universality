import Maxwell.Continuum.CornerParity
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Orthogonality and completeness of the eight transverse parity spaces. -/

noncomputable section
namespace Maxwell.Continuum.Corner

theorem sum_bool (f : Bool → ℝ) : ∑ b, f b = f false + f true := by
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [huniv]
  simp

theorem sum_parity (f : Parity → ℝ) : ∑ s, f s =
    f (false, false, false) + f (false, false, true) +
    f (false, true, false) + f (false, true, true) +
    f (true, false, false) + f (true, false, true) +
    f (true, true, false) + f (true, true, true) := by
  simp only [Fintype.sum_prod_type, sum_bool]
  ring

def clusterDot (u v : ClusterField) : ℝ := ∑ s, dotProduct (u s) (v s)

set_option maxHeartbeats 600000 in
/-- This is the Gram identity for the actual parity embeddings. -/
theorem embedding_gram (p q : Parity) (u v : Vec) :
    clusterDot (embedding p u) (embedding q v) = if p = q then 8 * dotProduct u v else 0 := by
  obtain ⟨p₁, p₂, p₃⟩ := p
  obtain ⟨q₁, q₂, q₃⟩ := q
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;>
    norm_num [clusterDot, embedding, reflect, character, waveSigns, sign,
      sum_parity, dotProduct, Fin.sum_univ_succ] <;> ring

theorem projectedEmbedding_orthogonal (p q : Parity) (h : p ≠ q) (u v : Vec) :
    clusterDot (projectedEmbedding p u) (projectedEmbedding q v) = 0 := by
  simp [projectedEmbedding, embedding_gram, h]

theorem embedding_normSq (p : Parity) (v : Vec) :
    clusterDot (embedding p v) (embedding p v) = 8 * dotProduct v v := by
  simp only [embedding_gram, ite_true]

theorem embedding_ne_zero (p : Parity) (v : Vec) (hv : v ≠ 0) : embedding p v ≠ 0 := by
  intro h
  have hnorm := embedding_normSq p v
  rw [h] at hnorm
  have hdot : dotProduct v v = 0 := by simpa [clusterDot] using hnorm.symm
  exact hv (dotProduct_self_eq_zero.mp hdot)

theorem cluster_top_ne_zero : embedding selectedParity topVector ≠ 0 :=
  embedding_ne_zero selectedParity topVector topVector_ne_zero

/-- Fourier coefficient on the sign cube, including the polar reflection. -/
def parityCoefficient (p : Parity) (u : ClusterField) : Vec :=
  fun i => (1 / 8 : ℝ) * ∑ s, character p s * waveSigns s i * u s i

/-- The sign-character transform reconstructs every twenty-four-component
field before transverse projection. -/
theorem embedding_decomposition (u : ClusterField) :
    (∑ p, embedding p (parityCoefficient p u)) = u := by
  funext s i
  obtain ⟨s₁, s₂, s₃⟩ := s
  cases s₁ <;> cases s₂ <;> cases s₃ <;> fin_cases i <;>
    norm_num [Finset.sum_apply, embedding, reflect, parityCoefficient, character,
      waveSigns, sign, sum_parity] <;> ring

theorem clusterProjection_embedding (p : Parity) (v : Vec) :
    clusterProjection (embedding p v) = projectedEmbedding p v := by
  funext s
  change (waveProjection s).mulVec (character p s • reflect s v) = _
  rw [Matrix.mulVec_smul, waveProjection_reflect]
  rfl

theorem clusterProjection_sum (u : Parity → ClusterField) :
    clusterProjection (∑ p, u p) = ∑ p, clusterProjection (u p) := by
  funext s i
  simp only [clusterProjection, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- The projected parity spaces exhaust the entire transverse cluster. -/
theorem projected_decomposition (u : ClusterField) :
    (∑ p, projectedEmbedding p (parityCoefficient p u)) = clusterProjection u := by
  have h := congrArg clusterProjection (embedding_decomposition u)
  rw [clusterProjection_sum] at h
  simpa only [clusterProjection_embedding] using h

def planeVector (a : Fin 2 → ℝ) : Vec := ![a 0, a 1, -a 0 - a 1]

theorem planeVector_coordinates (v : Vec) (hv : ∑ i, v i = 0) :
    planeVector ![v 0, v 1] = v := by
  simp [Fin.sum_univ_succ] at hv
  ext i
  fin_cases i <;> simp [planeVector]
  linarith

/-- An explicit reconstruction with sixteen scalar coefficients, two for each
of the eight parity spaces. -/
theorem transverse_sixteen_coordinates (u : ClusterField) (hu : clusterProjection u = u) :
    ∃ a : Parity → Fin 2 → ℝ, u = ∑ p, embedding p (planeVector (a p)) := by
  refine ⟨fun p => ![(projection.mulVec (parityCoefficient p u)) 0,
    (projection.mulVec (parityCoefficient p u)) 1], ?_⟩
  calc
    u = ∑ p, projectedEmbedding p (parityCoefficient p u) :=
      hu.symm.trans (projected_decomposition u).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [planeVector_coordinates _ (sum_projection_mulVec _)]
      rfl

end Maxwell.Continuum.Corner
