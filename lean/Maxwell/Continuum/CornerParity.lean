import Maxwell.Continuum.CornerEigenvector

/-!
# Parity intertwiners for the full twenty-four-component corner

The operator below acts on eight three-component amplitudes. It is literally
the projected nearest-neighbor coupling on the sign cube: each edge flips one
wavevector sign and has weight `-1/2`, `-1`, or `-2`. Its parity intertwiners
are proved against this action, not against a table of eigenvalues.
-/

noncomputable section
namespace Maxwell.Continuum.Corner

abbrev ClusterField := Parity → Vec

def waveSigns (s : Parity) : Vec := ![sign s.1, sign s.2.1, sign s.2.2]
def weights : Vec := ![1, 2, 4]

def toggle (s : Parity) (j : Fin 3) : Parity :=
  ![(!s.1, s.2.1, s.2.2), (s.1, !s.2.1, s.2.2), (s.1, s.2.1, !s.2.2)] j

def character (p s : Parity) : ℝ :=
  (if s.1 then 1 else sign p.1) * (if s.2.1 then 1 else sign p.2.1) *
    (if s.2.2 then 1 else sign p.2.2)

def waveProjection (s : Parity) : Mat :=
  1 - (1 / 3 : ℝ) • Matrix.vecMulVec (waveSigns s) (waveSigns s)

def reflect (s : Parity) (v : Vec) : Vec := fun i => waveSigns s i * v i

def polarReflect (j : Fin 3) (v : Vec) : Vec := fun i => if i = j then -v i else v i

def embedding (p : Parity) (v : Vec) : ClusterField :=
  fun s => character p s • reflect s v

def clusterProjection (u : ClusterField) : ClusterField :=
  fun s => (waveProjection s).mulVec (u s)

def clusterOperator (u : ClusterField) : ClusterField := fun s =>
  ∑ j : Fin 3, -(weights j / 2) •
    (waveProjection s).mulVec ((waveProjection (toggle s j)).mulVec (u (toggle s j)))

def projectedEmbedding (p : Parity) (v : Vec) : ClusterField :=
  embedding p (projection.mulVec v)

theorem waveProjection_idempotent (s : Parity) :
    waveProjection s * waveProjection s = waveProjection s := by
  obtain ⟨a, b, c⟩ := s
  ext i j
  cases a <;> cases b <;> cases c <;> fin_cases i <;> fin_cases j <;>
    norm_num [waveProjection, waveSigns, sign, Matrix.vecMulVec, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem reflect_smul (s : Parity) (r : ℝ) (v : Vec) :
    reflect s (r • v) = r • reflect s v := by
  ext i
  simp only [reflect, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflect_add (s : Parity) (u v : Vec) :
    reflect s (u + v) = reflect s u + reflect s v := by
  ext i
  simp only [reflect, Pi.add_apply, mul_add]

theorem embedding_add (p : Parity) (u v : Vec) :
    embedding p (u + v) = embedding p u + embedding p v := by
  ext s i
  simp only [embedding, reflect_add, smul_add, Pi.add_apply]

theorem embedding_smul (p : Parity) (r : ℝ) (v : Vec) :
    embedding p (r • v) = r • embedding p v := by
  ext s i
  simp only [embedding, reflect_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem embedding_sum (p : Parity) (v : Fin 3 → Vec) (s : Parity) :
    embedding p (∑ j, v j) s = ∑ j, embedding p (v j) s := by
  funext i
  simp only [embedding, reflect, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]

theorem waveProjection_reflect (s : Parity) (v : Vec) :
    (waveProjection s).mulVec (reflect s v) = reflect s (projection.mulVec v) := by
  obtain ⟨a, b, c⟩ := s
  ext i
  cases a <;> cases b <;> cases c <;> fin_cases i <;>
    norm_num [waveProjection, waveSigns, sign, reflect, projection, normal,
      Matrix.vecMulVec, Matrix.mulVec, Matrix.one_apply, dotProduct, Fin.sum_univ_succ] <;> ring

theorem reflect_toggle (s : Parity) (j : Fin 3) (v : Vec) :
    reflect (toggle s j) v = reflect s (polarReflect j v) := by
  obtain ⟨a, b, c⟩ := s
  ext i
  cases a <;> cases b <;> cases c <;> fin_cases j <;> fin_cases i <;>
    norm_num [reflect, waveSigns, toggle, polarReflect, sign]

theorem character_toggle (p s : Parity) (j : Fin 3) :
    character p (toggle s j) = character p s * waveSigns p j := by
  obtain ⟨p₁, p₂, p₃⟩ := p
  obtain ⟨s₁, s₂, s₃⟩ := s
  cases p₁ <;> cases p₂ <;> cases p₃ <;>
    cases s₁ <;> cases s₂ <;> cases s₃ <;> fin_cases j <;>
    norm_num [character, toggle, waveSigns, sign]

/-- Each projected parity embedding lands in the literal transverse cluster. -/
theorem clusterProjection_projectedEmbedding (p : Parity) (v : Vec) :
    clusterProjection (projectedEmbedding p v) = projectedEmbedding p v := by
  funext s
  change (waveProjection s).mulVec (character p s • reflect s (projection.mulVec v)) = _
  rw [Matrix.mulVec_smul, waveProjection_reflect, Matrix.mulVec_mulVec, projection_idempotent]
  rfl

def reducedEdge (p : Parity) (j : Fin 3) (v : Vec) : Vec :=
  -(weights j * waveSigns p j / 2) • projection.mulVec (polarReflect j (projection.mulVec v))

theorem reducedEdge_sum (p : Parity) (v : Vec) :
    ∑ j, reducedEdge p j v = (parityBlock p).mulVec v := by
  rw [parityBlock, block_explicit]
  ext i
  fin_cases i <;>
    norm_num [reducedEdge, weights, waveSigns, parityCoefficients, polarReflect,
      projection, normal, Matrix.vecMulVec, Matrix.mulVec, Matrix.one_apply,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem edge_intertwines (p s : Parity) (j : Fin 3) (v : Vec) :
    -(weights j / 2) • (waveProjection s).mulVec
      ((waveProjection (toggle s j)).mulVec (projectedEmbedding p v (toggle s j))) =
      embedding p (reducedEdge p j v) s := by
  have hproj := congrFun (clusterProjection_projectedEmbedding p v) (toggle s j)
  change (waveProjection (toggle s j)).mulVec (projectedEmbedding p v (toggle s j)) = _ at hproj
  rw [hproj]
  change -(weights j / 2) • (waveProjection s).mulVec
    (character p (toggle s j) • reflect (toggle s j) (projection.mulVec v)) = _
  rw [character_toggle, reflect_toggle, Matrix.mulVec_smul, waveProjection_reflect]
  change -(weights j / 2) • ((character p s * waveSigns p j) •
    reflect s (projection.mulVec (polarReflect j (projection.mulVec v)))) = _
  simp only [embedding, reducedEdge, reflect_smul, smul_smul]
  congr 1
  ring

/-- The exact parity intertwining identity for all twenty-four amplitudes. -/
theorem clusterOperator_intertwines (p : Parity) (v : Vec) :
    clusterOperator (projectedEmbedding p v) = embedding p ((parityBlock p).mulVec v) := by
  funext s
  rw [← reducedEdge_sum, embedding_sum]
  exact Finset.sum_congr rfl fun j _ => edge_intertwines p s j v

theorem projectedEmbedding_topVector :
    projectedEmbedding selectedParity topVector = embedding selectedParity topVector := by
  rw [projectedEmbedding, projection_mulVec_transverse topVector topVector_sum]

/-- The selected vector is an eigenvector of the full corner coupling. -/
theorem cluster_top_eigen :
    clusterOperator (embedding selectedParity topVector) =
      lambdaStar • embedding selectedParity topVector := by
  rw [← projectedEmbedding_topVector, clusterOperator_intertwines, topVector_eigen,
    embedding_smul, projectedEmbedding_topVector]

end Maxwell.Continuum.Corner
