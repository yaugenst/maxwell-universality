import Maxwell.Continuum.CornerBridgeGapReal
import Maxwell.Continuum.CornerHessian

/-! Certified real corner resolvent vectors in the full sign cube. -/

noncomputable section
namespace Maxwell.Continuum.CornerBridge

open Corner

theorem toggle_selected_eq_flipped (j : Fin 3) : toggle selectedParity j = flippedParity j := by
  fin_cases j <;> rfl

theorem flippedParity_injective : Function.Injective flippedParity := by
  intro j k h
  apply (toggle_inj_iff selectedParity j k).mp
  simpa only [toggle_selected_eq_flipped] using h

theorem resolventVector_sum (j : Fin 3) : ∑ i, resolventVector j i = 0 := by
  fin_cases j <;> simp [resolventVector,Fin.sum_univ_succ] <;> ring

def normalizedResolvent (j : Fin 3) : Vec :=
  (Real.sqrt (dotProduct topVector topVector))⁻¹ • resolventVector j

theorem normalizedResolvent_sum (j : Fin 3) : ∑ i, normalizedResolvent j i = 0 := by
  simp only [normalizedResolvent,Pi.smul_apply,← Finset.smul_sum,resolventVector_sum,smul_zero]

theorem normalizedResolvent_solves (j : Fin 3) :
    lambdaStar • normalizedResolvent j - (parityBlock (flippedParity j)).mulVec (normalizedResolvent j) =
      normalizedTopVector := by
  have h := congrArg (fun v : Vec => (Real.sqrt (dotProduct topVector topVector))⁻¹ • v)
    (resolventVector_solves j)
  rw [shiftedFlippedBlock,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,smul_sub] at h
  change lambdaStar • ((Real.sqrt (dotProduct topVector topVector))⁻¹ • resolventVector j) -
    (parityBlock (flippedParity j)).mulVec
      ((Real.sqrt (dotProduct topVector topVector))⁻¹ • resolventVector j) = _
  rw [Matrix.mulVec_smul,smul_comm lambdaStar]
  exact h

theorem normalizedResolvent_rayleigh (j : Fin 3) :
    dotProduct normalizedTopVector (normalizedResolvent j) = hessianCoefficient j := by
  have he : normalizedResolvent j = (shiftedFlippedBlock j)⁻¹.mulVec normalizedTopVector := by
    rw [normalizedResolvent,normalizedTopVector,Matrix.mulVec_smul,resolventVector_eq_inverse]
  rw [he,normalized_resolvent_rayleigh]

def resolventCube (j : Fin 3) : ClusterField :=
  (Real.sqrt 8)⁻¹ • embedding (flippedParity j) (normalizedResolvent j)

theorem resolventCube_transverse (j : Fin 3) : clusterProjection (resolventCube j) = resolventCube j := by
  rw [resolventCube,cornerProjection_smul,clusterProjection_embedding,projectedEmbedding,
    projection_mulVec_transverse _ (normalizedResolvent_sum j)]

theorem resolventCube_perp (j : Fin 3) : clusterDot normalizedClusterVector (resolventCube j) = 0 := by
  rw [normalizedClusterVector,resolventCube,clusterDot_smul_left,clusterDot_smul_right,
    embedding_gram,ite_eq_right (Ne.symm (flippedParity_ne_selected j)),mul_zero,mul_zero]

theorem embedding_sub (p : Parity) (v w : Vec) : embedding p (v-w) = embedding p v - embedding p w := by
  funext s i
  simp only [embedding,reflect,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sub]

theorem resolventCube_solves (j : Fin 3) :
    lambdaStar • resolventCube j - clusterOperator (resolventCube j) =
      velocity j normalizedClusterVector := by
  rw [resolventCube,cornerOperator_smul,
    cornerOperator_embedding _ _ (normalizedResolvent_sum j),
    smul_comm lambdaStar,← smul_sub,← embedding_smul,← embedding_sub,
    normalizedResolvent_solves,normalizedClusterVector,velocity_smul,velocity_embedding,
    toggle_selected_eq_flipped]

theorem velocity_transverse (j : Fin 3) :
    clusterProjection (velocity j normalizedClusterVector) = velocity j normalizedClusterVector := by
  rw [normalizedClusterVector,velocity_smul,velocity_embedding,cornerProjection_smul,
    clusterProjection_embedding,projectedEmbedding,
    projection_mulVec_transverse _ normalizedTopVector_sum]

theorem velocity_resolvent_gram (j k : Fin 3) :
    clusterDot (velocity j normalizedClusterVector) (resolventCube k) =
      if j = k then hessianCoefficient j else 0 := by
  rw [normalizedClusterVector,velocity_smul,velocity_embedding,resolventCube,
    clusterDot_smul_left,clusterDot_smul_right,embedding_gram,toggle_selected_eq_flipped]
  by_cases h : j = k
  · subst k
    simp only [ite_true,normalizedResolvent_rayleigh]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
    calc
      _ = (8 / (Real.sqrt 8)^2) * hessianCoefficient j := by ring
      _ = _ := by rw [hs]; norm_num
  · rw [ite_eq_right (fun hh => h (flippedParity_injective hh)),ite_eq_right h,mul_zero,mul_zero]

end Maxwell.Continuum.CornerBridge
