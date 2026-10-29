import Maxwell.Continuum.CornerBridgeTop

/-! Exact rank-one decomposition of the selected parity block. -/

noncomputable section
namespace Maxwell.Continuum.CornerBridge

open Corner

set_option maxHeartbeats 600000 in
/-- The selected transverse block is the sum of its two spectral projections. -/
theorem selected_rank_one :
    dotProduct topVector topVector • parityBlock selectedParity =
      (parityRoot selectedParity false * dotProduct topVector topVector) • projection +
        (lambdaStar - parityRoot selectedParity false) • Matrix.vecMulVec topVector topVector := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  have hs3 : Real.sqrt 19 ^ 3 = 19 * Real.sqrt 19 := by
    calc
      _ = Real.sqrt 19 ^ 2 * Real.sqrt 19 := by ring
      _ = _ := by rw [hs]
  rw [topVector_normSq,parity_root_formula,parityBlock,block_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [selectedParity,parityCoefficients,sign,topVector,lambdaStar,
      coefficientSum,discriminant,projection,normal,Matrix.smul_apply,
      Matrix.add_apply,Matrix.vecMulVec_apply,Matrix.one_apply] <;> nlinarith

theorem selected_action_orthogonal (v : Vec) (hv : ∑ j, v j = 0)
    (ho : dotProduct normalizedTopVector v = 0) :
    (parityBlock selectedParity).mulVec v = parityRoot selectedParity false • v := by
  have hs : (Real.sqrt (dotProduct topVector topVector))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr topVector_normSq_pos))
  have hdot : dotProduct topVector v = 0 := by
    rw [normalizedTopVector,smul_dotProduct,smul_eq_mul] at ho
    exact (mul_eq_zero.mp ho).resolve_left hs
  have h := congrArg (fun M : Mat => M.mulVec v) selected_rank_one
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec,
    projection_mulVec_transverse v hv] at h
  have hout : (Matrix.vecMulVec topVector topVector).mulVec v = 0 := by
    funext i
    simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,mul_assoc,← Finset.mul_sum]
    rw [show ∑ j, topVector j * v j = 0 from hdot,mul_zero]
    rfl
  rw [hout,smul_zero,add_zero] at h
  have he : (parityRoot selectedParity false * dotProduct topVector topVector) • v =
      dotProduct topVector topVector • (parityRoot selectedParity false • v) := by
    rw [smul_smul,mul_comm]
  rw [he] at h
  exact smul_right_injective _ topVector_normSq_pos.ne' h

theorem selected_rayleigh (v : Vec) (hv : ∑ j, v j = 0)
    (ho : dotProduct normalizedTopVector v = 0) :
    dotProduct v ((parityBlock selectedParity).mulVec v) ≤ lambdaNext * dotProduct v v := by
  rw [selected_action_orthogonal v hv ho,dotProduct_smul,smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (other_root_le_next selectedParity false (by simp))
    (Finset.sum_nonneg (fun j _ => mul_self_nonneg (v j)))

end Maxwell.Continuum.CornerBridge
