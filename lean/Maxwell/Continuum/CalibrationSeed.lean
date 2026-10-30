import Maxwell.Continuum.CalibrationSeedScalars
import Maxwell.Continuum.CalibrationRationalCoordinates
import Maxwell.Continuum.CalibrationRationalSupport

/-! Literal rational finite-alias approximation to the actual normalized
top corner vector. The output has eight aliases and 24 real rational
coordinates; the infinite-fiber error follows from the actual unitary. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def seedSign (s : Corner.Parity) (j : Fin 3) : ℚ :=
  (if s.2.1 then 1 else -1)*(if s.2.2 then 1 else -1)*
    ![(if s.1 then 1 else -1), (if s.2.1 then 1 else -1), (if s.2.2 then 1 else -1)] j

theorem seedSign_cast (s : Corner.Parity) (j : Fin 3) :
    (seedSign s j : ℝ) = Corner.character Corner.selectedParity s*Corner.waveSigns s j := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;> fin_cases j <;>
    norm_num [seedSign, Corner.character, Corner.selectedParity, Corner.waveSigns, Corner.sign]

theorem seedSign_abs (s : Corner.Parity) (j : Fin 3) : |(seedSign s j : ℝ)| = 1 := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;> fin_cases j <;> norm_num [seedSign]

theorem normalizedClusterVector_formula (s : Corner.Parity) (j : Fin 3) :
    Corner.normalizedClusterVector s j =
      (seedSign s j : ℝ)*(Corner.topVector j/exactSeedDenominator) := by
  rw [seedSign_cast]
  simp only [Corner.normalizedClusterVector, Corner.normalizedTopVector, Corner.embedding,
    Corner.reflect, Pi.smul_apply, smul_eq_mul, exactSeedDenominator]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), div_eq_mul_inv, mul_inv_rev]
  ring

def rationalSeedCoordinates (N : ℕ) (i : Fin 24) : RationalComplex :=
  (seedSign (centralIndexFin.symm i).1 (centralIndexFin.symm i).2*
    seedComponent N (centralIndexFin.symm i).2, 0)

def rationalSeed (N : ℕ) : RationalAliasField := rationalExpandCoordinates (rationalSeedCoordinates N)

noncomputable def seedCoordinates (N : ℕ) : EuclideanSpace ℂ (Fin 24) :=
  WithLp.toLp 2 (fun i => rationalComplexValue (rationalSeedCoordinates N i))

noncomputable def seedVector (N : ℕ) : FiberSpace := (centralFinUnitary (seedCoordinates N)).val

noncomputable def exactSeedCoordinates : EuclideanSpace ℂ (Fin 24) :=
  WithLp.toLp 2 (fun i => (Corner.normalizedClusterVector
    (centralIndexFin.symm i).1 (centralIndexFin.symm i).2 : ℂ))

theorem seed_represents (N : ℕ) : Represents (rationalSeed N) (seedVector N) :=
  rationalExpandCoordinates_represents (rationalSeedCoordinates N) (seedCoordinates N) (fun _ => rfl)

theorem rationalSeed_supported (N : ℕ) : RationalSupported (rationalSeed N) 1 := by
  intro ν hν i
  have hn : rationalCentralCheck ν = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨j,hj⟩ := hν
    have hc := (rationalCentralCheck_true ν).mp h j
    rcases hc with hc | hc <;> rw [hc] at hj <;> norm_num at hj
  simp only [rationalSeed, rationalExpandCoordinates, hn, Bool.false_eq_true, ↓reduceIte]

theorem exactSeedCoordinates_vector :
    (centralFinUnitary exactSeedCoordinates).val = CornerBridge.topState.val := by
  apply CornerBridge.eq_of_aliases
  · exact centralSpace_noncentral _
  · intro ν hν
    exact CornerBridge.pack_noncentral _ ν hν
  · intro s
    ext j
    rw [← rationalCubeAlias_eq, centralFinUnitary_apply]
    change (Corner.normalizedClusterVector (centralIndexFin.symm (centralIndexFin (s,j))).1
      (centralIndexFin.symm (centralIndexFin (s,j))).2 : ℂ) = _
    rw [Equiv.symm_apply_apply, rationalCubeAlias_eq]
    change _ = CornerBridge.pack (CornerBridge.realCube Corner.normalizedClusterVector)
      (CornerBridge.cubeAlias s) j
    rw [CornerBridge.pack_alias]
    rfl

theorem seedCoordinates_error (N : ℕ) (i : Fin 24) :
    ‖seedCoordinates N i-exactSeedCoordinates i‖ ≤ 3*(1/2 : ℝ)^(N+7) := by
  change ‖rationalComplexValue (rationalSeedCoordinates N i)-
    (Corner.normalizedClusterVector (centralIndexFin.symm i).1 (centralIndexFin.symm i).2 : ℂ)‖ ≤ _
  rw [rationalComplexValue_eq, rationalSeedCoordinates]
  simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_mul]
  rw [normalizedClusterVector_formula]
  rw [show ((seedSign (centralIndexFin.symm i).1 (centralIndexFin.symm i).2 : ℚ) : ℂ)*
      ((seedComponent N (centralIndexFin.symm i).2 : ℚ) : ℂ) =
      (((seedSign (centralIndexFin.symm i).1 (centralIndexFin.symm i).2 : ℝ)*
        (seedComponent N (centralIndexFin.symm i).2 : ℝ) : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    ← mul_sub, abs_mul, seedSign_abs, one_mul]
  exact seedComponent_error N _

private theorem coordinate_norm_sum (x : EuclideanSpace ℂ (Fin 24)) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem seedVector_error (N : ℕ) :
    ‖seedVector N-CornerBridge.topState.val‖ ≤ (1/2 : ℝ)^N := by
  rw [← exactSeedCoordinates_vector]
  change ‖(centralFinUnitary (seedCoordinates N)-centralFinUnitary exactSeedCoordinates : centralSpace)‖ ≤ _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  apply (coordinate_norm_sum _).trans
  calc
    _ ≤ ∑ _i : Fin 24, 3*(1/2 : ℝ)^(N+7) := by
      apply Finset.sum_le_sum
      intro i _
      exact seedCoordinates_error N i
    _ = 72*(1/2 : ℝ)^(N+7) := by simp; ring
    _ ≤ (1/2 : ℝ)^N := by
      rw [pow_add]
      have hp : (0 : ℝ) ≤ (1/2 : ℝ)^N := by positivity
      norm_num only [show (1/2 : ℝ)^7 = 1/128 by norm_num]
      nlinarith only [hp]

theorem seedVector_norm (N : ℕ) : ‖seedVector N‖ ≤ 2 := by
  have h := norm_le_norm_sub_add (seedVector N) CornerBridge.topState.val
  rw [show ‖CornerBridge.topState.val‖ = 1 from CornerBridge.topState_norm] at h
  have he := seedVector_error N
  have hp : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith only [h, he, hp]

theorem seedVector_norm_lower {N : ℕ} (hN : 1 ≤ N) : (1/2 : ℝ) ≤ ‖seedVector N‖ := by
  have h := norm_le_norm_sub_add CornerBridge.topState.val (seedVector N)
  rw [show ‖CornerBridge.topState.val‖ = 1 from CornerBridge.topState_norm, norm_sub_rev] at h
  have he := seedVector_error N
  have hp : (1/2 : ℝ)^N ≤ 1/2 := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) hN
  linarith only [h, he, hp]

#print axioms seed_represents
#print axioms rationalSeed_supported
#print axioms seedVector_error
#print axioms seedVector_norm_lower

end Maxwell.Continuum.Calibration
