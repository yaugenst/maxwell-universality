import Maxwell.Continuum.ContractSoundness

/-! Explicit input-independent constants close the analytic resource clauses
of the continuum contract. No machine execution or running-time bound is
assumed or asserted here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.Realization
open RealizationParameters
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent Calibration.FiniteAlgorithm.mode pecCurlCurl computedEnclosures

def analyticConstants (p : Source.Parameters) : Constants where
  overhead := Nat.ceil (8 * |Parameters.sourceVolumeCoefficient p| +
    |completeDescriptionCoefficient p| + 1) + 1
  wordCoefficient := outputBitCoefficient p + (2 * decodedWordCoefficient p + 1) +
    (analysisBits p + 4) + energyWordCoefficient p + detuningBitCoefficient p + 1
  conditionPower := analysisBits p + 10
  tolerancePower := 2 * Parameters.sourcePolynomialExponent p + 1
  overhead_pos := Nat.zero_lt_succ _
  wordCoefficient_pos := Nat.zero_lt_succ _
  conditionPower_pos := by omega
  tolerancePower_pos := Nat.zero_lt_succ _

private theorem overhead_bounds (p : Source.Parameters) :
    Parameters.sourceVolumeCoefficient p ≤ ((analyticConstants p).overhead : ℝ) ∧
    8 * Parameters.sourceVolumeCoefficient p ≤ ((analyticConstants p).overhead : ℝ) ∧
    completeDescriptionCoefficient p + 1 ≤ ((analyticConstants p).overhead : ℝ) := by
  have h := Nat.le_ceil (8 * |Parameters.sourceVolumeCoefficient p| +
    |completeDescriptionCoefficient p| + 1)
  have hv := le_abs_self (Parameters.sourceVolumeCoefficient p)
  have hd := le_abs_self (completeDescriptionCoefficient p)
  have hv0 := abs_nonneg (Parameters.sourceVolumeCoefficient p)
  have hd0 := abs_nonneg (completeDescriptionCoefficient p)
  simp only [analyticConstants, Nat.cast_add, Nat.cast_one]
  constructor
  · linarith only [h, hv, hv0, hd0]
  constructor <;> linarith only [h, hv, hd, hv0, hd0]

private theorem budget_large (C : Constants) (S : Source.SparseSystem)
    (hm2 : 2 ≤ S.nnz) (k : ℕ) :
    budget C S k = (C.overhead : ℝ) * (S.nnz : ℝ) ^ (3 / 2 : ℝ) * (logSize S : ℝ) ^ k := by
  rw [budget, S.effectiveSize_of_two_le hm2]

theorem analytic_resources (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 0 < S.nnz) (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S)
    (hb : S.source ≠ 0) (j : Fin (drawCount p S hm)) :
    Resources p (analyticConstants p) S hm hb j := by
  have hcoeff := overhead_bounds p
  have hv := Parameters.source_physical_volume_bound p S hm hm2 hp.1
  have hvolume :
      (MeasureTheory.volume (BoxModes.openBox (BoxCutoff.side (box p S hm)))).toReal ≤
        budget (analyticConstants p) S 24 := by
    rw [budget_large _ _ hm2]
    exact hv.trans (by gcongr; exact hcoeff.1)
  have hgrid : (gridCount p S hm : ℝ) ≤ budget (analyticConstants p) S 24 := by
    have hg : (gridCount p S hm : ℝ) ≤ 8 * ((ambientCells p S hm).length : ℝ) := by
      exact_mod_cast gridCount_ambient p S hm
    rw [ambientCells_volume] at hg
    rw [budget_large _ _ hm2]
    calc
      _ ≤ 8 * (Parameters.sourceVolumeCoefficient p * (S.nnz : ℝ) ^ (3 / 2 : ℝ) *
          (logSize S : ℝ) ^ 24) := hg.trans (mul_le_mul_of_nonneg_left hv (by norm_num))
      _ = (8 * Parameters.sourceVolumeCoefficient p) * (S.nnz : ℝ) ^ (3 / 2 : ℝ) *
          (logSize S : ℝ) ^ 24 := by ring
      _ ≤ _ := by gcongr; exact hcoeff.2.1
  have hdescription : ((computedBytes p S hm j).length : ℝ) ≤
      budget (analyticConstants p) S 64 := by
    have hd := completeDescriptionBits_polynomial p S hm hm2 hp hb j
    have hℓ : (1 : ℝ) ≤ logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
    have hs : (1 : ℝ) ≤ (S.nnz : ℝ) ^ (3 / 2 : ℝ) * (logSize S : ℝ) ^ 64 :=
      one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)) (one_le_pow₀ hℓ)
    rw [budget_large _ _ hm2]
    calc
      _ = ((completeDescriptionBits p S hm j).length : ℝ) + 1 := by
        simp only [computedBytes, List.length_cons, Nat.cast_add, Nat.cast_one]
      _ ≤ completeDescriptionCoefficient p * (S.nnz : ℝ) ^ (3 / 2 : ℝ) *
          (logSize S : ℝ) ^ 64 + (S.nnz : ℝ) ^ (3 / 2 : ℝ) * (logSize S : ℝ) ^ 64 :=
        add_le_add hd hs
      _ = (completeDescriptionCoefficient p + 1) * (S.nnz : ℝ) ^ (3 / 2 : ℝ) *
          (logSize S : ℝ) ^ 64 := by ring
      _ ≤ _ := by gcongr; exact hcoeff.2.2
  have lift {n a : ℕ} (hn : n ≤ a * logSize S) (ha : a ≤ (analyticConstants p).wordCoefficient) :
      n ≤ wordBudget (analyticConstants p) S := hn.trans (Nat.mul_le_mul_right _ ha)
  refine ⟨Parameters.sourcePhysicalLengths_pos p S hm, ?_, computedSource_real p S hm,
    gridTemplate_real p S hm, hvolume, hdescription, hgrid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(computedDielectric p S hm hb j).lower x, (computedDielectric p S hm hb j).upper x⟩
  · apply lift (decoder_format_width p S hm hm2 hp.1)
    simp only [analyticConstants]
    omega
  · intro w i
    apply lift (decoder_output_words p S hm hm2 hp hb w i)
    simp only [analyticConstants]
    omega
  · exact_mod_cast residual_pos p S hm
  · rw [S.effectiveSize_of_two_le hm2, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]
    apply le_trans _ (residual_polynomial p S hm hm2 hp.1)
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by exact_mod_cast hm) (by simp only [analyticConstants]; omega)
  · apply lift (residual_word_bits p S hm hm2 hp.1)
    simp only [analyticConstants]
    omega
  · apply lift (energy_word_bits p S hm hm2 hp.1)
    simp only [analyticConstants]
    omega
  · apply lift (randomBitCount_linear p S hm hm2 hp.1)
    simp only [analyticConstants]
    omega

/-- All source-dependent analytic resource, conditioning, and finite-report
obligations use this single explicit choice of constants. The remaining
uniform-program clauses are not hypotheses of this theorem. -/
theorem analytic_contract (p : Source.Parameters) :
    ∃ C : Constants, 10 ≤ C.conditionPower ∧
      ∀ S : Source.SparseSystem, ∀ hm : 0 < S.nnz, ∀ _hm2 : 2 ≤ S.nnz,
        Source.Promises p S → ∀ hb : S.source ≠ 0,
        (∀ j : Fin (drawCount p S hm), Resources p C S hm hb j) ∧
        (∀ w : Fin (randomBitCount p S hm) → Bool,
          (randomDraw p S hm w).val ∉ computedBadDraws p S hm hb →
            GoodDraw p C S hm hb (randomDraw p S hm w)) ∧
        ((FairBits.law (randomBitCount p S hm)).toOuterMeasure
          {w | (randomDraw p S hm w).val ∈ computedBadDraws p S hm hb}).toReal ≤
            3 / (64 * (S.nnz : ℝ)) := by
  refine ⟨analyticConstants p, by simp only [analyticConstants]; omega, ?_⟩
  intro S hm hm2 hp hb
  exact ⟨analytic_resources p S hm hm2 hp hb,
    selected_good_event p (analyticConstants p) S hm hm2 hp hb
      (by simp only [analyticConstants]; omega)⟩

#print axioms analytic_resources
#print axioms analytic_contract

end Maxwell.Continuum.Realization
