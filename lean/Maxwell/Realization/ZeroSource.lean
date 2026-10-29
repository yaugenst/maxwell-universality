import Maxwell.Realization.BaseCases

namespace Maxwell.Realization

/-- The zero readout is exact for a zero right-hand side in every dimension,
without a matrix solve or a division by its zero normalization scale. -/
theorem zero_source_goodDraw (p : Source.Parameters) (C : Constants)
    (S : Source.SparseSystem) (hb : S.source = 0) :
    GoodDraw p C S (BaseCases.zeroInstance S) := by
  refine ⟨BaseCases.zero_instance_isUnit S, ?_, ?_⟩
  · rw [BaseCases.zero_instance_condition]
    exact Real.one_le_rpow (le_max_left _ _) (by positivity)
  · intro y _
    refine ⟨BaseCases.zero_decoder_fits S _,
      ⟨BaseCases.zero_messages S, BaseCases.zero_decoder_accurate S _ _⟩, ?_⟩
    intro w _ eta _
    rw [BaseCases.zero_decoder_decode]
    exact Source.zero_source_residual S eta hb

/-- Its full physical and readout resource bounds hold in all dimensions.
The variable number of zero rows must still be emitted by the finite program. -/
theorem zero_source_resources (C : Constants) (S : Source.SparseSystem)
    (hsize : 4 ≤ sizeBudget C S) (hbits : 2 ≤ bitBudget C S) :
    Resources C S (BaseCases.zeroInstance S) := by
  have hbitsR : (2 : ℝ) ≤ bitBudget C S := by exact_mod_cast hbits
  have hz : Source.ShortRational (bitBudget C S) 0 := by
    constructor <;> norm_num [signedBitLength, unsignedBitLength] <;> linarith
  have ho : Source.ShortRational (bitBudget C S) 1 := by
    constructor <;> norm_num [signedBitLength, unsignedBitLength] <;> linarith
  have hd0 : IsDyadic 0 := ⟨0, ⟨0⟩, by norm_num [Dyadic.value]⟩
  have hd1 : IsDyadic 1 := ⟨0, ⟨1⟩, by norm_num [Dyadic.value]⟩
  refine ⟨by norm_num [BaseCases.zeroInstance, BaseCases.box],
    by norm_num [BaseCases.zeroInstance, BaseCases.box],
    by norm_num [BaseCases.zeroInstance, BaseCases.box], ?_, ?_, ?_, ?_, ?_,
    (fun _ => hd1), (fun _ => hd0), (fun _ => ho), (fun _ => hz), ho,
    (fun _ => hz), ?_, ?_, ?_, ?_⟩
  · rw [BaseCases.zero_instance_dimension]
    decide
  · rw [BaseCases.zero_instance_dimension]
    norm_num
    linarith
  · simpa using hsize
  · dsimp [BaseCases.zeroDecoder]
    norm_num
    linarith
  · change 1 ≤ bitBudget C S
    omega
  · intro i
    exact Nat.zero_le _
  · intro i j _hj
    exact Fin.elim0 j
  · intro w i
    rw [BaseCases.zero_decoder_decode]
    exact hz
  · change (max (1:ℝ) S.nnz)^(-(C.tolerancePower:ℝ)) ≤ ((1:ℚ):ℝ)
    norm_num only [Rat.cast_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (neg_nonpos.mpr (Nat.cast_nonneg _))

end Maxwell.Realization
