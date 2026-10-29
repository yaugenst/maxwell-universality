import Maxwell.Cost.BaseCases

/-! Complete resource and actual-program closure for the literal `m ≤ 1`
branch. This is one branch of the quantitative theorem, not a replacement
for the general sparse-input construction. -/

namespace Maxwell.Realization

def baseConstants : Constants where
  overhead := 4096
  logPower := 0
  coefficientBits := 2
  conditionPower := 1
  tolerancePower := 1
  stencilSize := 0
  overhead_pos := by decide
  coefficientBits_pos := by decide
  conditionPower_pos := by decide
  tolerancePower_pos := by decide

theorem base_bitBudget (S : Source.SparseSystem) : 2 ≤ bitBudget baseConstants S := by
  simp [bitBudget, baseConstants, unsignedBitLength]

theorem base_sizeBudget (S : Source.SparseSystem) : 4096 ≤ sizeBudget baseConstants S := by
  have hb : (1 : ℝ) ≤ (effectiveSize S : ℝ) := by
    exact_mod_cast (show 1 ≤ effectiveSize S by simp [effectiveSize])
  have hp : (1 : ℝ) ≤ (effectiveSize S : ℝ) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow hb (by norm_num)
  simp only [sizeBudget, baseConstants, pow_zero, mul_one]
  norm_num
  linarith

theorem base_resources (C : Constants) (S : Source.SparseSystem) (hm : S.nnz ≤ 1)
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
  · have hmax : max (1 : ℝ) (S.nnz : ℝ) = 1 := max_eq_left (by exact_mod_cast hm)
    simp [hmax]

theorem decodes_mono {decoder : Cost.BitRAM} {small large n fuel : ℕ}
    {I : Target.Instance n} (h : Decodes decoder small I fuel) (hle : small ≤ large) :
    Decodes decoder large I fuel := by
  intro messages
  obtain ⟨stop, hrun, houtput, hrandom⟩ := h messages
  obtain ⟨pairs, hout, hvalue, hshort⟩ := houtput
  refine ⟨stop, hrun, ⟨pairs, hout, hvalue, ?_⟩, hrandom⟩
  intro i
  exact ⟨(hshort i).1.trans hle, (hshort i).2.trans hle⟩

/-- One fixed encoder and decoder, actual every-draw execution, full
physical resources and conditioning, and every admissible-output guarantee
are all proved for the finite branch. -/
theorem complete_base_branch (p : Source.Parameters) (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : S.nnz ≤ 1) :
    (∀ draw : Draw 0, Encodes Cost.BaseCases.encoder S draw Cost.BaseCases.fuel
      (BaseCases.zeroInstance S)) ∧
    Decodes Cost.BaseCases.decoder (bitBudget baseConstants S)
      (BaseCases.zeroInstance S) Cost.BaseCases.fuel ∧
    Resources baseConstants S (BaseCases.zeroInstance S) ∧
    ((Cost.BaseCases.fuel + Cost.BaseCases.fuel : ℕ) : ℝ) ≤ sizeBudget baseConstants S ∧
    GoodDraw p baseConstants S (BaseCases.zeroInstance S) := by
  refine ⟨Cost.BaseCases.encodes S hunit hm, ?_, ?_, ?_, base_goodDraw p baseConstants S hunit hm⟩
  · exact decodes_mono (Cost.BaseCases.decodes S hunit hm) (by have := base_bitBudget S; omega)
  · exact base_resources baseConstants S hm (by have := base_sizeBudget S; linarith) (base_bitBudget S)
  · exact base_sizeBudget S

end Maxwell.Realization
