import Maxwell.Continuum.FourierTensorModeDecodeData

/-! Checked execution of the literal alias decoder from the combined
table-row bank, restoring the scratch needed by dyadic rounding. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeDecode
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem outside_changed (i : ℕ)
    (hi : (5 ≤ i ∧ i<30) ∨ (107 ≤ i ∧ i<310 ∧ i∉NaturalQuotient.workPorts)) : i∉changed := by
  have hr : i∉ids RowArithmetic.bank := by
    apply fun h => outside_workspace RowArithmetic.bank i (by omega) (Finset.mem_union_right _ h)
  have hn : i∉ModeIndex.ports := by simp only [ModeIndex.ports,Finset.mem_Icc];omega
  have hq : i∉NaturalQuotient.workPorts := by
    rcases hi with hi|hi
    · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton];omega
    · exact hi.2.2
  intro h
  rcases Finset.mem_union.mp h with hsmall|hall
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hsmall
    omega
  · rcases Finset.mem_union.mp hall with hall|hquot
    · rcases Finset.mem_union.mp hall with hp|hrat
      · exact hn hp
      · exact hr hrat
    · exact hq hquot

theorem executes (v : ℕ→Parts) (n : ℕ→ℕ) (W : ℕ) (hW : 2≤W)
    (hw : WidthBank RowArithmetic.bank W v) (hg : Good RowArithmetic.bank v)
    (hn : ∀i∈ModeIndex.ports,(n i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : RationalDataflow.Ready RowArithmetic.bank v s)
    (hb : NatAssign.Bank ModeIndex.ports n s.val) (hz : DyadicFloor.Clean s.val) :
    ∃cost t,Executes input tape ArrayDecodeMachine.decodeLoadCode cost s t ∧
      cost≤2^112*(W+5)^2 ∧ RationalDataflow.Ready RowArithmetic.bank (decoded v n) t ∧
      Good RowArithmetic.bank (decoded v n) ∧ WidthBank RowArithmetic.bank (2*W+8) (decoded v n) ∧
      NatAssign.Bank ModeIndex.ports (after v n) t.val ∧
      (∀i∈ModeIndex.ports,(after v n i).bits.length≤2*W+8) ∧
      DyadicFloor.Clean t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  have hparts : ids RawFree.stageRegisters⊆allIds := by
    intro i hi
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have hwork : NaturalQuotient.workPorts⊆allIds := Finset.subset_union_right
  have scratch : ∀i,i<5→Blank s.val i := by
    intro i hi
    by_cases hlt : i<4
    · exact hr.2 i hlt
    · have h4 : i=4 := by omega
      subst i
      exact hz.1
  obtain ⟨cost,t,he,hcost,bank,ready,z4,frame⟩ := ArrayDecodeMachine.decodeLoad_scratch_executes
    allIds allIds_ge decode_subset hwork hparts (combined v n) v (combined_parts v n)
    (combined_quotient v n) W hW (combined_width v n W hw hn) input tape s
    (combined_bank hr hb hz) scratch
  refine ⟨cost,t,he,hcost,ready,decoded_good v n hg,decoded_width v n W hw hn,
    fun i hi => bank i (Finset.mem_union_left _ (Finset.mem_union_left _ hi)),
    after_width v n W hw hn,⟨z4,?_⟩,frame⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hextra|hquot
  · have hout : i∉changed := by
      apply outside_changed
      apply Or.inr
      simp only [DyadicFloor.extraIds,Finset.mem_insert,Finset.mem_singleton] at hextra
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.blank_of_eq (frame.tapes i hout) (hz.2 i (Finset.mem_union_left _ hextra))
  · apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    have hb' := bank i (Finset.mem_union_right _ hquot)
    change Word t.val i (after v n i) at hb'
    simpa only [after_quotient v n i hquot] using hb'

theorem table_frame {m : ℕ} {a : Table m} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame changed s.val t.val) (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : (5 ≤ i ∧ i<30) ∨ (107 ≤ i ∧ i<310 ∧ i∉NaturalQuotient.workPorts)) :=
    f.tapes i (outside_changed i hi)
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven,
    BankArray.word_of_eq (keep 200 (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem output_frame {m : ℕ} {a : Table m} {s t : Store} (h : a.OutputReady s)
    (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hout : i∉changed := by
    have hm : i=37 ∨ i=210 ∨ i=212 ∨ i=213 ∨ i=214 ∨ i=215 := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using hi
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    all_goals apply outside_changed;decide
  exact f.tapes i hout

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeDecode
