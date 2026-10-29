import Maxwell.Cost.ChildPermutation.Common

/-! The four actual indexed bank writes for one recursive child label:
forward left, inverse left, forward right, inverse right. -/
namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open IncidenceEncoding (word)

private theorem output_base_budget (layout : Layout) (index : List Bool) (s : Fin 4) :
    (layout.outputBase s).bits.length ≤ budget layout index := by
  fin_cases s <;> simp only [Layout.outputBase] <;> dsimp [budget] <;> omega

private theorem write_one {k : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (out : Outputs k) (i : Fin (2^k)) (slot : Fin 4)
    (indexBank payloadBank : ℕ) (hib : 10 ≤ indexBank) (hpb : 10 ≤ payloadBank)
    (index clock childClock idx : List Bool) (hw : 0 < layout.childWidth)
    (hi : addressValue idx=(d.writeIndex slot i).val)
    (hlen : idx.length ≤ budget layout index) (hs : layout.Separated k)
    (s : Store) (cfg : Config layout index clock childClock s.val) (scratch : BankArray.Scratch s.val)
    (hidx : Word s.val indexBank idx)
    (hpayload : Word s.val payloadBank (word layout.childWidth (d.writeValue slot i).val))
    (rep : Represents layout s.val.memory d out) :
    ∃ cost t, cost ≤ 30000*(budget layout index+1)^2 ∧
      Executes input tape (BankArray.writeCode 120 indexBank (122+slot.val) payloadBank) cost s t ∧
      t.val.memory=writeMemory layout d i slot s.val.memory ∧
      Represents layout t.val.memory d (writeOutput layout.childWidth d i slot out) ∧
      BankArray.Scratch t.val ∧ t.val.tapes 7=s.val.tapes 7 ∧ BankArray.Frame s.val t.val := by
  obtain ⟨cost,t,hcost,et,tm,_,ts,t7,tf⟩ := BankArray.write_bank 120 indexBank (122+slot.val) payloadBank
    (by omega) hib (by omega) hpb input tape layout.childWidth.bits idx (layout.outputBase slot).bits
    (word layout.childWidth (d.writeValue slot i).val) (out slot) (d.writeIndex slot i)
    (RationalAccumulator.bits_nonempty hw) hi (by simp only [IncidenceEncoding.word_length,addressValue_bits])
    s scratch cfg.childWidth hidx (cfg.bases slot) hpayload
    (by simpa only [addressValue_bits] using rep.outputs slot)
  have hmem : t.val.memory=writeMemory layout d i slot s.val.memory := by
    simpa only [writeMemory,addressValue_bits] using tm
  refine ⟨cost,t,?_,et,hmem,?_,ts,t7,tf⟩
  · apply hcost.trans
    apply IncidencePass.array_cost_le
    · dsimp [budget]; omega
    · exact hlen
    · exact output_base_budget layout index slot
    · simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega
    · simp only [addressValue_bits]; dsimp [budget]; omega
  · rw [hmem]
    exact represents_write rep hs i slot

def writeCode : Code := .seq (BankArray.writeCode 120 81 122 89)
  (.seq (BankArray.writeCode 120 89 123 37)
    (.seq (BankArray.writeCode 120 81 124 91) (BankArray.writeCode 120 91 125 37)))

/-- One fixed finite code performs both forward writes and both inverse
scatters, preserving the metadata and the three retained payload words. -/
theorem write_executes {k : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (out : Outputs k) (i : Fin (2^k))
    (index clock childClock : List Bool) (hw : layout.parentWidth=k+2)
    (hi : addressValue index=i.val) (hs : layout.Separated k)
    (s : Store) (cfg : Config layout index clock childClock s.val)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (h89 : Word s.val 89 (word layout.childWidth (d.left i).val))
    (h91 : Word s.val 91 (word layout.childWidth (d.right i).val))
    (h37 : Word s.val 37 (word layout.childWidth i.val))
    (rep : Represents layout s.val.memory d out) :
    ∃ cost t, cost ≤ 200000*(budget layout index+1)^2 ∧
      Executes input tape writeCode cost s t ∧
      t.val.memory=stepMemory layout d i s.val.memory ∧
      Represents layout t.val.memory d (stepOutputs layout.childWidth d i out) ∧
      Config layout index clock childClock t.val ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      Word t.val 89 (word layout.childWidth (d.left i).val) ∧
      Word t.val 91 (word layout.childWidth (d.right i).val) ∧
      Word t.val 37 (word layout.childWidth i.val) ∧
      Frame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory ∧ BankArray.Frame s.val t.val := by
  have hcw : layout.childWidth=k+1 := by simp [Layout.childWidth,hw]
  have hpos : 0 < layout.childWidth := by omega
  have hfit : 2^k ≤ 2^layout.childWidth := by rw [hcw,pow_succ]; omega
  have wi (j : Fin (2^k)) : addressValue (word layout.childWidth j.val)=j.val :=
    IncidenceEncoding.word_value _ _ (j.isLt.trans_le hfit)
  have ib : index.length ≤ budget layout index := by dsimp [budget]; omega
  have wb (j : Fin (2^k)) : (word layout.childWidth j.val).length ≤ budget layout index := by
    simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega
  obtain ⟨ca,a,hca,ea,am,ar,ass,a7,af⟩ := write_one input tape layout d out i 0 81 89
    (by omega) (by omega) index clock childClock index hpos hi ib hs s cfg scratch cfg.index h89 rep
  have acfg := Config.of_frame (Frame.of_bank af) cfg
  have a89 := BankArray.word_of_eq (af.2.2.2.1 89 (by omega)) h89
  have a37 := BankArray.word_of_eq (af.2.2.2.1 37 (by omega)) h37
  obtain ⟨cb,b,hcb,eb,bm,br,bss,b7,bf⟩ := write_one input tape layout d _ i 1 89 37
    (by omega) (by omega) index clock childClock (word layout.childWidth (d.left i).val)
    hpos (wi (d.left i)) (wb (d.left i)) hs a acfg ass a89 a37 ar
  have bcfg := Config.of_frame (Frame.of_bank bf) acfg
  have b91 := BankArray.word_of_eq ((bf.2.2.2.1 91 (by omega)).trans (af.2.2.2.1 91 (by omega))) h91
  obtain ⟨cc,c,hcc,ec,cm,cr,css,c7,cf⟩ := write_one input tape layout d _ i 2 81 91
    (by omega) (by omega) index clock childClock index hpos hi ib hs b bcfg bss bcfg.index b91 br
  have ccfg := Config.of_frame (Frame.of_bank cf) bcfg
  have c91 := BankArray.word_of_eq (cf.2.2.2.1 91 (by omega)) b91
  have c37 := BankArray.word_of_eq ((cf.2.2.2.1 37 (by omega)).trans (bf.2.2.2.1 37 (by omega))) a37
  obtain ⟨ct,t,hct,et,tm,tr,tss,t7,tf⟩ := write_one input tape layout d _ i 3 91 37
    (by omega) (by omega) index clock childClock (word layout.childWidth (d.right i).val)
    hpos (wi (d.right i)) (wb (d.right i)) hs c ccfg css c91 c37 cr
  have keep (j : ℕ) (hj : j=4 ∨ 10≤j) : t.val.tapes j=s.val.tapes j :=
    (tf.2.2.2.1 j hj).trans ((cf.2.2.2.1 j hj).trans ((bf.2.2.2.1 j hj).trans (af.2.2.2.1 j hj)))
  have hmem : t.val.memory=stepMemory layout d i s.val.memory := by
    rw [tm,cm,bm,am]
    rfl
  refine ⟨ca+(cb+(cc+ct)),t,by omega,ea.seq (eb.seq (ec.seq et)),hmem,tr,
    Config.of_frame (Frame.of_bank tf) ccfg,tss,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (t7.trans (c7.trans (b7.trans a7))) h7
  · exact BankArray.word_of_eq (keep 89 (by omega)) h89
  · exact BankArray.word_of_eq (keep 91 (by omega)) h91
  · exact BankArray.word_of_eq (keep 37 (by omega)) h37
  · exact (Frame.of_bank af).trans ((Frame.of_bank bf).trans ((Frame.of_bank cf).trans (Frame.of_bank tf)))
  · rw [hmem]
    exact stepMemory_frame layout d i s.val.memory
  · exact af.trans (bf.trans (cf.trans tf))

end Maxwell.Cost.ChildPermutation
