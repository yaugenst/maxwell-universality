import Maxwell.Continuum.CalibrationCoefficientMachine
import Maxwell.Continuum.CalibrationInverseAllocation
import Maxwell.Continuum.RationalDataflowTableHeaderSwap

/-! The generated coefficient buffer becomes the input buffer by actual
header swaps. The discarded source buffer is described from the memory
present after generation; no preservation of its unused data is assumed. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 7000000
set_option maxRecDepth 32768

def refreshTable {n : ℕ} (a : PartArray.Table n) (memory : ℕ → Bool) : PartArray.Table n :=
  {a with
    positive:=NeumannMachine.memoryWords memory (addressValue a.basePositive) (addressValue a.width) n
    negative:=NeumannMachine.memoryWords memory (addressValue a.baseNegative) (addressValue a.width) n
    denominator:=NeumannMachine.memoryWords memory (addressValue a.baseDenominator) (addressValue a.width) n}

theorem refresh_ready {n : ℕ} (a : PartArray.Table n) (t : Store)
    (headers : ∀ k∈([200,202,203,204,205]:List ℕ), BankArray.Word t.val k
      (if k=200 then a.width else if k=202 then a.basePositive else if k=203 then a.baseNegative
        else if k=204 then a.baseDenominator else a.clock))
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) :
    (refreshTable a t.val.memory).Ready t := by
  refine ⟨hz,h7,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [refreshTable] using headers 200 (by simp)
  · simpa [refreshTable] using headers 202 (by simp)
  · simpa [refreshTable] using headers 203 (by simp)
  · simpa [refreshTable] using headers 204 (by simp)
  · simpa [refreshTable] using headers 205 (by simp)
  · exact NeumannMachine.memoryWords_represents _ _ _ _
  · exact NeumannMachine.memoryWords_represents _ _ _ _
  · exact NeumannMachine.memoryWords_represents _ _ _ _

theorem generated_header_executes {n m : ℕ} (a : PartArray.Table n) (b : PartArray.Table m)
    (B W : ℕ) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (v : ℕ → Parts) (nf : ℕ → ℕ)
    (hn : ∀ k ∈ ids RawFree.neighborRegisters, nf k=dataValues v k)
    (input : List Bool) (tape : ℕ → Bool) (u : Store)
    (headers : ∀ k∈([200,202,203,204,205]:List ℕ), BankArray.Word u.val k
      (if k=200 then a.width else if k=202 then a.basePositive else if k=203 then a.baseNegative
        else if k=204 then a.baseDenominator else a.clock))
    (hb : b.OutputReady u) (hbank : NatAssign.Bank emissionIds nf u.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank u.val k)
    (h216 : RationalAccumulator.Blank u.val 216) :
    ∃ cost t, Executes input tape PartArray.headerSwapCode cost u t ∧ cost ≤ 256*(B+W+1) ∧
      b.Ready t ∧ (refreshTable a u.val.memory).OutputReady t ∧
      RationalDataflow.Ready RawFree.neighborRegisters v t ∧
      RationalAccumulator.Blank t.val 216 ∧
      BinaryPrecision.Frame (insert 216 PartArray.headerSlots) u.val t.val := by
  have old : (refreshTable a u.val.memory).Ready u := refresh_ready a u headers hb.scratch hb.seven
  have oldMeta : (refreshTable a u.val.memory).MetadataWidth (B+W) :=
    ⟨haMeta.width.trans (by omega),haMeta.basePositive.trans (by omega),
      haMeta.baseNegative.trans (by omega),haMeta.baseDenominator.trans (by omega),
      haMeta.clock.trans (by omega)⟩
  have raw : RationalDataflow.Ready RawFree.neighborRegisters v u := by
    refine ⟨?_,fun k hk => hz k (by omega)⟩
    intro k hk
    simpa only [hn k hk] using hbank k (emissionIds_parts hk)
  obtain ⟨cost,t,e,hc,raw',b',old',temp',frame⟩ := PartArray.headerSwap_executes
    (refreshTable a u.val.memory) b (B+W) oldMeta (hbMeta.mono (by omega))
    RawFree.neighborRegisters v input tape u raw old hb h216
  exact ⟨cost,t,e,hc,b',old',raw',temp',frame⟩

#print axioms generated_header_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
