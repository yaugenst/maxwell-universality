import Maxwell.Cost.ColorAssemble.Encoding

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open ChildPermutation (Layout Config Frame budget)

def writeCode : Code := BankArray.writeCode 80 81 100 90

/-- The assembled parent label is written into its exact output slot. -/
theorem write_executes {k : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (out : Output k) (i : Fin (2*(2^k)))
    (index clock childClock : List Bool) (hw : 0<layout.parentWidth) (hi : addressValue index=i.val)
    (hs : Separated layout k) (s : Store) (cfg : Config layout index clock childClock s.val)
    (scratch : BankArray.Scratch s.val)
    (h90 : Word s.val 90 (IncidenceEncoding.word layout.parentWidth (data.value i).val))
    (rep : Represents layout s.val.memory data out) :
    ∃ cost t, cost≤30000*(budget layout index+1)^2 ∧ Executes input tape writeCode cost s t ∧
      t.val.memory=stepMemory layout data i s.val.memory ∧
      Represents layout t.val.memory data (stepOutput layout data i out) ∧
      Config layout index clock childClock t.val ∧ BankArray.Scratch t.val ∧
      t.val.tapes 7=s.val.tapes 7 ∧ BankArray.Frame s.val t.val ∧
      MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,et,tm,_,ts,t7,tf⟩ := BankArray.write_bank 80 81 100 90
    (by omega) (by omega) (by omega) (by omega) input tape layout.parentWidth.bits index layout.parentForward.bits
    (IncidenceEncoding.word layout.parentWidth (data.value i).val) out i
    (RationalAccumulator.bits_nonempty hw) hi (by simp only [IncidenceEncoding.word_length,addressValue_bits])
    s scratch cfg.parentWidth cfg.index cfg.parent h90 (by simpa only [addressValue_bits] using rep.output)
  have hmem : t.val.memory=stepMemory layout data i s.val.memory := by
    simpa only [stepMemory,addressValue_bits] using tm
  refine ⟨cost,t,?_,et,hmem,by rw [hmem]; exact represents_step rep hs i,
    cfg.of_frame (Frame.of_bank tf),ts,t7,tf,by rw [hmem]; exact stepMemory_frame layout data i s.val.memory⟩
  apply hcost.trans
  apply IncidencePass.array_cost_le
  · dsimp [budget]; omega
  · dsimp [budget]; omega
  · dsimp [budget]; omega
  · simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega
  · simp only [addressValue_bits]; dsimp [budget]; omega

end Maxwell.Cost.ColorAssemble
