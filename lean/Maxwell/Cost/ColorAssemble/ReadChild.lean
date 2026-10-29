import Maxwell.Cost.ColorAssemble.Index

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open ChildPermutation (Layout Config Frame Private budget)

def childBase (layout : Layout) (bit : Bool) : ℕ := if bit then layout.rightForward else layout.leftForward

def readChildCode : Code := .branch 30 (BankArray.readBankCode 120 37 124 121 90)
  (BankArray.readBankCode 120 37 122 121 90)

/-- One child lookup reads the selected stored label through its binary address. -/
theorem read_child (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (labels : Vector (Fin (2^k)) (2^k)) (bit : Bool)
    (index clock childClock lookup : List Bool) (i : Fin (2^k))
    (hw : layout.parentWidth=k+2) (hi : addressValue lookup=i.val)
    (hc : childClock.length=layout.childWidth) (hl : lookup.length≤budget layout index)
    (s : Store) (cfg : Config layout index clock childClock s.val)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h90 : Blank s.val 90)
    (hlookup : Word s.val 37 lookup) (hr : s.val.registers 30=bit)
    (rep : BitArray.Represents s.val.memory (childBase layout bit) layout.childWidth
      (DoublingPass.words layout.childWidth labels)) :
    ∃ cost t, cost≤36000*(budget layout index+1)^2 ∧ Executes input tape readChildCode cost s t ∧
      Word t.val 90 (IncidenceEncoding.word layout.childWidth (labels.get i).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock childClock t.val ∧ BankArray.FrameExcept 90 s.val t.val ∧
      t.val.registers 30=bit := by
  let bank := if bit then 124 else 122
  have hb : 10≤bank := by dsimp [bank]; split <;> omega
  have baseWord : Word s.val bank (childBase layout bit).bits := by
    cases bit
    · simpa [bank,childBase,Layout.outputBase] using cfg.bases 0
    · simpa [bank,childBase,Layout.outputBase] using cfg.bases 2
  have hcw : layout.childWidth=k+1 := by simp [Layout.childWidth,hw]
  obtain ⟨cost,t,hcost,he,tw,ts,t7,tm,_,tf⟩ := BankArray.read_bank 120 37 bank 121 90
    (by omega) (by omega) hb (by omega) (by omega)
    input tape layout.childWidth.bits lookup (childBase layout bit).bits childClock
    (DoublingPass.words layout.childWidth labels) i (RationalAccumulator.bits_nonempty (by omega)) hi
    (by simpa only [addressValue_bits] using hc) s ss h7 h90 cfg.childWidth hlookup baseWord cfg.childClock
    (by simpa only [addressValue_bits] using rep)
  have branchRun : Executes input tape readChildCode (1+cost) s t := by
    cases bit
    · exact .no hr he
    · exact .yes hr he
  refine ⟨1+cost,t,?_,branchRun,by simpa only [DoublingPass.words_get] using tw,ts,t7,tm,
    cfg.of_frame (Frame.of_except (by simp [Private,DoublingInit.Private,DoublingPass.Private]) tf),tf,
    (tf.2.2.2.2 30 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr⟩
  have hbnd : (childBase layout bit).bits.length≤budget layout index := by
    cases bit <;> dsimp [childBase,budget] <;> omega
  have hcost' := IncidencePass.array_cost_le layout.childWidth.bits lookup (childBase layout bit).bits childClock (budget layout index)
    (by dsimp [budget]; omega) hl hbnd (by dsimp [budget]; omega)
    (by simp only [addressValue_bits]; dsimp [budget]; omega)
  simp only [addressValue_bits] at hcost
  have hp : layout.childWidth≤budget layout index := by dsimp [budget]; omega
  nlinarith

end Maxwell.Cost.ColorAssemble
