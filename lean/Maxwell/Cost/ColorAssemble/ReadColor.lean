import Maxwell.Cost.ColorAssemble.Index

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open ChildPermutation (Layout Config Frame Private budget)

def readColorCode : Code := .seq (BankArray.readBankCode 86 81 128 87 88) (.atom (.readTape 88 30 31))

/-- Fetch the actual stored split bit and load the branch register. -/
theorem read_color {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (colors : Vector Bool n) (index clock childClock : List Bool) (i : Fin n)
    (hi : addressValue index=i.val) (s : Store) (cfg : Config layout index clock childClock s.val)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h88 : Blank s.val 88)
    (rep : BitArray.Represents s.val.memory layout.colors 1 (ColorPass.colorWords colors)) :
    ∃ cost t, cost≤36000*(budget layout index+1)^2 ∧ Executes input tape readColorCode cost s t ∧
      Word t.val 88 [colors.get i] ∧ t.val.registers 30=colors.get i ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock childClock t.val ∧
      (∀ j, j=4 ∨ 10 ≤ j → j≠88 → t.val.tapes j=s.val.tapes j) ∧ Frame s.val t.val := by
  obtain ⟨cost,a,hcost,ea,aw,ass,a7,am,_,af⟩ := BankArray.read_bank 86 81 128 87 88
    (by omega) (by omega) (by omega) (by omega) (by omega) input tape [true] index layout.colors.bits [false]
    (ColorPass.colorWords colors) i (by decide) hi (by decide) s ss h7 h88
    cfg.one cfg.index cfg.colors cfg.bitClock (by simpa only [addressValue_bits,addressValue,Bool.toNat_true] using rep)
  have a88 : Word a.val 88 [colors.get i] := by simpa [ColorPass.colorWords,Vector.get,Fin.cast] using aw
  obtain ⟨origin,ho⟩ := a88
  have hr : (a.val.tapes 88).read=some (colors.get i) := by simp [ho,BitTape.read,BitTape.shifted]
  let raw : BitRAMState := {a.val with
    pc := 1
    registers := Function.update (Function.update a.val.registers 30 (colors.get i)) 31 true}
  let t := Store.ofState raw
  have et : Executes input tape (.atom (.readTape 88 30 31)) 3 a t := by
    apply Executes.atom (extra:=1)
    · simp [BitRAM.next,a.property,hr,raw,BitRAMState.setRegister]
    · rfl
  have tf : Frame a.val t.val := by
    refine ⟨rfl,rfl,rfl,fun _ _ _ => rfl,?_⟩
    intro j _ hj
    simp only [t,Store.ofState,raw,Function.update_apply]
    simp [show j≠30 by omega,show j≠31 by omega]
  have frame := (Frame.of_except (show Private 88 by simp [Private,DoublingInit.Private,DoublingPass.Private]) af).trans tf
  refine ⟨cost+3,t,?_,ea.seq et,⟨origin,ho⟩,by simp [t,Store.ofState,raw],ass,a7,am,
    cfg.of_frame frame,af.2.2.2.1,frame⟩
  have hb := IncidencePass.array_cost_le [true] index layout.colors.bits [false] (budget layout index)
    (by simp only [List.length_cons,List.length_nil]; dsimp [budget]; omega) (by dsimp [budget]; omega) (by dsimp [budget]; omega)
    (by simp only [List.length_cons,List.length_nil]; dsimp [budget]; omega) (by dsimp [budget,addressValue]; omega)
  norm_num [addressValue] at hcost
  have hpositive : 1≤(budget layout index+1)^2 := by
    have hp : 0<(budget layout index+1)^2 := by positivity
    omega
  nlinarith

end Maxwell.Cost.ColorAssemble
