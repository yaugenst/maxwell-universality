import Maxwell.Cost.ChildPermutation.Common

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing.Coloring.NumericSplit

/-- One preserved-parent lookup with an explicit binary index word. -/
theorem read_parent {k : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (index clock childClock lookup : List Bool)
    (indexBank target : ℕ) (i : Fin (2*(2^k)))
    (hbank : 10 ≤ indexBank) (htarget : Private target)
    (hw : 0<layout.parentWidth) (hi : addressValue lookup=i.val)
    (hc : clock.length=layout.parentWidth) (hl : lookup.length≤budget layout index)
    (s : Store) (cfg : Config layout index clock childClock s.val)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) (ht : Blank s.val target)
    (hlookup : Word s.val indexBank lookup)
    (rep : BitArray.Represents s.val.memory layout.parentForward layout.parentWidth
      (DoublingPass.words layout.parentWidth (Vector.ofFn data.target))) :
    ∃ cost t, cost≤35000*(budget layout index+1)^2 ∧
      Executes input tape (BankArray.readBankCode 80 indexBank 100 83 target) cost s t ∧
      Word t.val target (IncidenceEncoding.word layout.parentWidth (data.target i).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock childClock t.val ∧ BankArray.FrameExcept target s.val t.val := by
  obtain ⟨cost,t,hcost,he,tw,ts,t7,tm,_,tf⟩ := BankArray.read_bank 80 indexBank 100 83 target
    (by omega) hbank (by omega) (by omega)
    (by simp only [Private,DoublingInit.Private,DoublingPass.Private] at htarget; omega)
    input tape layout.parentWidth.bits lookup layout.parentForward.bits clock
    (DoublingPass.words layout.parentWidth (Vector.ofFn data.target)) i
    (RationalAccumulator.bits_nonempty hw) hi (by simpa only [addressValue_bits] using hc)
    s ss h7 ht cfg.parentWidth hlookup cfg.parent cfg.clock
    (by simpa only [addressValue_bits] using rep)
  refine ⟨cost,t,?_,he,by simpa [DoublingPass.words,IncidenceEncoding.words,Vector.get,Fin.cast] using tw,
    ts,t7,tm,cfg.of_frame (Frame.of_except htarget tf),tf⟩
  have hb := IncidencePass.array_cost_le layout.parentWidth.bits lookup layout.parentForward.bits clock (budget layout index)
    (by dsimp [budget]; omega) hl (by dsimp [budget]; omega) (by dsimp [budget]; omega)
    (by simp only [addressValue_bits]; dsimp [budget]; omega)
  simp only [addressValue_bits] at hcost
  have hp : layout.parentWidth≤budget layout index := by dsimp [budget]; omega
  nlinarith

/-- The lower-half color is read from its one-bit memory slot. -/
theorem read_color {k : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (index clock childClock : List Bool) (i : Fin (2^k))
    (hi : addressValue index=i.val) (s : Store) (cfg : Config layout index clock childClock s.val)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h88 : Blank s.val 88)
    (rep : BitArray.Represents s.val.memory layout.colors 1 (ColorPass.colorWords data.colors)) :
    ∃ cost t, cost≤35000*(budget layout index+1)^2 ∧
      Executes input tape (BankArray.readBankCode 86 81 128 87 88) cost s t ∧
      Word t.val 88 [data.colors.get (lower i)] ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ Config layout index clock childClock t.val ∧ BankArray.FrameExcept 88 s.val t.val := by
  obtain ⟨cost,t,hcost,he,tw,ts,t7,tm,_,tf⟩ := BankArray.read_bank 86 81 128 87 88
    (by omega) (by omega) (by omega) (by omega) (by omega) input tape [true] index layout.colors.bits [false]
    (ColorPass.colorWords data.colors) (lower i) (by decide) hi (by decide) s ss h7 h88
    cfg.one cfg.index cfg.colors cfg.bitClock (by simpa only [addressValue_bits,addressValue,Bool.toNat_true] using rep)
  refine ⟨cost,t,?_,he,by simpa [ColorPass.colorWords,Vector.get,Fin.cast] using tw,
    ts,t7,tm,cfg.of_frame (Frame.of_except (by simp [Private,DoublingInit.Private,DoublingPass.Private]) tf),tf⟩
  have hb := IncidencePass.array_cost_le [true] index layout.colors.bits [false] (budget layout index)
    (by simp only [List.length_cons,List.length_nil]; dsimp [budget]; omega) (by dsimp [budget]; omega) (by dsimp [budget]; omega)
    (by simp only [List.length_cons,List.length_nil]; dsimp [budget]; omega) (by dsimp [budget,addressValue]; omega)
  norm_num [addressValue] at hcost
  have hpositive : 1≤(budget layout index+1)^2 := by
    have hp : 0<(budget layout index+1)^2 := by positivity
    omega
  nlinarith

end Maxwell.Cost.ChildPermutation
