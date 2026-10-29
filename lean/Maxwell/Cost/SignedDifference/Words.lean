import Maxwell.Cost.Subtraction
import Maxwell.Cost.Arithmetic.Words
import Maxwell.Cost.Multiplication.Tapes

namespace Maxwell.Cost.Subtraction

theorem words (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (xo yo zo : ℤ)
    (hpc : s.pc = 0) (hx : s.tapes 0 = BitTape.shifted xs xo)
    (hy : s.tapes 1 = BitTape.shifted ys yo)
    (hz : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ t, PricedSteps (program.next input tape) (20 * max xs.length ys.length + 9) s t ∧
      t.pc = 19 ∧ t.registers 2 = (result false xs ys).2 ∧
      t.tapes 0 = {BitTape.shifted xs xo with head := xo + max xs.length ys.length} ∧
      t.tapes 1 = {BitTape.shifted ys yo with head := yo + max xs.length ys.length} ∧
      t.tapes 2 = BitTape.shiftedEnd (result false xs ys).1 zo ∧
      rippleFrame t = rippleFrame s := by
  obtain ⟨t, hs, hp, hb, hw, ht0, ht1, hf⟩ := simulation input tape s xs ys hpc
    (hx ▸ BitTape.shifted_represents xs xo) (hy ▸ BitTape.shifted_represents ys yo)
  refine ⟨t, hs, hp, hb, ?_, ?_, hw.blank hz, hf⟩
  · simpa [hx, BitTape.shifted] using ht0
  · simpa [hy, BitTape.shifted] using ht1

def swapOperands : Equiv.Perm ℕ := Equiv.swap 0 1

def swappedProgram : BitRAM := program.renameTapes swapOperands

@[simp] theorem swapOperands_zero : swapOperands 0 = 1 := by simp [swapOperands]
@[simp] theorem swapOperands_one : swapOperands 1 = 0 := by simp [swapOperands]
@[simp] theorem swapOperands_two : swapOperands 2 = 2 := by decide
@[simp] theorem swapOperands_symm : swapOperands.symm = swapOperands := by rfl

@[simp] theorem swapState_twice (s : BitRAMState) :
    (s.renameTapes swapOperands).renameTapes swapOperands = s := by
  simp [BitRAMState.renameTapes, Function.comp_def, swapOperands]

theorem swapped_words (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (xo yo zo : ℤ)
    (hpc : s.pc = 0) (hx : s.tapes 0 = BitTape.shifted xs xo)
    (hy : s.tapes 1 = BitTape.shifted ys yo)
    (hz : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ t, PricedSteps (swappedProgram.next input tape) (20 * max ys.length xs.length + 9) s t ∧
      t.pc = 19 ∧ t.registers 2 = (result false ys xs).2 ∧
      t.tapes 0 = {BitTape.shifted xs xo with head := xo + max ys.length xs.length} ∧
      t.tapes 1 = {BitTape.shifted ys yo with head := yo + max ys.length xs.length} ∧
      t.tapes 2 = BitTape.shiftedEnd (result false ys xs).1 zo ∧
      rippleFrame t = rippleFrame s := by
  obtain ⟨t, hs, hp, hb, ht0, ht1, ht2, hf⟩ := words input tape (s.renameTapes swapOperands)
    ys xs yo xo zo hpc
    (by simpa [BitRAMState.renameTapes] using hy)
    (by simpa [BitRAMState.renameTapes] using hx)
    (by simpa [BitRAMState.renameTapes] using hz)
  have hsteps := hs.renameTapes swapOperands
  rw [swapState_twice] at hsteps
  refine ⟨t.renameTapes swapOperands, hsteps, hp, hb, ?_, ?_, ?_, ?_⟩
  · simpa [BitRAMState.renameTapes] using ht1
  · simpa [BitRAMState.renameTapes] using ht0
  · simpa [BitRAMState.renameTapes] using ht2
  · simpa [rippleFrame, BitRAMState.renameTapes, Function.comp_def,
      swapOperands, Equiv.swap_apply_of_ne_of_ne] using hf

end Maxwell.Cost.Subtraction
