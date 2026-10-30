import Maxwell.Continuum.FourierTensorModePreludeData

/-! Actual fixed execution of the physical normalization and rescaled
frequency constants, including square-root scratch cleanup. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

theorem executes (M A L W : ℕ) (hM : 0<M) (hW : 1≤W)
    (hm : M.bits.length≤W) (ha : A.bits.length≤W) (hl : L.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready RowArithmetic.bank zeroValues s) (hz : PhysicalFactorMachine.Clean s.val)
    (wm : Word s.val 350 M) (wa : Word s.val 351 A) (wl : Word s.val 352 L)
    (z353 : Blank s.val 353) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound A W ∧
      Ready RowArithmetic.bank (values M A L) t ∧
      Word t.val 350 M ∧ Word t.val 351 A ∧ Word t.val 352 L ∧ Blank t.val 353 ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,r0,_,m0,a0,f0⟩ := PhysicalFactorMachine.shared_executes
    RowArithmetic.bank 0 M A W zeroValues (by decide) hM (zero_width _ W hW) hm ha
    input tape s hr hz wm wa
  have l0 := RationalAccumulator.word_of_eq (f0.tapes 352 (by decide)) wl
  have zero0 := RationalAccumulator.blank_of_eq (f0.tapes 353 (by decide)) z353
  obtain ⟨c1,t,e1,hc1,r1,m1,l1,z1,f1⟩ := FrequencyScaleMachine.executes RowArithmetic.bank 1 M L
    (factorWidth A W) (factorValues M A) (by decide) (by unfold factorWidth;omega)
    (factorValues_width M A W hm ha) (hm.trans (by unfold factorWidth;omega))
    (hl.trans (by unfold factorWidth;omega)) input tape u r0 m0 l0 zero0
  exact ⟨c0+c1,t,e0.seq e1,(Nat.add_le_add hc0 hc1).trans (cost_bound A W),r1,m1,
    RationalAccumulator.word_of_eq (f1.tapes 351 (by decide)) a0,l1,z1,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)⟩

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
