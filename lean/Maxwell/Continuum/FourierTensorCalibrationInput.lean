import Maxwell.Continuum.FourierTensorCalibrationHandoff
import Maxwell.Continuum.FourierTensorZeroInitialization

/-! Transfer the actual normalized calibration table to the Fourier input
header and reinitialize its shared rational workspace. Both headers retain
the same array, and the previously captured material payloads are preserved. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationInput
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def code : Code := .seq CalibrationHandoff.code ZeroInitialization.code

def changed : Finset ℕ := CalibrationHandoff.changed∪workspace RowArithmetic.bank

def cost {n : ℕ} (a : Table n) (H B : ℕ) : ℕ :=
  128*(H+ModeAllocation.tableWidth a+1)+2^128*(B+1)^2

theorem executes {n : ℕ} (a : Table n) (H B : ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (hold : WordCleanup.Bounded CalibrationHandoff.targets H s.val)
    (hwork : WordCleanup.Bounded ZeroInitialization.clearPorts B s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost a H B ∧
      a.Ready t ∧ a.OutputReady t ∧ Ready RowArithmetic.bank ModePrelude.zeroValues t ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,au,ou,f0⟩ := CalibrationHandoff.executes a H input tape s ha hold
  have nextWork : WordCleanup.Bounded ZeroInitialization.clearPorts B u.val := by
    intro i hi
    obtain ⟨xs,hxs,hx⟩ := hwork i hi
    have hw : i∈workspace RowArithmetic.bank := by
      simpa only [ZeroInitialization.clearPorts,Finset.mem_sort] using hi
    have outside : i∉CalibrationHandoff.changed :=
      Finset.disjoint_left.mp (by decide : Disjoint (workspace RowArithmetic.bank) CalibrationHandoff.changed) hw
    exact ⟨xs,hxs,BankArray.word_of_eq (f0.tapes i outside) hx⟩
  obtain ⟨c1,t,e1,hc1,rt,f1⟩ := ZeroInitialization.executes B input tape u nextWork
  have ready := au.arithmetic_frame RowArithmetic.bank f1 rt.2
  have ot : a.OutputReady t := by
    apply ou.transfer f1.memory _ ready.scratch ready.seven
    intro i hi
    apply f1.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,ready,ot,rt,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)⟩

theorem retained {s t : Store} (frame : BinaryPrecision.Frame changed s.val t.val) :
    t.val.tapes 988=s.val.tapes 988 ∧ t.val.tapes 991=s.val.tapes 991 ∧
      t.val.tapes 992=s.val.tapes 992 :=
  ⟨frame.tapes 988 (by decide),frame.tapes 991 (by decide),frame.tapes 992 (by decide)⟩

#print axioms executes
#print axioms retained
end Maxwell.Continuum.Profile.WaveMachine.Runtime.CalibrationInput
