import Maxwell.Continuum.ProfileBufferArithmetic

/-! Actual construction of the two profile-buffer headers and unary clocks.
The underlying memory may contain arbitrary bits. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] runtimeBudget bufferWidth

def allocationCode : Code := .seq allocationArithmeticCode
  (.seq (Calibration.WidthClock.code 704 216 215) (Calibration.WidthClock.code 708 216 205))
def allocationWorkspace : Finset ℕ := allocationArithmeticWorkspace∪{205,215,216}
def clockCost (W : ℕ) : ℕ := (W+1)*(13*W.bits.length+21)+21*W.bits.length+4*W+31
def allocationCost (N D B : ℕ) : ℕ := allocationArithmeticCost B+
  (clockCost (runtimeBudget N)+clockCost (bufferWidth N D))

theorem allocationClock_bank {N D heap : ℕ} {s t : Store}
    (b : NatAssign.Bank allocationIds (bufferAddressValues N D heap) s.val)
    {x : ℕ} (hx : x=205 ∨ x=215) (f : BinaryPrecision.Frame {216,x} s.val t.val) :
    NatAssign.Bank allocationIds (bufferAddressValues N D heap) t.val := by
  intro i hi
  apply word_of_eq (f.tapes i _) (b i hi)
  simp only [allocationIds,bufferIds,bufferHeaderIds,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  omega

theorem allocation_executes (N D heap B : ℕ) (hN : N.bits.length≤B)
    (hD : D.bits.length≤B) (hh : heap.bits.length≤B) (hB : 501≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds (bufferInput N D heap) s.val)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216) :
    ∃cost t,Executes input tape allocationCode cost s t ∧ cost≤allocationCost N D B ∧
      (memoryTable D (runtimeBudget N) heap (runtimeBudget_parameters N).1 s.val.memory).OutputReady t ∧
      (memoryTable D (bufferWidth N D) (secondBufferBase N D heap)
        (by unfold bufferWidth encodedTableWidth correctionWorkingWidth;omega) s.val.memory).Ready t ∧
      NatAssign.Bank allocationIds (bufferAddressValues N D heap) t.val ∧
      Blank t.val 216 ∧ BinaryPrecision.Frame allocationWorkspace s.val t.val := by
  have z : NatAssign.Scratch s.val := by
    intro i hi;interval_cases i <;> first | exact hz.1 | exact hz.2.1 | exact hz.2.2.1 | exact hz.2.2.2.1
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := allocation_arithmetic_executes N D heap B hN hD hh hB input tape s hs z
  have w0 : Word s0.val 704 (runtimeBudget N) := by
    simpa [bufferAddressValues_eq,bufferWidthValues_eq,bufferBudgetValues_eq] using b0 704 (by decide)
  obtain ⟨c1,s1,e1,hc1,_,z1,clock1,f1⟩ := Calibration.WidthClock.executes 704 216 215
    (by decide) (by decide) (by decide) input tape (runtimeBudget N).bits s0 w0
    (blank_of_eq (f0.tapes 216 (by decide)) h216) (blank_of_eq (f0.tapes 215 (by decide)) h215)
  have b1 := allocationClock_bank b0 (Or.inr rfl) f1
  have w1 : Word s1.val 708 (bufferWidth N D) := by
    simpa [bufferAddressValues_eq,bufferWidthValues_eq] using b1 708 (by decide)
  obtain ⟨c2,t,e2,hc2,_,z2,clock2,f2⟩ := Calibration.WidthClock.executes 708 216 205
    (by decide) (by decide) (by decide) input tape (bufferWidth N D).bits s1 w1 z1
    (blank_of_eq (f1.tapes 205 (by decide)) (blank_of_eq (f0.tapes 205 (by decide)) h205))
  have b2 := allocationClock_bank b1 (Or.inl rfl) f2
  have frame : BinaryPrecision.Frame allocationWorkspace s.val t.val :=
    (f0.mono (by unfold allocationWorkspace;exact Finset.subset_union_left)).trans
      ((f1.mono (by decide)).trans (f2.mono (by decide)))
  have zt : BankArray.Scratch t.val := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact blank_of_eq (f2.tapes 0 (by decide)) (blank_of_eq (f1.tapes 0 (by decide)) (z0 0 (by decide)))
    · exact blank_of_eq (f2.tapes 1 (by decide)) (blank_of_eq (f1.tapes 1 (by decide)) (z0 1 (by decide)))
    · exact blank_of_eq (f2.tapes 2 (by decide)) (blank_of_eq (f1.tapes 2 (by decide)) (z0 2 (by decide)))
    · exact blank_of_eq (f2.tapes 3 (by decide)) (blank_of_eq (f1.tapes 3 (by decide)) (z0 3 (by decide)))
    · exact blank_of_eq (frame.tapes 5 (by decide)) hz.2.2.2.2.1
    · exact blank_of_eq (frame.tapes 6 (by decide)) hz.2.2.2.2.2.1
    · exact blank_of_eq (frame.tapes 8 (by decide)) hz.2.2.2.2.2.2.1
    · exact blank_of_eq (frame.tapes 9 (by decide)) hz.2.2.2.2.2.2.2
  have seven := blank_of_eq (frame.tapes 7 (by decide)) h7
  have packing := blank_of_eq (frame.tapes 37 (by decide)) h37
  have wa (i : ℕ) (hi : i∈allocationIds) := b2 i hi
  have ao := memoryTable_outputReady D (runtimeBudget N) heap (runtimeBudget_parameters N).1 t zt seven packing
    (by simpa [bufferAddressValues_eq] using wa 210 (by decide))
    (by simpa [bufferAddressValues_eq] using wa 212 (by decide))
    (by simpa [bufferAddressValues_eq] using wa 213 (by decide))
    (by simpa [bufferAddressValues_eq] using wa 214 (by decide))
    (by simpa only [addressValue_bits] using BankArray.word_of_eq (f2.tapes 215 (by decide)) clock1)
  have bi := memoryTable_ready D (bufferWidth N D) (secondBufferBase N D heap)
    (by unfold bufferWidth encodedTableWidth correctionWorkingWidth;omega) t zt seven
    (by simpa [bufferAddressValues_eq] using wa 200 (by decide))
    (by simpa [bufferAddressValues_eq] using wa 202 (by decide))
    (by simpa [bufferAddressValues_eq] using wa 203 (by decide))
    (by simpa [bufferAddressValues_eq] using wa 204 (by decide))
    (by simpa only [addressValue_bits] using clock2)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,?_,?_,b2,z2,frame⟩
  · simp only [addressValue_bits] at hc1 hc2
    unfold allocationCost clockCost
    omega
  · simpa only [frame.memory] using ao
  · simpa only [frame.memory] using bi

#print axioms allocation_executes
end Maxwell.Continuum.Profile.Runtime
