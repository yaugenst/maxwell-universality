import Maxwell.Continuum.ProfileBufferPlan

/-! The computed profile buffers occupy disjoint memory intervals. Their
contents are read from the actual initial memory and need no initialization. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] runtimeBudget bufferWidth

theorem bufferAddressValues_eq (N D heap i : ℕ) : bufferAddressValues N D heap i=
    if i=210 then runtimeBudget N else if i=212 then heap
    else if i=213 then heap+D*runtimeBudget N else if i=214 then heap+2*D*runtimeBudget N
    else if i=200 then bufferWidth N D else if i=202 then secondBufferBase N D heap
    else if i=203 then secondBufferBase N D heap+D*bufferWidth N D
    else if i=204 then secondBufferBase N D heap+2*D*bufferWidth N D
    else if i=709 then bufferHeapEnd N D heap else bufferWidthValues N D heap i := by
  by_cases h : i∈({200,202,203,204,210,212,213,214,706,709} : Finset ℕ)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [bufferAddressValues,bufferAddressPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,
        bufferWidthValues_eq,bufferBudgetValues_eq,bufferInput,secondBufferBase,bufferHeapEnd] <;> ring
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [bufferAddressValues,values_unchanged bufferAddressPlan _ i (by
      simp [bufferAddressPlan,NatAssign.Instruction.target]
      omega)]
    simp only [ite_eq_right h.1,ite_eq_right h.2.1,ite_eq_right h.2.2.1,
      ite_eq_right h.2.2.2.1,ite_eq_right h.2.2.2.2.1,ite_eq_right h.2.2.2.2.2.1,
      ite_eq_right h.2.2.2.2.2.2.1,ite_eq_right h.2.2.2.2.2.2.2.1,
      ite_eq_right h.2.2.2.2.2.2.2.2.2]

theorem memoryTable_separated (n width heap : ℕ) (hw : 0<width) (memory : ℕ→Bool) :
    (memoryTable n width heap hw memory).Separated := by
  simp only [PartArray.Table.Separated,memoryTable,addressValue_bits,
    IncidenceEncoding.Separated]
  have he : 2*n*width=n*width+n*width := by ring
  rw [he]
  exact ⟨Or.inl le_rfl,Or.inl (by omega),Or.inl (by omega)⟩

theorem memoryTable_separatedFrom (n m width width' heap heap' : ℕ)
    (hw : 0<width) (hw' : 0<width') (memory : ℕ→Bool)
    (hheap : heap+3*n*width≤heap') :
    (memoryTable n width heap hw memory).SeparatedFrom
      (memoryTable m width' heap' hw' memory) := by
  intro x hx y hy
  simp only [memoryTable,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp only [memoryTable,addressValue_bits,IncidenceEncoding.Separated] <;>
    left <;> nlinarith only [hheap,Nat.zero_le (n*width),Nat.zero_le (m*width')]

theorem memoryTable_metadata (n width heap B : ℕ) (hw : 0<width)
    (memory : ℕ→Bool) (hwidth : width≤B)
    (hbase : heap.bits.length+n.bits.length+width.bits.length+4≤B) :
    (memoryTable n width heap hw memory).MetadataWidth B := by
  have small : width.bits.length≤width := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have product := bits_mul_le n width
  have twice := bits_mul_le 2 n
  have twiceProduct := bits_mul_le (2*n) width
  have add := bits_add_le heap (n*width)
  have addTwice := bits_add_le heap (2*n*width)
  rw [show (2:ℕ).bits.length=2 from rfl] at twice
  refine ⟨small.trans hwidth,?_,?_,?_,?_⟩
  · change heap.bits.length≤B;omega
  · change (heap+n*width).bits.length≤B;omega
  · change (heap+2*n*width).bits.length≤B;omega
  · simpa only [memoryTable,List.length_replicate] using hwidth

theorem memoryTable_ready (n width heap : ℕ) (hw : 0<width) (s : Store)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hwidth : Word s.val 200 width) (hp : Word s.val 202 heap)
    (hn : Word s.val 203 (heap+n*width)) (hd : Word s.val 204 (heap+2*n*width))
    (hc : BankArray.Word s.val 205 (List.replicate width false)) :
    (memoryTable n width heap hw s.val.memory).Ready s := by
  refine ⟨hz,h7,hwidth,hp,hn,hd,hc,?_,?_,?_⟩ <;>
    simpa only [memoryTable,addressValue_bits] using
      Calibration.NeumannMachine.memoryWords_represents s.val.memory _ width n

theorem memoryTable_outputReady (n width heap : ℕ) (hw : 0<width) (s : Store)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hwidth : Word s.val 210 width) (hp : Word s.val 212 heap)
    (hn : Word s.val 213 (heap+n*width)) (hd : Word s.val 214 (heap+2*n*width))
    (hc : BankArray.Word s.val 215 (List.replicate width false)) :
    (memoryTable n width heap hw s.val.memory).OutputReady s := by
  refine ⟨hz,h7,h37,hwidth,hp,hn,hd,hc,?_,?_,?_⟩ <;>
    simpa only [memoryTable,addressValue_bits] using
      Calibration.NeumannMachine.memoryWords_represents s.val.memory _ width n

#print axioms bufferAddressValues_eq
#print axioms memoryTable_separatedFrom
#print axioms memoryTable_outputReady
end Maxwell.Continuum.Profile.Runtime
