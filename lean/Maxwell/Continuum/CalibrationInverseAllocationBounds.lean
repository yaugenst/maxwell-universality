import Maxwell.Continuum.CalibrationInverseDescriptorInputs
import Maxwell.Continuum.CalibrationNeumannCopyWidths

/-! The actual wider allocation has bounded headers and is disjoint from
the raw table whenever its heap starts beyond the raw table's last channel. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.Allocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000

theorem table_metadata (n width heap : ℕ) (hw : 0<width) (memory : ℕ → Bool)
    (haddress : heap.bits.length+2*n.bits.length+width.bits.length+10≤width) :
    (table n width heap hw memory).MetadataWidth width := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [table]
    omega
  · dsimp [table]
    omega
  · exact (layout_address_bits n width heap (tableSize n) (by unfold tableSize; nlinarith)).trans haddress
  · have h := layout_address_bits n width heap (2*tableSize n) (by unfold tableSize; nlinarith)
    simpa only [table,Nat.mul_assoc] using h.trans haddress
  · simp only [table,List.length_replicate,le_refl]

theorem table_disjoint {m n : ℕ} (a : PartArray.Table (tableSize m)) (rawHeap width heap : ℕ)
    (hc : SourceLayout a rawHeap) (hw : 0<width) (memory : ℕ → Bool)
    (hheap : rawHeap+3*tableSize m*addressValue a.width≤heap) :
    a.SeparatedFrom (table n width heap hw memory) := by
  simp only [Nat.mul_assoc] at hheap
  simp only [PartArray.Table.SeparatedFrom,table,hc.positive,hc.negative,hc.denominator,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,addressValue_bits,
    IncidenceEncoding.Separated,Nat.mul_assoc]
  exact ⟨⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,
    ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,
    ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩⟩

#print axioms table_metadata
#print axioms table_disjoint

end Maxwell.Continuum.Calibration.NeumannMachine.Allocation
