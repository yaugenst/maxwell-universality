import Maxwell.Continuum.CalibrationNeumannCopyPrepare

/-! Automatic descriptor and buffer-header word bounds for the concrete
copy allocation. These concern actual unreduced machine words. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2500000

private theorem values_width (ids : Finset ℕ) (p : List NatAssign.Instruction)
    (hp : ∀ a ∈ p, a.Valid ids) (v : ℕ → ℕ) (B : ℕ)
    (hw : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (hl : ∀ a ∈ p, a.literalWidth ≤ B) :
    ∀ i ∈ ids, (NatAssign.values p v i).bits.length ≤ 2^p.length*(B+1) := by
  induction p generalizing v B with
  | nil =>
    intro i hi
    simpa only [NatAssign.values,List.length_nil,pow_zero,one_mul] using (hw i hi).trans (by omega)
  | cons a p ih =>
    have h := ih (fun b hb => hp b (by simp [hb])) (a.update v) (2*B+1)
      (NatAssign.instruction_width ids a (hp a (by simp)) v B hw (hl a (by simp)))
      (fun b hb => (hl b (by simp [hb])).trans (by omega))
    intro i hi
    simpa only [NatAssign.values,List.length_cons,pow_succ,
      show 2*B+1+1=2*(B+1) by ring,Nat.mul_assoc] using h i hi

theorem CopyPlan.output_width (v : ℕ → ℕ) (B : ℕ)
    (hw : ∀ i ∈ CopyPlan.ids, (v i).bits.length ≤ B) :
    ∀ i ∈ Descriptors.ids,
      (NatAssign.values CopyPlan.plan v i).bits.length ≤ 2^CopyPlan.plan.length*(B+1) := by
  intro i hi
  exact values_width CopyPlan.ids CopyPlan.plan CopyPlan.valid v B hw
    (by simp [CopyPlan.plan,NatAssign.Instruction.literalWidth]) i (Finset.mem_insert_of_mem hi)

theorem copyTarget_metadata {n : ℕ} (a : PartArray.Table (tableSize n)) (heap B : ℕ)
    (memory : ℕ → Bool) (ha : a.MetadataWidth B)
    (haddress : heap.bits.length+2*n.bits.length+(addressValue a.width).bits.length+10 ≤ B) :
    (copyTarget a heap memory).MetadataWidth B := by
  refine ⟨ha.width,?_,?_,?_,ha.clock⟩
  · exact (layout_address_bits n (addressValue a.width) heap (3*tableSize n)
      (by unfold tableSize; nlinarith)).trans haddress
  · exact (layout_address_bits n (addressValue a.width) heap (4*tableSize n)
      (by unfold tableSize; nlinarith)).trans haddress
  · exact (layout_address_bits n (addressValue a.width) heap (5*tableSize n)
      (by unfold tableSize; nlinarith)).trans haddress

#print axioms CopyPlan.output_width
#print axioms copyTarget_metadata

end Maxwell.Continuum.Calibration.NeumannMachine
