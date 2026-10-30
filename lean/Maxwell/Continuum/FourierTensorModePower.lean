import Maxwell.Continuum.FourierTensorModeAllocated
import Maxwell.Continuum.FourierTensorFrequencyScale
import Maxwell.Continuum.RationalDataflowArrayTransfer
import Maxwell.Continuum.DyadicFloorPowerPreparation

/-! Generation of the actual dyadic rounding scale retains the source
and destination arrays, mode indices, and small rational input bank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem floor_allocated_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame allocatedChanges s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) allocatedChanges) hi)) (h.2 i hi)

theorem frequency_scale_width (M L : ℕ) :
    (FrequencyScaleMachine.result M L).Width (M.bits.length+L.bits.length+2) := by
  have h := RationalAccumulator.bits_mul_le 2 M
  rw [show (2:ℕ).bits.length=2 by decide] at h
  change L.bits.length≤_ ∧ (0:ℕ).bits.length≤_ ∧ (2*M).bits.length≤_
  exact ⟨by omega,by simp,h.trans (by omega)⟩

theorem generated_fit (M A L R P : ℕ) [NeZero M] (a : Table (2*aliasArraySize R))
    (j : Fin 3) (v : ℕ→Parts) (hnorm : (v 0).value=Supercell.physicalFactorApprox M A)
    (hscale : v 1=FrequencyScaleMachine.result M L)
    (hmode : ‖(GlobalPower.tableData R a).value‖≤2)
    (r : Fin (RowArithmetic.rowCount R)) (k : Fin 5) :
    (ModePrepare.fields P R a j r (ModePrepare.canonical v) k).Width (slotWidth M L R P) := by
  apply ModePrepare.fields_width M A P R (M.bits.length+L.bits.length+2) (slotWidth M L R P) a j r
  · simpa only [ModePrepare.canonical,show ¬(2≤0 ∧ 0<28) by decide,ite_false] using hnorm
  · exact hmode
  · simpa only [ModePrepare.canonical,show ¬(2≤1 ∧ 1<28) by decide,ite_false,hscale] using frequency_scale_width M L
  · unfold slotWidth;omega
  · unfold slotWidth;omega

theorem power_executes {n m : ℕ} (a : Table n) (b : Table m) (S : Finset ℕ)
    (v : ℕ→Parts) (R P : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hi : NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) s.val)
    (hc : Word s.val 201 (RowArithmetic.rowCount R))
    (hp : Word s.val 145 P) (hz : DyadicFloor.Clean s.val)
    (h144 : Blank s.val 144) (h146 : Blank s.val 146) :
    ∃cost t,Executes input tape DyadicFloor.StoredPower.powerCode cost s t ∧ cost≤2^10*(P+2)^2 ∧
      RationalDataflow.Ready S v t ∧ a.Ready t ∧ b.OutputReady t ∧
      NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) t.val ∧
      Word t.val 201 (RowArithmetic.rowCount R) ∧ DyadicFloor.Clean t.val ∧
      Word t.val 144 (2^P) ∧ Blank t.val 146 ∧
      BinaryPrecision.Frame {144,146} s.val t.val := by
  obtain ⟨cost,t,e,hcost,_,power,z146,f⟩ := DyadicFloor.StoredPower.power_executes P input tape s hp h146 h144
  have keep (i : ℕ) (h : i≠144 ∧ i≠146) := f.tapes i (by simp [h.1,h.2])
  have scratch : BankArray.Scratch t.val :=
    ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) ha.scratch.1,
     RationalAccumulator.blank_of_eq (keep 1 (by decide)) ha.scratch.2.1,
     RationalAccumulator.blank_of_eq (keep 2 (by decide)) ha.scratch.2.2.1,
     RationalAccumulator.blank_of_eq (keep 3 (by decide)) ha.scratch.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 5 (by decide)) ha.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 6 (by decide)) ha.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 8 (by decide)) ha.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 9 (by decide)) ha.scratch.2.2.2.2.2.2.2⟩
  have seven := RationalAccumulator.blank_of_eq (keep 7 (by decide)) ha.seven
  have source := ha.transfer f.memory (by
    intro i hi;apply keep;simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega) scratch seven
  have target := hb.transfer f.memory (by
    intro i hi;apply keep;simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega) scratch seven
  have ready : RationalDataflow.Ready S v t := by
    refine ⟨?_,?_⟩
    · intro i hi
      have hn : i≠144 ∧ i≠146 := by
        constructor <;> intro he <;> subst i
        · exact outside_workspace S 144 (Or.inr (by omega)) (Finset.mem_union_right _ hi)
        · exact outside_workspace S 146 (Or.inr (by omega)) (Finset.mem_union_right _ hi)
      exact RationalAccumulator.word_of_eq (keep i hn) (hr.1 i hi)
    · intro i hi
      exact RationalAccumulator.blank_of_eq (keep i (by omega)) (hr.2 i hi)
  refine ⟨cost,t,e,hcost,ready,source,target,?_,RationalAccumulator.word_of_eq (keep 201 (by decide)) hc,
    ?_,power,z146,f⟩
  · intro i him
    have bounds := Finset.mem_Icc.mp him
    exact RationalAccumulator.word_of_eq (keep i (by omega)) (hi i him)
  · refine ⟨RationalAccumulator.blank_of_eq (keep 4 (by decide)) hz.1,?_⟩
    intro i him
    have hn : i≠144 ∧ i≠146 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at him
      omega
    exact RationalAccumulator.blank_of_eq (keep i hn) (hz.2 i him)

#print axioms generated_fit
#print axioms power_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
