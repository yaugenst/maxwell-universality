import Maxwell.Continuum.FourierTensorModeFootprint
import Maxwell.Cost.Structured.Determinism

/-! The row allocator retains its actual address words. The result is
derived from the same terminating execution, without a second allocation. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def allocationValues (M L R P : ℕ) (a : Table (2*aliasArraySize R)) : ℕ→ℕ :=
  Profile.Runtime.CacheAllocation.outputValues
    (values M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator))

theorem allocated_stored {p cost : ℕ} (M L R P W H : ℕ) (hW : 5≤W)
    (a : Table (2*aliasArraySize R)) (old : Table p)
    (hw : InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) W) (hm : old.MetadataWidth H)
    (input : List Bool) (tape : ℕ→Bool) (s t : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hz : NatAssign.Scratch s.val) (ha : a.Ready s) (ho : old.OutputReady s) (hz216 : Blank s.val 216)
    (e : Executes input tape allocatedCode cost s t) :
    NatAssign.Bank Profile.Runtime.CacheAllocation.inputs (allocationValues M L R P a) t.val ∧
      (∀i∈Profile.Runtime.CacheAllocation.inputs,
        (allocationValues M L R P a i).bits.length≤2^8*(2^32*(W+1)+1)) := by
  cases e with
  | seq first second =>
    obtain ⟨c0,u,e0,_,b0,w0,z0,f0⟩ := executes M L R P _ _ _ _ W hW hw input tape s hb hz
    have same0 := first.deterministic e0
    rw [same0.2] at second
    let vals := values M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)
    have source0 := setup_table_frame ha f0 z0
    have target0 : old.OutputReady u := by
      apply ho.transfer f0.memory _ source0.scratch source0.seven
      intro i hi
      apply f0.tapes
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [setupChanged,Finset.mem_insert,Finset.mem_singleton]
      omega
    have bank0 : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs vals u.val :=
      fun i hi => b0 i ((by decide : Profile.Runtime.CacheAllocation.inputs⊆ids) hi)
    have width0 : ∀i∈Profile.Runtime.CacheAllocation.inputs,(vals i).bits.length≤2^32*(W+1) :=
      fun i hi => w0 i ((by decide : Profile.Runtime.CacheAllocation.inputs⊆ids) hi)
    have positive : 0<vals 726 := by
      rw [show vals 726=slotWidth M L R P from values_width _ _ _ _ _ _ _ _]
      exact slotWidth_pos M L R P
    obtain ⟨c1,v,e1,_,_,_,b1,w1,_,_⟩ := Profile.Runtime.CacheAllocation.executes a old vals
      (2^32*(W+1)) H positive width0 hm
      input tape u bank0 source0 target0 (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) hz216)
    have same1 := second.deterministic e1
    rw [same1.2]
    exact ⟨fun i hi => b1 i (Finset.mem_union_left _ hi),
      fun i hi => w1 i (Finset.mem_union_left _ hi)⟩

theorem power_preserves_allocation {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape DyadicFloor.StoredPower.powerCode cost s t)
    (i : ℕ) (hi : i∈Profile.Runtime.CacheAllocation.inputs) : t.val.tapes i=s.val.tapes i := by
  exact e.outsideTapes (by decide : DyadicFloor.StoredPower.powerCode.outsideTapes 725 729=true)
    i (Finset.mem_Icc.mp hi).1 (by have := (Finset.mem_Icc.mp hi).2;omega)

theorem generated_stored {p cost : ℕ} (M L R P W H : ℕ) (hW : 5≤W)
    (a : Table (2*aliasArraySize R)) (old : Table p) (j : Fin 3)
    (hw : InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) W) (hm : old.MetadataWidth H)
    (input : List Bool) (tape : ℕ→Bool) (s t : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hz : NatAssign.Scratch s.val) (ha : a.Ready s) (ho : old.OutputReady s) (hz216 : Blank s.val 216)
    (e : Executes input tape (generatedCode j) cost s t) :
    NatAssign.Bank Profile.Runtime.CacheAllocation.inputs (allocationValues M L R P a) t.val ∧
      (∀i∈Profile.Runtime.CacheAllocation.inputs,
        (allocationValues M L R P a i).bits.length≤2^8*(2^32*(W+1)+1)) := by
  cases e with
  | seq first rest =>
    obtain ⟨bank,width⟩ := allocated_stored M L R P W H hW a old hw hm input tape s _ hb hz ha ho hz216 first
    cases rest with
    | seq power rows =>
      refine ⟨?_,width⟩
      intro i hi
      have hir : i∈ModePrepare.retainedPorts := by
        have bounds := Finset.mem_Icc.mp hi
        simp only [ModePrepare.retainedPorts,Finset.mem_union,Finset.mem_insert,
          Finset.mem_singleton,Finset.mem_Icc]
        omega
      exact RationalAccumulator.word_of_eq
        ((ModePrepare.table_executes_retained rows i hir).trans (power_preserves_allocation power i hi)) (bank i hi)

theorem generated_precision {cost : ℕ} (M L R P W : ℕ) (hW : 5≤W)
    (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (hw : InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) W)
    (input : List Bool) (tape : ℕ→Bool) (s t : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hz : NatAssign.Scratch s.val) (h144 : Blank s.val 144) (h146 : Blank s.val 146)
    (e : Executes input tape (generatedCode j) cost s t) : Word t.val 145 P := by
  cases e with
  | seq allocated rest =>
    cases allocated with
    | seq setup allocate =>
      obtain ⟨c,u,run,_,bank,_,_,_⟩ := executes M L R P _ _ _ _ W hW hw input tape s hb hz
      have same := setup.deterministic run
      rw [same.2] at allocate
      have word := bank 145 (by simp [ids])
      rw [values_precision] at word
      have word' := RationalAccumulator.word_of_eq
        (allocate.protectsTape 145 (by decide)) word
      cases rest with
      | seq power rows =>
        have z144 := RationalAccumulator.blank_of_eq
          ((allocate.protectsTape 144 (by decide)).trans (run.protectsTape 144 (by decide))) h144
        have z146 := RationalAccumulator.blank_of_eq
          ((allocate.protectsTape 146 (by decide)).trans (run.protectsTape 146 (by decide))) h146
        obtain ⟨c1,v,e1,_,precision,_,_,_⟩ := DyadicFloor.StoredPower.power_executes P input tape _ word' z146 z144
        have same1 := power.deterministic e1
        rw [same1.2] at rows
        exact RationalAccumulator.word_of_eq
          (ModePrepare.table_executes_retained rows 145 (by simp [ModePrepare.retainedPorts])) precision

theorem generated_middle {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {cost : ℕ} {s t : Store} (e : Executes input tape (generatedCode j) cost s t)
    (i : ℕ) (hlo : 600 ≤ i) (hhi : i<725) : t.val.tapes i=s.val.tapes i := by
  have syntactic : (generatedCode j).outsideTapes 600 725=true := by
    fin_cases j <;> decide
  exact e.outsideTapes syntactic i hlo hhi

#print axioms generated_stored
#print axioms generated_precision
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
