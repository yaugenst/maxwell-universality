import Maxwell.Continuum.PhaseRuntimeSetup

/-! The fixed Machin program is instantiated on the precision computed by
the phase setup. Stored rational operands are restored afterward. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def afterMachinValues (a b Q N i : ℕ) : ℕ :=
  if i∈Machin.allIds then Machin.finalValues (Calibration.phaseBits Q N) i else setupValues a b Q N i
def restore : List NatAssign.Instruction := [.copy 650 630,.copy 651 631]
def seedValues (a b Q N : ℕ) : ℕ→ℕ := NatAssign.values restore (afterMachinValues a b Q N)
def machinCode : Code := .seq Machin.Runtime.program (NatAssign.code restore)
def machinWidth (Q N W : ℕ) : ℕ := Machin.finalWidth (Calibration.phaseBits Q N)+2^19*(W+1)+1
def machinCost (Q N W : ℕ) : ℕ :=
  Machin.Runtime.costBound (Calibration.phaseBits Q N)+2^20*(machinWidth Q N W+2)^2

theorem setupValues_machin_zero (a b Q N i : ℕ) (hi : i∈Machin.allIds) : setupValues a b Q N i=0 := by
  have hilo : 610 ≤ i ∧ i≤627 := by
    simp only [Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  simp [setupValues_eq,scannedValues,initialValues,show i≠630 by omega,show i≠655 by omega,
    show i≠654 by omega,show i≠650 by omega,show i≠651 by omega,show i≠652 by omega,show i≠653 by omega]

theorem machin_executes (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (setupValues a b Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape machinCode cost s t ∧ cost≤machinCost Q N W ∧
      NatAssign.Bank ids (seedValues a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have hm : NatAssign.Bank Machin.allIds (fun _ => 0) s.val := by
    intro i hi
    simpa only [setupValues_machin_zero a b Q N i hi] using
      hs i ((show Machin.allIds⊆ids by decide) hi)
  have haux : Machin.Runtime.InputReady (Calibration.phaseBits Q N) s.val := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa only [setupValues_precision] using hs 630 (by decide)
    · simpa [setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using hs 619 (by decide)
    · simpa [setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using hs 628 (by decide)
    · simpa [setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using hs 631 (by decide)
    · simpa [setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using hs 632 (by decide)
    · simpa [setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using hs 633 (by decide)
  obtain ⟨c0,u,e0,h0,bu,zu,aux,fu⟩ := Machin.Runtime.program_executes (Calibration.phaseBits Q N)
    input tape s hm hz haux
  have full : NatAssign.Bank ids (afterMachinValues a b Q N) u.val := by
    intro i hi
    by_cases hm : i∈Machin.allIds
    · simpa only [afterMachinValues,ite_eq_left hm] using bu i hm
    by_cases h619 : i=619
    · subst i
      simpa [afterMachinValues,hm,setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using aux.index
    by_cases h628 : i=628
    · subst i
      simpa [afterMachinValues,hm,setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using aux.two
    by_cases h631 : i=631
    · subst i
      simpa [afterMachinValues,hm,setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using aux.terms
    by_cases h632 : i=632
    · subst i
      simpa [afterMachinValues,hm,setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using aux.count
    by_cases h633 : i=633
    · subst i
      simpa [afterMachinValues,hm,setupValues_eq,scannedValues,initialValues,zero_word_iff_blank] using aux.six
    have hout : i∉Machin.Runtime.fullWorkspace := by
      have h4 := ids_ge i hi
      simp only [Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hm
      simp only [Machin.Runtime.fullWorkspace,Machin.Runtime.workspace,Machin.allWorkspace,
        Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    simpa only [afterMachinValues,ite_eq_right hm] using word_of_eq (fu.tapes i hout) (hs i hi)
  have hvalid : ∀j∈restore,j.Valid ids := by
    simp [restore,NatAssign.Instruction.Valid,ids,extras,PhaseMachine.allIds,PhaseMachine.ids]
  have hw : ∀i∈ids,(afterMachinValues a b Q N i).bits.length≤machinWidth Q N W := by
    intro i hi
    unfold afterMachinValues
    split_ifs with hm
    · exact (Machin.finalValues_width _ i hm).trans (by unfold machinWidth;omega)
    · exact (setupValues_width a b Q N W i hi ha hb hQ hN hW).trans (by unfold machinWidth;omega)
  obtain ⟨c1,t,e1,h1,bt,zt,ft⟩ := NatAssign.executes ids ids_ge restore hvalid
    (afterMachinValues a b Q N) input tape u full zu
  have hp := NatAssign.price_bound ids restore hvalid (afterMachinValues a b Q N) (machinWidth Q N W)
    hw (by simp [restore,NatAssign.Instruction.literalWidth])
  have hc1 : c1≤2^20*(machinWidth Q N W+2)^2 := h1.trans (hp.trans (by
    change 3000*8^2*(machinWidth Q N W+2)^2≤2^20*(machinWidth Q N W+2)^2
    exact Nat.mul_le_mul_right _ (by norm_num)))
  exact ⟨c0+c1,t,e0.seq e1,by unfold machinCost;omega,bt,zt,
    (fu.mono (by decide)).trans (ft.mono (by decide))⟩

theorem seedValues_core (a b Q N i : ℕ) (hi : i∈PhaseMachine.allIds) :
    seedValues a b Q N i=PhaseMachine.fullSeed a b Q N i := by
  have hilo : i≤631 := by
    simp only [PhaseMachine.allIds,PhaseMachine.ids,RationalTaylor.ids,RationalMagnitude.ids,
      Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  by_cases h630 : i=630
  · subst i
    simp [seedValues,restore,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,afterMachinValues,
      Machin.allIds,RationalArctan.ids,setupValues_eq,scannedValues,initialValues,
      PhaseMachine.fullSeed,PhaseMachine.initialValues]
  by_cases h631 : i=631
  · subst i
    simp [seedValues,restore,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,afterMachinValues,
      Machin.allIds,RationalArctan.ids,setupValues_eq,scannedValues,initialValues,
      PhaseMachine.fullSeed,PhaseMachine.initialValues]
  simp only [seedValues,restore,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne h630,Function.update_of_ne h631]
  unfold afterMachinValues PhaseMachine.fullSeed
  split_ifs
  · rfl
  · simp [setupValues_eq,scannedValues,initialValues,PhaseMachine.initialValues,h630,h631,
      show i≠655 by omega,show i≠654 by omega,show i≠650 by omega,show i≠651 by omega,
      show i≠652 by omega,show i≠653 by omega]

#print axioms machin_executes
#print axioms seedValues_core
end Maxwell.Continuum.PhaseMachine.Runtime
