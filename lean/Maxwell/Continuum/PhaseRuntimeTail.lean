import Maxwell.Continuum.PhaseRuntimeFinalData
import Maxwell.Continuum.PhaseRuntimePreparation

/-! Fixed phase tail: exact argument preparation, four-cycle Taylor
evaluation, and restoration of the runtime countdown and index words. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def tail (negative : Bool) (base : RationalTaylor.Runtime.Cycle) : Code :=
  .seq preparation (RationalTaylor.Runtime.cleanProgram (fractionCycle negative base) 655)
def tailCost (Q N W : ℕ) : ℕ := preparationCost Q N W+
  RationalTaylor.Runtime.cleanCost (PhaseMachine.order Q N) (fullWorkWidth Q N W) (PhaseMachine.order Q N).bits.length

theorem preparation_full (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (seedValues a b Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape preparation cost s t ∧ cost≤preparationCost Q N W ∧
      NatAssign.Bank ids (preparedValues a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have hs' : NatAssign.Bank PhaseMachine.allIds (fullSeed a b Q N) s.val := by
    intro i hi
    simpa only [seedValues_core a b Q N i hi] using hs i (Finset.mem_union_left _ hi)
  obtain ⟨c,t,e,hc,bt,zt,ft⟩ := preparation_executes a b Q N W ha hb input tape s hs' hz
  refine ⟨c,t,e,hc,?_,zt,ft.mono (by decide)⟩
  intro i hi
  by_cases ho : i∈PhaseMachine.allIds
  · simpa only [preparedValues,ite_eq_left ho] using bt i ho
  · have hout : i∉PhaseMachine.allWorkspace := by
      have h4 := ids_ge i hi
      simp only [PhaseMachine.allWorkspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      exact not_or_intro (by omega) ho
    simpa only [preparedValues,ite_eq_right ho] using word_of_eq (ft.tapes i hout) (hs i hi)

theorem tail_executes (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (seedValues a b Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (tail negative base) cost s t ∧ cost≤tailCost Q N W ∧
      NatAssign.Bank ids (finalValues negative base a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,u,e0,h0,bu,zu,fu⟩ := preparation_full a b Q N W ha hb input tape s hs hz
  have coreBank : NatAssign.Bank PhaseMachine.allIds (fullPrepared a b Q N) u.val := by
    intro i hi
    simpa only [preparedValues,ite_eq_left hi] using bu i (Finset.mem_union_left _ hi)
  have word : Word u.val 655 (PhaseMachine.order Q N) := by
    simpa only [preparedValues_order] using bu 655 (by decide)
  obtain ⟨origin,hword⟩ := word
  have h607 : Blank u.val 607 := by
    simpa only [(preparedValues_indices a b Q N).1,zero_word_iff_blank] using bu 607 (by decide)
  have h608 : Blank u.val 608 := by
    simpa only [(preparedValues_indices a b Q N).2,zero_word_iff_blank] using bu 608 (by decide)
  obtain ⟨c1,t,e1,h1,bt,zt,zcount,z607,z608,ft⟩ := RationalTaylor.Runtime.clean_extended
    PhaseMachine.allIds (by decide) (fractionCycle negative base) 655 (PhaseMachine.order Q N)
    (fullWorkWidth Q N W) (by decide) (by decide) (by
      intro i hi hn
      have h4 := PhaseMachine.allIds_ge i hi
      have h655 : i≠655 := by intro h;subst i;exact (show 655∉PhaseMachine.allIds by decide) hi
      have h607' : i≠607 := by intro h;subst i;exact (show 607∉PhaseMachine.allIds by decide) hi
      have h608' : i≠608 := by intro h;subst i;exact (show 608∉PhaseMachine.allIds by decide) hi
      simp only [RationalTaylor.ids,Finset.mem_insert,Finset.mem_singleton] at hn
      simp only [RationalTaylor.Runtime.loopWorkspace,RationalTaylor.Runtime.workspace,RationalTaylor.workspace,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega) (fullPrepared a b Q N) (by unfold fullWorkWidth;omega)
    (fun i hi => fullPrepared_width a b Q N W ha hb i ((show RationalTaylor.ids⊆PhaseMachine.allIds by decide) hi))
    input tape (PhaseMachine.order Q N).bits origin u (addressValue_bits _) hword coreBank zu h607 h608
  rw [fractionCycle_signs] at bt
  change NatAssign.Bank PhaseMachine.allIds (fullFinal negative (RationalTaylor.Runtime.cycleSigns base) a b Q N) t.val at bt
  refine ⟨c0+c1,t,e0.seq e1,by unfold tailCost;omega,?_,zt,fu.trans (ft.mono (by decide))⟩
  intro i hi
  by_cases ho : i∈PhaseMachine.allIds
  · simpa only [finalValues,ite_eq_left ho] using bt i ho
  by_cases h655 : i=655
  · subst i
    simpa only [finalValues,ite_eq_right ho,ite_true,zero_word_iff_blank] using zcount
  by_cases h607' : i=607
  · subst i
    simpa [finalValues,ho,seedValues_extra a b Q N 607 (by decide),setupValues_eq,
      scannedValues,initialValues,zero_word_iff_blank] using z607
  by_cases h608' : i=608
  · subst i
    simpa [finalValues,ho,seedValues_extra a b Q N 608 (by decide),setupValues_eq,
      scannedValues,initialValues,zero_word_iff_blank] using z608
  have hout : i∉RationalTaylor.Runtime.loopWorkspace 655 := by
    have h4 := ids_ge i hi
    have hn : i∉RationalTaylor.ids := fun hx => ho ((show RationalTaylor.ids⊆PhaseMachine.allIds by decide) hx)
    simp only [RationalTaylor.ids,Finset.mem_insert,Finset.mem_singleton] at hn
    simp only [RationalTaylor.Runtime.loopWorkspace,RationalTaylor.Runtime.workspace,RationalTaylor.workspace,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  simpa only [finalValues,preparedValues,ite_eq_right ho,ite_eq_right h655] using
    word_of_eq (ft.tapes i hout) (bu i hi)

#print axioms tail_executes
end Maxwell.Continuum.PhaseMachine.Runtime
