import Maxwell.Continuum.SourceRoutingPortMachine
import Maxwell.Continuum.SourceRoutingMetadata
import Maxwell.Cost.Structured.Rename

/-! The incidence arithmetic uses its own fifth scratch tape, preserving
the source parser's tape 4. The renaming is fixed before input is read. -/

namespace Maxwell.Cost.RoutingPorts.Complete.PortArithmetic
open Structured Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def relocation : Equiv.Perm ℕ := Equiv.swap 4 753
def privateWork : Finset ℕ := {0,1,2,3,753}∪ids
def privateCode : Code := .call (code.compile.renameTapes relocation)

@[simp] theorem relocation_symm : relocation.symm=relocation := Equiv.symm_swap _ _
theorem relocation_fixed (i : ℕ) (h4 : i≠4) (h753 : i≠753) : relocation i=i :=
  Equiv.swap_apply_of_ne_of_ne h4 h753
theorem ids_fixed (i : ℕ) (hi : i∈ids) : relocation i=i := by
  apply relocation_fixed
  · have := ids_lower i hi
    omega
  · simp only [ids,ports,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
    omega
theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (relocation i) := by
  simp only [Store.renameTapes,BitRAMState.renameTapes,relocation_symm,Function.comp_apply]

theorem private_frame {s t : Store}
    (hf : BinaryPrecision.Frame ({0,1,2,3,4}∪ids) (s.renameTapes relocation.symm).val t.val) :
    BinaryPrecision.Frame privateWork s.val (t.renameTapes relocation).val := by
  refine ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,?_⟩
  intro i hi
  have hi' := hi
  simp only [privateWork,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hi'
  by_cases h4 : i=4
  · subst i
    have hh := hf.tapes 753 (by decide)
    change t.val.tapes 753=s.val.tapes 4 at hh ⊢
    exact hh
  · have hfixed := relocation_fixed i h4 hi'.1.2.2.2.2
    have hh := hf.tapes i (by
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨⟨hi'.1.1,hi'.1.2.1,hi'.1.2.2.1,hi'.1.2.2.2.1,h4⟩,hi'.2⟩)
    simpa only [relocation_symm,renamed_tape,hfixed] using hh

theorem private_executes (v : ℕ→ℕ) (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (hhalf : 0<v 710) (B : ℕ) (hB : 2≤B) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank ids v s.val)
    (hz : Ready s.val) (h753 : Blank s.val 753) :
    ∃steps t, Executes input tape privateCode steps s t ∧ steps≤2^120*(B+2)^2+1 ∧
      NatAssign.Bank ids (output v) t.val ∧ Ready t.val ∧ Blank t.val 753 ∧
      BinaryPrecision.Frame privateWork s.val t.val := by
  let a := s.renameTapes relocation.symm
  have ba : NatAssign.Bank ids v a.val := by
    intro i hi
    apply RationalAccumulator.word_of_eq _ (hs i hi)
    change (s.renameTapes relocation.symm).val.tapes i=s.val.tapes i
    rw [relocation_symm,renamed_tape,ids_fixed i hi]
  have za : ∀i,i<5→Blank a.val i := by
    intro i hi
    interval_cases i
    · exact hz.scratch.1
    · exact hz.scratch.2.1
    · exact hz.scratch.2.2.1
    · exact hz.scratch.2.2.2.1
    · exact h753
  obtain ⟨steps,u,he,hc,bu,zu,fu⟩ := executes v hzero hhalf B hB hw input tape a ba za
  let t := u.renameTapes relocation
  have frame := private_frame fu
  have bt : NatAssign.Bank ids (output v) t.val := by
    intro i hi
    apply RationalAccumulator.word_of_eq _ (bu i hi)
    exact (renamed_tape u i).trans (congrArg u.val.tapes (ids_fixed i hi))
  have zt : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq _ (zu i (by omega))
    exact (renamed_tape u i).trans
      (congrArg u.val.tapes (relocation_fixed i (by omega) (by omega)))
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37,752}:Finset ℕ)) : t.val.tapes i=s.val.tapes i := by
    apply frame.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rcases hz.scratch with ⟨_,_,_,_,h5,h6,h8,h9⟩
  have rt : Ready t.val :=
    ⟨⟨zt 0 (by decide),zt 1 (by decide),zt 2 (by decide),zt 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩,
      RationalAccumulator.blank_of_eq (keep 7 (by decide)) hz.seven,
      RationalAccumulator.blank_of_eq (keep 37 (by decide)) hz.pack,
      RationalAccumulator.blank_of_eq (keep 752 (by decide)) hz.probe⟩
  refine ⟨steps+1,t,?_,by omega,bt,rt,zu 4 (by decide),frame⟩
  simpa only [privateCode,a,Store.renameTapes_symm] using he.renamed_call relocation

#print axioms private_executes

end Maxwell.Cost.RoutingPorts.Complete.PortArithmetic
