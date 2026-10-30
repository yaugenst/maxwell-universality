import Maxwell.Continuum.SourceRoutingArrayMachine
import Maxwell.Continuum.NaturalBankDivMod
import Maxwell.Cost.Structured.Rename

/-! Fixed arithmetic on the geometry controls. Division uses a private
fifth scratch tape and therefore preserves the source parser's tape 4. -/

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def controls : Finset ℕ := Finset.Icc 1200 1239
def ids : Finset ℕ := controls∪NaturalQuotient.workPorts
def work : Finset ℕ := {0,1,2,3,1249}∪ids
def relocation : Equiv.Perm ℕ := Equiv.swap 4 1249
def divisionCode (source divisor quotient remainder : ℕ) : Code :=
  .call ((NaturalDivMod.code source divisor quotient remainder).compile.renameTapes relocation)

theorem ids_lower (i : ℕ) (hi : i∈ids) : 40 ≤ i := by
  simp only [ids,controls,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega
theorem ids_fixed (i : ℕ) (hi : i∈ids) : relocation i=i := by
  apply Equiv.swap_apply_of_ne_of_ne
  all_goals simp only [ids,controls,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  all_goals omega

theorem ready_of_frame {s t : BitRAMState} (hs : GeometryArray.Ready s)
    (hz : NatAssign.Scratch t) (hf : BinaryPrecision.Frame work s t) : GeometryArray.Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37} : Finset ℕ)) : t.tapes i=s.tapes i := by
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) hs.scratch.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) hs.scratch.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) hs.scratch.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) hs.scratch.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) hs.seven,
    RationalAccumulator.blank_of_eq (keep 37 (by decide)) hs.pack⟩

theorem scratch {s : BitRAMState} (hs : GeometryArray.Ready s) : NatAssign.Scratch s := by
  intro i hi
  interval_cases i
  · exact hs.scratch.1
  · exact hs.scratch.2.1
  · exact hs.scratch.2.2.1
  · exact hs.scratch.2.2.2.1

theorem stage (instructions : List NatAssign.Instruction)
    (valid : ∀a∈instructions,a.Valid ids) (v : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈ids,(v i).bits.length ≤ B) (literal : ∀a∈instructions,a.literalWidth ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val) :
    ∃steps t,Executes input tape (NatAssign.code instructions) steps s t ∧
      steps ≤ 3000*8^instructions.length*(B+2)^2 ∧
      NatAssign.Bank ids (NatAssign.values instructions v) t.val ∧ GeometryArray.Ready t.val ∧
      BinaryPrecision.Frame ({0,1,2,3}∪ids) s.val t.val := by
  obtain ⟨steps,t,he,hcost,bt,zt,ft⟩:=NatAssign.executes ids
    (fun i hi => by have h:=ids_lower i hi;omega) instructions valid v input tape s bank (scratch ready)
  have changed : NatAssign.changes instructions⊆({0,1,2,3}∪ids : Finset ℕ) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · obtain ⟨a,ha,he⟩:=List.mem_map.mp (List.mem_toFinset.mp hi)
      have target : a.target∈ids := by
        have h:=valid a ha
        cases a <;> simp only [NatAssign.Instruction.Valid,NatAssign.Instruction.target] at h ⊢
        · exact h
        · exact h.2.1
        · exact h.2.1
        · exact h.2.1
      exact Finset.mem_union_right _ (he ▸ target)
  have frame := ft.mono changed
  have wide : BinaryPrecision.Frame work s.val t.val := frame.mono (by
    intro i hi
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto)
  exact ⟨steps,t,he,hcost.trans (NatAssign.price_bound ids instructions valid v B width literal),
    bt,ready_of_frame ready zt wide,frame⟩

@[simp] theorem relocation_symm : relocation.symm=relocation := Equiv.symm_swap _ _
theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (relocation i) := by
  simp only [Store.renameTapes,BitRAMState.renameTapes,relocation_symm,Function.comp_apply]

theorem divisionFrame {s t : Store}
    (hf : BinaryPrecision.Frame ({0,1,2,3,4}∪ids) (s.renameTapes relocation.symm).val t.val) :
    BinaryPrecision.Frame work s.val (t.renameTapes relocation).val := by
  refine ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,?_⟩
  intro i hi
  have hn:=hi
  simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hn
  by_cases h4 : i=4
  · subst i
    exact hf.tapes 1249 (by decide)
  · have fixed : relocation i=i := Equiv.swap_apply_of_ne_of_ne h4 hn.1.2.2.2.2
    have h:=hf.tapes i (by
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨⟨hn.1.1,hn.1.2.1,hn.1.2.2.1,hn.1.2.2.2.1,h4⟩,hn.2⟩)
    simpa only [relocation_symm,renamed_tape,fixed] using h

theorem divide (source divisor quotient remainder : ℕ)
    (hsource : source∈controls) (hdivisor : divisor∈controls)
    (hquotient : quotient∈controls) (hremainder : remainder∈controls) (hne : quotient≠remainder)
    (v : ℕ→ℕ) (zero : ∀i∈NaturalQuotient.workPorts,v i=0) (positive : 0<v divisor)
    (B : ℕ) (width : ∀i∈ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : NatAssign.Bank ids v s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (divisionCode source divisor quotient remainder) steps s t ∧
      steps ≤ 2^100*(B+2)^2+1 ∧
      NatAssign.Bank ids (Function.update (Function.update v quotient (v source/v divisor))
        remainder (v source%v divisor)) t.val ∧ GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      BinaryPrecision.Frame work s.val t.val := by
  have port (i : ℕ) (hi : i∈controls) : i∈ids := Finset.mem_union_left _ hi
  have outside (i : ℕ) (hi : i∈controls) : i∉NaturalQuotient.workPorts := by
    simp only [controls,Finset.mem_Icc] at hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton]
    omega
  have ba : NatAssign.Bank ids v (s.renameTapes relocation.symm).val := by
    intro i hi
    apply RationalAccumulator.word_of_eq _ (bank i hi)
    rw [relocation_symm,renamed_tape,ids_fixed i hi]
  have za : ∀i,i<5→Blank (s.renameTapes relocation.symm).val i := by
    intro i hi
    by_cases h4 : i=4
    · subst i;exact privateBlank
    · apply RationalAccumulator.blank_of_eq _ (scratch ready i (by omega))
      rw [relocation_symm,renamed_tape]
      exact congrArg s.val.tapes (Equiv.swap_apply_of_ne_of_ne h4 (by omega))
  obtain ⟨steps,u,he,hcost,bu,zu,fu⟩:=NaturalDivMod.executes ids
    (fun i hi => by have h:=ids_lower i hi;omega) Finset.subset_union_right
    source divisor quotient remainder (port _ hsource) (port _ hdivisor) (port _ hquotient) (port _ hremainder)
    (outside _ hsource) (outside _ hdivisor) (outside _ hquotient) (outside _ hremainder)
    hne v zero positive B width input tape (s.renameTapes relocation.symm) ba za
  let t:=u.renameTapes relocation
  have frame:=divisionFrame fu
  have bt : NatAssign.Bank ids (Function.update (Function.update v quotient (v source/v divisor))
        remainder (v source%v divisor)) t.val := by
    intro i hi
    exact RationalAccumulator.word_of_eq ((renamed_tape u i).trans (congrArg u.val.tapes (ids_fixed i hi))) (bu i hi)
  have zt : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq _ (zu i (by omega))
    exact (renamed_tape u i).trans (congrArg u.val.tapes
      (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)))
  refine ⟨steps+1,t,?_,by omega,bt,ready_of_frame ready zt frame,zu 4 (by decide),frame⟩
  simpa only [divisionCode,Store.renameTapes_symm] using he.renamed_call relocation

#print axioms stage
#print axioms divide
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
