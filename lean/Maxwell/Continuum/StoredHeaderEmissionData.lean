import Maxwell.Continuum.StoredHeaderPlan
import Maxwell.Continuum.NaturalSignedEmission
import Maxwell.Cost.RationalCanonical.StoredList

/-! The complete header serializer has one relocated energy operand and
otherwise fixed source/selector ports. No output bits occur in its code. -/
namespace Maxwell.Continuum.StoredHeader
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def retained (energyPort : ℕ) : Finset ℕ := {energyPort,energyPort+1,energyPort+2,4707,4708,4506,4510}
def emissionInputs (energyPort : ℕ) : Finset ℕ := inputs∪retained energyPort
def emissionIds (energyPort : ℕ) : Finset ℕ := ids∪retained energyPort
def emissionWork : Finset ℕ := work∪RationalCanonical.StoredEmission.work
def fractions (energyPort : ℕ) : List (ℕ×ℕ×ℕ) :=
  [(energyPort,energyPort+1,energyPort+2),(732,731,730),(4707,731,4708)]
def detuningCode : Code := .seq (EmitNatural.code 4506) (EmitNonnegative.code 4510)
def code (energyPort : ℕ) : Code := .seq prepareCode
  (.seq StoredNatural.continuumHeaderCode
    (.seq (RationalCanonical.StoredEmission.listCode (fractions energyPort)) detuningCode))
def bits (energyPort : ℕ) (v : ℕ→ℕ) : List Bool :=
  StoredNatural.bits StoredNatural.continuumHeaderPorts (prepared v)++
    RationalCanonical.StoredEmission.listBits (fractions energyPort) (prepared v)++
    (Codec.nat (v 4506)++Codec.int (v 4510:ℤ))
def emissionWidth (B : ℕ) : ℕ := max (prepareWidth B) B
def workspaceWidth (B H : ℕ) : ℕ := max H (emissionWidth B+1)
def emissionCost (B H J : ℕ) : ℕ := prepareCost B H+160*emissionWidth B+193+
  (3*RationalCanonical.StoredEmission.costBound (emissionWidth B) (workspaceWidth B J)+1)+40*B+52

theorem retained_outside (energyPort : ℕ) (h : 733 ≤ energyPort) (i : ℕ) (hi : i∈retained energyPort) :
    i∉work := by
  simp only [retained,Finset.mem_insert,Finset.mem_singleton] at hi
  simp only [work,outputs,outputList,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  omega

theorem emission_naturals (energyPort : ℕ) :
    ∀i∈StoredNatural.continuumHeaderPorts,i∈emissionIds energyPort := by
  intro i hi
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  simp only [StoredNatural.continuumHeaderPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  simp only [outputs,outputList,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem fraction_ports (energyPort : ℕ) (a : ℕ×ℕ×ℕ) (ha : a∈fractions energyPort) :
    a.1∈emissionIds energyPort ∧a.2.1∈emissionIds energyPort ∧a.2.2∈emissionIds energyPort := by
  simp only [fractions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl <;>
    simp [emissionIds,ids,inputs,outputs,outputList,retained]

theorem detuning_executes (v : ℕ→ℕ) (B : ℕ)
    (pw : (v 4506).bits.length ≤ B) (nw : (v 4510).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 4506 (v 4506)) (numerator : Word s.val 4510 (v 4510)) :
    ∃cost t,Executes input tape detuningCode cost s t ∧cost ≤ 40*B+52 ∧
      t.val.output=(Codec.nat (v 4506)++Codec.int (v 4510:ℤ)).reverse++s.val.output ∧
      EmitNatural.Frame s t := by
  obtain ⟨origin,hp⟩:=precision
  obtain ⟨a,ea,oa,fa⟩:=EmitNatural.executes 4506 (v 4506) origin input tape s hp
  obtain ⟨t,et,ot,ft⟩:=EmitNonnegative.executes 4510 (v 4510) input tape a
    (word_of_eq (congrFun fa.2.2.2.2 4510) numerator)
  refine ⟨_,t,ea.seq et,by omega,?_,ft.1.trans fa.1,ft.2.1.trans fa.2.1,
    ft.2.2.1.trans fa.2.2.1,ft.2.2.2.1.trans fa.2.2.2.1,ft.2.2.2.2.trans fa.2.2.2.2⟩
  rw [ot,oa]
  simp only [List.reverse_append,List.append_assoc]

#print axioms detuning_executes
end Maxwell.Continuum.StoredHeader
