import Maxwell.Continuum.FourierTensorModeGenerated
import Maxwell.Continuum.ProgramTapeInterval

/-! The row loop preserves the already computed allocation words and
the disjoint registers used by the following tensor traversal. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536

def retainedPorts : Finset ℕ := {350,351,352,354,355,356,357,358,360,361,362,
  710,711,725,726,727,728,145,146,216}∪Finset.Icc 1084 1110

theorem tableCode_retained (j : Fin 3) :
    ∀i∈retainedPorts,(tableCode j).protectsTape i=true := by
  have middle : (tableCode j).outsideTapes 330 1000=true := by
    fin_cases j <;> decide
  have upper : (tableCode j).outsideTapes 1084 1111=true := by
    fin_cases j <;> decide
  have special : ∀i∈({145,146,216}:Finset ℕ),(tableCode j).protectsTape i=true := by
    fin_cases j <;> decide
  intro i hi
  have ranges : (330 ≤ i ∧ i<1000) ∨ (1084 ≤ i ∧ i<1111) ∨ i∈({145,146,216}:Finset ℕ) := by
    simp only [retainedPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_Icc] at hi
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  rcases ranges with hm|hu|hs
  · exact Code.outsideTapes_protects middle hm.1 hm.2
  · exact Code.outsideTapes_protects upper hu.1 hu.2
  · exact special i hs

theorem table_executes_retained {input : List Bool} {tape : ℕ→Bool} {j : Fin 3}
    {cost : ℕ} {s t : Store} (h : Executes input tape (tableCode j) cost s t)
    (i : ℕ) (hi : i∈retainedPorts) : t.val.tapes i=s.val.tapes i :=
  h.protectsTape i (tableCode_retained j i hi)

#print axioms tableCode_retained
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
