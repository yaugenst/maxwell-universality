import Maxwell.Continuum.ProfileEndpointExecution
import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! The read-only endpoint pass preserves the output buffer, runtime
dyadic scale, and shared division workspace. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

def endpointProtected : List ℕ := [4,37,144,661,210,212,213,214,215,220,221,222,223]

theorem endpoint_protects : endpointProtected.all (fun i => endpointProgram.protectsTape i)=true := by decide
theorem endpoint_protects_memory : endpointProgram.protectsMemory=true := by decide

theorem endpoint_keep {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape endpointProgram cost s t) (i : ℕ) (hi : i∈endpointProtected) :
    t.val.tapes i=s.val.tapes i := e.protectsTape i (List.all_eq_true.mp endpoint_protects i hi)

theorem endpoint_shared_ready {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape endpointProgram cost s t) {v w : ℕ→Parts}
    (h : SharedConversion.Ready dftRegisters v s) (hr : Ready dftRegisters w t) :
    SharedConversion.Ready dftRegisters w t := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact hr.1 i hi
    · have mem : i∈endpointProtected := by
        simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
        simp only [endpointProtected,List.mem_cons,List.not_mem_nil,or_false]
        tauto
      have old := h.1 i (Finset.mem_union_right _ hi)
      rw [SharedConversion.work_values_zero v i hi] at old
      rw [SharedConversion.work_values_zero w i hi]
      exact RationalAccumulator.word_of_eq (endpoint_keep e i mem) old
  · intro i hi
    by_cases hlt : i<4
    · exact hr.2 i hlt
    · have he : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (endpoint_keep e 4 (by simp [endpointProtected])) (h.2 4 (by decide))

theorem endpoint_output_ready {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape endpointProgram cost s t) {n m : ℕ}
    {a : PartArray.Table n} {b : PartArray.Table m} (hb : b.OutputReady s) (ha : a.Ready t) :
    b.OutputReady t := by
  apply hb.transfer (e.protectsMemory endpoint_protects_memory) _ ha.scratch ha.seven
  intro i hi
  apply endpoint_keep e i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  simp only [endpointProtected,List.mem_cons,List.not_mem_nil,or_false]
  tauto

#print axioms endpoint_shared_ready
#print axioms endpoint_output_ready
end Maxwell.Continuum.Profile.Runtime
