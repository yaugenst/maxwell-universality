import Maxwell.Continuum.RationalDataflowResetInvariant
import Maxwell.Continuum.WellOriginalWrite
import Maxwell.Continuum.WellMediatorWrite

/-! The strength loop retains only its calibrated midpoint, common scale,
and three couplings. All per-entry work is reset by actual literal writes. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrengthReset
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def parameters : Finset ℕ := {1,4,5,6,7}
def targets : List ℕ := [0,2,3,8,9,10,11,12,13,14,15]
def canonical (v : ℕ→Parts) : ℕ→Parts := (resetList targets).evaluate v
def code : Code := (resetList targets).code

theorem targets_valid : ∀i∈targets,i∈WellStrength.bank := by decide

theorem retained_parameter (i : ℕ) (hi : i∈WellStrength.bank) (ht : i∉targets) :
    i∈parameters := by
  simp only [WellStrength.bank,Finset.mem_range] at hi
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false,not_or] at ht
  simp only [parameters,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem canonical_width (v : ℕ→Parts) (B : ℕ) (hB : 1 ≤ B)
    (hp : ∀i∈parameters,(v i).Width B) : WidthBank WellStrength.bank B (canonical v) :=
  resetList_result_width WellStrength.bank targets v B hB
    (fun i hi ht=>hp i (retained_parameter i hi ht))

theorem canonical_good (v : ℕ→Parts) (hg : Good WellStrength.bank v) :
    Good WellStrength.bank (canonical v) :=
  resetList_result_good WellStrength.bank targets v (fun i hi _=>hg i hi)

theorem canonical_parameter (v : ℕ→Parts) (i : ℕ) (hi : i∈parameters) : canonical v i=v i := by
  rw [canonical,resetList_values,ite_eq_right]
  simp only [parameters,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

theorem parameter_not_target (i : ℕ) (hi : i∈parameters) : i∉targets := by
  simp only [parameters,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

theorem canonical_idempotent (v : ℕ→Parts) : canonical (canonical v)=canonical v := by
  apply resetList_congr
  intro i hi
  simp only [canonical,resetList_values,hi,ite_false]

theorem canonical_natural_channels (v : ℕ→Parts) :
    (canonical v 8).negative=0 ∧ (canonical v 8).denominator=1 ∧
    (canonical v 9).negative=0 ∧ (canonical v 9).denominator=1 := by
  simp [canonical,resetList_values,targets,Parts.literal]

theorem target_preserves (k : WellTarget.Kind) (P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i∉targets) :
    WellTarget.output k P v i=v i := by
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  cases k <;>
    simp (disch := omega) [WellTarget.output,WellTarget.control,WellTarget.original,
      WellTarget.internal,WellTarget.mediator,WellStrength.values,WellStrength.prepared,
      WellStrength.reciprocal,NearestInteger.values,NearestInteger.prepared,NearestInteger.loaded,
      NearestInteger.tail,Control.evaluate,Instruction.update]

theorem reset_target (k : WellTarget.Kind) (P : ℕ) (v : ℕ→Parts) :
    canonical (WellTarget.output k P v)=canonical v :=
  resetList_congr targets _ _ (target_preserves k P v)

theorem reset_original (P : ℕ) (v : ℕ→Parts) (diagonal degree : ℕ) :
    canonical (WellOriginalWrite.output P v diagonal degree)=canonical v := by
  rw [WellOriginalWrite.output,reset_target]
  apply resetList_congr
  intro i hi
  apply WellSourceRead.pairValues_preserves
  all_goals
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    omega

theorem reset_mediator (P : ℕ) (v : ℕ→Parts) :
    canonical (WellMediatorWrite.output P v)=canonical v := by
  rw [WellMediatorWrite.output,reset_target]
  apply resetList_congr
  intro i hi
  apply WellAxisMachine.preserves
  all_goals
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    omega

theorem original_parameter (P : ℕ) (v : ℕ→Parts) (diagonal degree i : ℕ) (hi : i∈parameters) :
    WellOriginalWrite.output P v diagonal degree i=v i := by
  rw [WellOriginalWrite.output,target_preserves _ _ _ i (parameter_not_target i hi)]
  apply WellSourceRead.pairValues_preserves
  all_goals
    simp only [parameters,Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem mediator_parameter (P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i∈parameters) :
    WellMediatorWrite.output P v i=v i := by
  rw [WellMediatorWrite.output,target_preserves _ _ _ i (parameter_not_target i hi)]
  apply WellAxisMachine.preserves
  all_goals
    simp only [parameters,Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem executes (v : ℕ→Parts) (U B : ℕ) (hU : 1 ≤ U) (hB : 1 ≤ B)
    (hv : WidthBank WellStrength.bank U v) (hg : Good WellStrength.bank v)
    (hp : ∀i∈parameters,(v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready WellStrength.bank v s) :
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ 11*operationCost U+1 ∧
      Ready WellStrength.bank (canonical v) t ∧ WidthBank WellStrength.bank B (canonical v) ∧
      Good WellStrength.bank (canonical v) ∧ BinaryPrecision.Frame (workspace WellStrength.bank) s.val t.val := by
  obtain ⟨cost,t,ex,hc,r,f⟩ := resetList_executes WellStrength.bank targets targets_valid v U hU hv hg
    input tape s hr
  exact ⟨cost,t,ex,hc,r,canonical_width v B hB hp,canonical_good v hg,f⟩

#print axioms reset_original
#print axioms reset_mediator
#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellStrengthReset
