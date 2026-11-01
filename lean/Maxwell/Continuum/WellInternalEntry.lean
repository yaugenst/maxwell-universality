import Maxwell.Continuum.WellStrengthPassState

/-! The internal-vertex entry computes the degree-two target, writes its
rounded strength, and restores the shared canonical parameter bank. -/
namespace Maxwell.Continuum.RationalDataflow.WellInternalEntry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open WellStrengthPass
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def code : Code := .seq (WellTarget.writeCode .internal) WellStrengthReset.code

def part (P : ℕ) (v : ℕ→Parts) : Parts :=
  Parts.literal (WellStrength.numerator P (v 1).value (WellTarget.target .internal v):ℚ)

def costBound (P B M : ℕ) : ℕ :=
  2^184*(P+B+16)^2+2^20*(M+5)^2+11*operationCost (P+4096*B+4179)+1

theorem executes {J P B M boundary : ℕ} (a : PartArray.Table J) (i : Fin J)
    (config : Configuration a P B M boundary) (hindex : i.val.bits.length ≤ M)
    (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hB : 4 ≤ B) (hP : (2^P).bits.length ≤ B) (width : WidthBank WellStrength.bank B v)
    (good : Good WellStrength.bank v) (scale : (v 4).value ≠ 0)
    (denominator : (v 1).value+WellTarget.target .internal v ≠ 0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : State a P v i.val s) :
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ costBound P B M ∧
      State (a.set i (part P v)) P v i.val t ∧
      t.val.memory=a.writeMemory i (part P v) s.val.memory ∧
      (part P v).Width (addressValue a.width) ∧
      (∀k,300 ≤ k→k<1000→t.val.tapes k=s.val.tapes k) := by
  have fit : P+4096*B+4179 ≤ addressValue a.width := by have := config.fit;omega
  obtain ⟨c0,u,e0,hc0,r0,g0,w0,value0,table0,memory0,clean0,power0,index0,_,_,_,keep0⟩ :=
    WellTarget.write_executes a .internal P B M hB hP v width good scale denominator i i.val.bits
      (addressValue_bits i.val) hindex config.metadata fit config.separated input tape s state.rational
      state.clean state.power state.table state.outputIndex
  have parametersWidth : ∀k∈WellStrengthReset.parameters,(WellTarget.output .internal P v k).Width B := by
    intro k hk
    rw [WellStrengthReset.target_preserves _ _ _ k (WellStrengthReset.parameter_not_target k hk)]
    apply width
    simp only [WellStrengthReset.parameters,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨c1,t,e1,hc1,r1,_,_,f1⟩ := WellStrengthReset.executes _ (P+4096*B+4179) B
    (by omega) (by omega) w0 g0 parametersWidth input tape u r0
  rw [WellStrengthReset.reset_target,canonical] at r1
  have table1 := table0.rounded_frame r1 (f1.mono (RoundedInteger.arithmetic_workspace_subset WellStrength.bank))
  change WellTarget.output .internal P v 0=part P v at value0
  rw [value0] at table1 memory0
  have partWidth : (part P v).Width (addressValue a.width) := by
    rw [←value0]
    exact (w0 0 (by decide)).mono fit
  refine ⟨c0+c1,t,e0.seq e1,by unfold costBound;omega,
    ⟨r1,clean0.arithmetic_frame f1,word_of_eq (f1.tapes 144 (outside_workspace _ _ (by decide))) power0,
      table1,word_of_eq (f1.tapes 999 (outside_workspace _ _ (by decide))) index0⟩,
    f1.memory.trans memory0,partWidth,?_⟩
  intro k hk hk'
  exact (f1.tapes k (outside_workspace _ _ (Or.inr ⟨by omega,hk'⟩))).trans (keep0 k hk hk')

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellInternalEntry
