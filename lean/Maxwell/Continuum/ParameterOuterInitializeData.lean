import Maxwell.Continuum.ParameterOuterLoop
import Maxwell.Continuum.ParameterOuterInitialMachine

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

def powerSetup : List NatAssign.Instruction := [.literal 530 2,.literal 531 8,.copy 2206 534]
def finishSetup : List NatAssign.Instruction :=
  [.copy 532 2220,.copy 533 2221,.literal 2222 1,.literal 2223 2,.literal 2224 8,
    .literal 2225 4,.literal 2226 slowDivisor]
def powerIds : Finset ℕ := DynamicPower.ids∪{534}
def seedValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.overlay OuterInitial.ids (OuterInitial.result v) v
def powerInputs (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values powerSetup (seedValues v)
def powerResult (N : ℕ) : ℕ→ℕ := Function.update (DynamicPower.values 2 8 N) 534 0
def poweredValues (v : ℕ→ℕ) : ℕ→ℕ :=
  NatAssign.overlay powerIds (powerResult (initialExponent (v 2201) (v 2200))) (powerInputs v)
def initializedValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finishSetup (poweredValues v)
def seedWidth (v : ℕ→ℕ) (B : ℕ) : ℕ := max B (OuterInitial.searchWidth v B)+4
def initialWidth (v : ℕ→ℕ) (B : ℕ) : ℕ :=
  max (seedWidth v B) (DynamicPower.width (initialExponent (v 2201) (v 2200)) (seedWidth v B))+1025
def initializeCode : Code := .seq OuterInitial.code (.seq (NatAssign.code powerSetup)
  (.seq PowerMachine.code (NatAssign.code finishSetup)))
def initializeCost (v : ℕ→ℕ) (B : ℕ) : ℕ := OuterInitial.costBound v B+
  (3000*8^powerSetup.length*(seedWidth v B+2)^2+
    (PowerMachine.costBound (initialExponent (v 2201) (v 2200)) (seedWidth v B)+
      3000*8^finishSetup.length*(initialWidth v B+2)^2))

theorem powerSetup_valid : ∀a∈powerSetup,a.Valid ids := by
  simp [powerSetup,NatAssign.Instruction.Valid,ids,Compare.ids,extra,DynamicPower.ids]
theorem finishSetup_valid : ∀a∈finishSetup,a.Valid ids := by
  simp [finishSetup,NatAssign.Instruction.Valid,ids,Compare.ids,extra,DynamicPower.ids]

theorem powerInputs_fields (v : ℕ→ℕ) :
    powerInputs v 530=2 ∧ powerInputs v 531=8 ∧
    powerInputs v 534=initialExponent (v 2201) (v 2200) := by
  simp [powerInputs,powerSetup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,seedValues,NatAssign.overlay,OuterInitial.result,Rational.after,Rational.common,
    show 2206∈OuterInitial.ids by decide +kernel]

theorem initialized_core (v : ℕ→ℕ) :
    Core (dataOf v) (initialExponent (v 2201) (v 2200)) (initializedValues v) := by
  have keep (i : ℕ) (hi : 2210 ≤ i ∧ i ≤ 2219) : initializedValues v i=v i := by
    have ho : i∉OuterInitial.ids := by
      simp only [OuterInitial.ids,GeometricAdapter.ids,Rational.ids,OuterInitial.extra,Geometric.extra,Rational.common,
        Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton];omega
    have hp : i∉powerIds := by simp only [powerIds,DynamicPower.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton];omega
    unfold initializedValues
    rw [NatAssign.values_preserves finishSetup _ i (by simp [finishSetup,NatAssign.Instruction.target];omega)]
    rw [show poweredValues v i=powerInputs v i from NatAssign.overlay_outside _ _ _ hp]
    unfold powerInputs
    rw [NatAssign.values_preserves powerSetup _ i (by simp [powerSetup,NatAssign.Instruction.target];omega)]
    exact NatAssign.overlay_outside _ _ _ ho
  constructor
  · have span : (fun j:Fin 3=>initializedValues v (2217+j.val))=(fun j:Fin 3=>v (2217+j.val)) := by
      funext j;apply keep;have := j.isLt;omega
    simp only [dataOf,keep 2210 (by decide),keep 2211 (by decide),keep 2212 (by decide),
      keep 2213 (by decide),keep 2214 (by decide),keep 2215 (by decide),keep 2216 (by decide),span]
  · simp [initializedValues,finishSetup,poweredValues,powerInputs,powerSetup,seedValues,
      NatAssign.overlay,powerIds,DynamicPower.ids,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,OuterInitial.result,Rational.after,Rational.common,
      show 2206∈OuterInitial.ids by decide +kernel]
  all_goals simp [initializedValues,finishSetup,poweredValues,powerResult,NatAssign.overlay,
    powerIds,DynamicPower.ids,DynamicPower.values,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,stageLength]

#print axioms initialized_core
end Maxwell.Continuum.Parameters.OuterMachine
