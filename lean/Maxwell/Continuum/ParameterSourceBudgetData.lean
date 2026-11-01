import Maxwell.Continuum.ParameterSourceWords
import Maxwell.Continuum.ParameterMaster
import Maxwell.Cost.Structured.NatAssign.FixedPower

/-! Literal natural operands for the continuum search are computed from
retained source counts and the actual geometry size. Promise exponents are
fixed program parameters, while all source-dependent values are read. -/
namespace Maxwell.Continuum.Parameters.SourceBudgetMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

/-- Inputs: source dimension, nonzero count, circuit size, routing side, and
emitted well count. -/
def inputs : Finset ℕ := Finset.Icc 2300 2304
def extra : Finset ℕ := Finset.Icc 2300 2340
def outputs : Finset ℕ := {2201,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219}
def ids : Finset ℕ := extra∪outputs

def powers (κ η : ℕ) : List NatAssign.Instruction :=
  NatAssign.powerInstructions 2301 2310 (κ+1)++NatAssign.powerInstructions 2301 2311 η

def conditionInstructions : List NatAssign.Instruction :=
  [.literal 2315 9,.literal 2317 256,.literal 2318 1024,
   .copy 2303 2321,.multiply 2318 2321,
   .copy 2321 2322,.multiply 2321 2322,
   .copy 2302 2324,.multiply 2302 2324,
   .copy 2324 2325,.multiply 2324 2325,
   .multiply 2310 2325,.multiply 2317 2325,.add 2321 2325,
   .copy 2322 2326,.multiply 2315 2326,.multiply 2325 2326]

def errorInstructions : List NatAssign.Instruction :=
  [.literal 2312 1,.literal 2314 4,.literal 2316 16,.literal 2320 2048,
   .copy 2302 2330,.add 2312 2330,
   .copy 2330 2331,.multiply 2330 2331,.add 2312 2331,
   .multiply 2314 2331,.multiply 2300 2331,
   .copy 2303 2332,.multiply 2320 2332,.add 2312 2332,.multiply 2332 2331,
   .copy 2301 2333,.multiply 2301 2333,.multiply 2333 2331,
   .multiply 2311 2331,.multiply 2316 2331]

def outputInstructions (e : ℕ) : List NatAssign.Instruction :=
  [.literal 2201 (minimumLengthExponent e),.literal 2210 (2^e),
   .copy 2301 2211,.copy 2304 2212,.copy 2326 2213,.literal 2214 1,.literal 2215 1,
   .copy 2331 2216,.literal 2319 (2^54*129),.copy 2303 2217,.multiply 2319 2217,
   .copy 2217 2218,.copy 2217 2219]

def instructions (κ η e : ℕ) : List NatAssign.Instruction :=
  powers κ η++conditionInstructions++errorInstructions++outputInstructions e

def condition (m circuit side κ : ℕ) : ℕ :=
  9*(1024*side)^2*(256*m^(κ+1)*circuit^4+1024*side)
def errorDen (n m circuit side η : ℕ) : ℕ :=
  16*m^η*(4*n*((circuit+1)^2+1)*(1+2048*side)*m^2)

theorem condition_values (v : ℕ→ℕ) :
    NatAssign.values conditionInstructions v 2326=
      9*(1024*v 2303)^2*(256*v 2310*(v 2302)^4+1024*v 2303) := by
  simp [conditionInstructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]
  ring

theorem error_values (v : ℕ→ℕ) :
    NatAssign.values errorInstructions v 2331=
      16*v 2311*(4*v 2300*((v 2302+1)^2+1)*(1+2048*v 2303)*(v 2301)^2) := by
  simp [errorInstructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]
  ring

theorem condition_preserves (v : ℕ→ℕ) (i : ℕ)
    (hi : i∈inputs ∨ i=2310 ∨ i=2311) : NatAssign.values conditionInstructions v i=v i := by
  apply NatAssign.values_preserves
  intro a ha
  simp only [conditionInstructions,List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [inputs,Finset.mem_Icc] at hi
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [NatAssign.Instruction.target];omega

theorem error_preserves (v : ℕ→ℕ) (i : ℕ)
    (hi : i∈inputs ∨ i=2326) : NatAssign.values errorInstructions v i=v i := by
  apply NatAssign.values_preserves
  intro a ha
  simp only [errorInstructions,List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [inputs,Finset.mem_Icc] at hi
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [NatAssign.Instruction.target];omega

#print axioms condition_values
#print axioms error_values
end Maxwell.Continuum.Parameters.SourceBudgetMachine
