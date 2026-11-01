import Maxwell.Continuum.ParameterSpacingMachineCost
import Maxwell.Continuum.ParameterBufferMachineCost
import Maxwell.Continuum.ParameterOuterTauMachine
import Maxwell.Continuum.ParameterOuterStoppingData
import Maxwell.Cost.SelectedParameters.DynamicPowerMachine
import Maxwell.Cost.Structured.NatAssign.BankFrame

/-! Register allocation and fixed transfers between the executed searches.
Static source inputs occupy2210..2219. The outer exponent2206 and powers
2220=2^k,2221=8^k are retained across each inner search. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

def extra : Finset ℕ := Finset.Icc 2200 2260∪SpacingMachine.extra∪BufferMachine.extra∪
  Geometric.extra∪DynamicPower.ids∪{534}
def ids : Finset ℕ := Compare.ids extra
def workspace : Finset ℕ := ids∪{0,1,2,3,4}

def loadSpacing : List NatAssign.Instruction :=
  [.copy 2210 2000,.copy 2221 2001,.copy 2213 2002,.copy 2214 2003,.copy 2215 2004,.copy 2216 2005]

def saveSpacing : List NatAssign.Instruction :=
  [.copy 2006 2227,.copy 2007 2228,.copy 2022 2229,.copy 2025 2243]

def prepareTau : List NatAssign.Instruction :=
  [.copy 2221 2230,.copy 2228 2231,.literal 2232 (2^24),.copy 2230 2233]++
  List.replicate 3 (.multiply 2230 2233)++
  [.multiply 2231 2233,.multiply 2231 2233,.multiply 2232 2233,
    .literal 2234 1,.literal 2235 0,.literal 2236 0,.literal 2237 0,.literal 2238 0]++
  GeometricAdapter.clearGeo++Rational.clear

def prepareSpans : List NatAssign.Instruction :=
  [.copy 2217 2240,.multiply 2221 2240,.multiply 2227 2240,.multiply 2223 2240,.add 2225 2240,
   .copy 2218 2241,.multiply 2221 2241,.multiply 2227 2241,.multiply 2223 2241,.add 2225 2241,
   .copy 2219 2242,.multiply 2221 2242,.multiply 2227 2242,.multiply 2223 2242,.add 2225 2242]

def loadBuffer : List NatAssign.Instruction :=
  [.copy 2210 2100,.copy 2221 2101,.copy 2212 2102,.copy 2211 2103,
   .copy 2213 2104,.copy 2214 2105,.copy 2215 2106,.copy 2216 2107,
   .copy 2229 2108,.copy 2243 2109,.copy 2234 2110,.copy 2237 2111,
   .copy 2240 2112,.copy 2241 2113,.copy 2242 2114]

def saveBuffer : List NatAssign.Instruction :=
  [.copy 2115 2244,.copy 2130 2245,.copy 2155 2246,.copy 2156 2247]

def prepareTail : List NatAssign.Instruction :=
  [.copy 2225 2260,.multiply 2212 2260,.multiply 2210 2260]++
    List.replicate 5 (.multiply 2221 2260)++
  [.multiply 2228 2260,.multiply 2228 2260]

def tests : List AllComparisons.Test := [((2246,2247),(2251,2222)),((2260,2222),(2253,2222))]

theorem ids_ge : ∀i∈ids,10 ≤ i := by
  intro i hi
  simp only [ids,Compare.ids,extra,SpacingMachine.extra,BufferMachine.extra,Geometric.extra,
    DynamicPower.ids,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem loadSpacing_valid : ∀a∈loadSpacing,a.Valid ids := by
  simp [loadSpacing,NatAssign.Instruction.Valid,ids,Compare.ids,extra,SpacingMachine.extra]

theorem saveSpacing_valid : ∀a∈saveSpacing,a.Valid ids := by
  simp [saveSpacing,NatAssign.Instruction.Valid,ids,Compare.ids,extra,SpacingMachine.extra]

theorem prepareTau_valid : ∀a∈prepareTau,a.Valid ids := by
  simp [prepareTau,NatAssign.Instruction.Valid,ids,Compare.ids,extra,GeometricAdapter.clearGeo,
    Rational.clear,Geometric.extra]

theorem prepareSpans_valid : ∀a∈prepareSpans,a.Valid ids := by
  simp [prepareSpans,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem loadBuffer_valid : ∀a∈loadBuffer,a.Valid ids := by
  simp [loadBuffer,NatAssign.Instruction.Valid,ids,Compare.ids,extra,BufferMachine.extra]

theorem saveBuffer_valid : ∀a∈saveBuffer,a.Valid ids := by
  simp [saveBuffer,NatAssign.Instruction.Valid,ids,Compare.ids,extra,BufferMachine.extra]

theorem prepareTail_valid : ∀a∈prepareTail,a.Valid ids := by
  simp [prepareTail,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem tests_valid : ∀q∈tests,AllComparisons.Valid extra q := by
  simp [tests,AllComparisons.Valid,extra]

theorem loadSpacing_fields (v : ℕ→ℕ) :
    SpacingMachine.dataOf (NatAssign.values loadSpacing v)=
      ⟨v 2210,v 2221,v 2213,v 2214,v 2215,v 2216⟩ := by
  simp [SpacingMachine.dataOf,loadSpacing,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem saveSpacing_fields (v : ℕ→ℕ) :
    NatAssign.values saveSpacing v 2227=v 2006 ∧ NatAssign.values saveSpacing v 2228=v 2007 ∧
    NatAssign.values saveSpacing v 2229=v 2022 ∧ NatAssign.values saveSpacing v 2243=v 2025 := by
  simp [saveSpacing,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem prepareTau_fields (v : ℕ→ℕ) :
    NatAssign.values prepareTau v 2233=2^24*(v 2221)^4*(v 2228)^2 ∧
    NatAssign.values prepareTau v 2234=1 ∧ NatAssign.values prepareTau v 2237=0 ∧
    NatAssign.values prepareTau v 2238=0 ∧
    (∀i∈Geometric.extra,NatAssign.values prepareTau v i=0) := by
  simp [prepareTau,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,List.replicate_succ,GeometricAdapter.clearGeo,Rational.clear,Geometric.extra]
  ring

theorem prepareSpans_fields (v : ℕ→ℕ) (h2 : v 2223=2) (h4 : v 2225=4) (j : Fin 3) :
    NatAssign.values prepareSpans v (2240+j.val)=2*v 2221*v 2227*v (2217+j.val)+4 := by
  fin_cases j <;>
    simp [prepareSpans,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,h2,h4] <;> ring

theorem loadBuffer_fields (v : ℕ→ℕ) :
    BufferMachine.dataOf (NatAssign.values loadBuffer v)=
      ⟨v 2210,v 2221,v 2212,v 2211,v 2213,v 2214,v 2215,v 2216,v 2229,v 2243,v 2234,v 2237,
        fun j=>v (2240+j.val)⟩ := by
  simp [BufferMachine.dataOf,loadBuffer,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]
  funext j
  fin_cases j <;> rfl


theorem saveBuffer_fields (v : ℕ→ℕ) :
    NatAssign.values saveBuffer v 2244=v 2115 ∧ NatAssign.values saveBuffer v 2245=v 2130 ∧
    NatAssign.values saveBuffer v 2246=v 2155 ∧ NatAssign.values saveBuffer v 2247=v 2156 := by
  simp [saveBuffer,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem prepareTail_value (v : ℕ→ℕ) (h4 : v 2225=4) :
    NatAssign.values prepareTail v 2260=OuterStopping.tailNumerator (v 2210) (v 2212) (v 2221) (v 2228) := by
  simp [prepareTail,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,List.replicate_succ,h4,OuterStopping.tailNumerator]
  ring

#print axioms prepareTau_fields
#print axioms loadBuffer_fields
end Maxwell.Continuum.Parameters.OuterMachine
