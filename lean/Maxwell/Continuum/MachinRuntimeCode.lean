import Maxwell.Continuum.MachinRuntimeCost

/-! The executable Machin program has a fixed, explicitly bounded code size. -/
namespace Maxwell.Continuum.Machin.Runtime
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192

theorem program_size_bound : program.size≤2^24 := by
  have ha := RationalArctan.Runtime.program_size_bound 632
  have hcopy : (WordReplace.code 631 632).size≤2^16 := by decide
  have hclear : (TapeOps.clear 632).code.length≤2^16 := by decide
  have hclear' : (TapeOps.clear 631).code.length≤2^16 := by decide
  have hindex : (NatAssign.code RationalArctan.Runtime.clearIndices).size≤2^16 := by decide
  have hp : (NatAssign.code prologue).size≤2^16 := by decide
  have hs : (NatAssign.code saveFirst).size≤2^16 := by decide
  have hc : (NatAssign.code combine).size≤2^16 := by decide
  have hsetup : (NatAssign.code setup).size≤2^16 := by decide
  simp only [program,core,arctanCall,RationalArctan.Runtime.cleanProgram,Code.size]
  omega

#print axioms program_size_bound
end Maxwell.Continuum.Machin.Runtime
