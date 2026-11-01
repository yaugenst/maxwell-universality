import Maxwell.Continuum.RationalDataflowDenominatorProduct
import Maxwell.Cost.Structured.MemoryFootprint

/-! Literal read-only program footprints, including retained auxiliary banks. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem read_one_protects_four : (readCode 1).protectsTape 4=true := by decide

def denominatorProtectedPorts : List ℕ := [4,37,210,212,213,214,215,220,221,222,223]

theorem denominator_protects_auxiliary :
    denominatorProtectedPorts.all (fun i => (denominatorCode 0 1).protectsTape i)=true := by decide

theorem denominator_protects_memory : (denominatorCode 0 1).protectsMemory=true := by decide

#print axioms denominator_protects_memory
#print axioms denominator_protects_auxiliary
end Maxwell.Continuum.RationalDataflow.PartArray
