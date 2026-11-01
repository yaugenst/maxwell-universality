import Maxwell.Cost.RoutingPorts.Primitives
import Maxwell.Cost.Structured.WordCleanup

/-! A binary exponent word drives actual power-of-two generation after
charged cleanup of the finite destination and countdown words. -/
namespace Maxwell.Cost.Structured.StoredPowerOfTwo
open RationalAccumulator
set_option maxHeartbeats 1500000

def code (source temporary target : ℕ) : Code:=.seq (WordCleanup.code [temporary,target])
  (RoutingPorts.powerCode source temporary target)

theorem executes (source temporary target : ℕ) (hst : source≠temporary) (hso : source≠target)
    (hto : temporary≠target) (N H : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (exponent : Word s.val source N) (old : WordCleanup.Bounded [temporary,target] H s.val) :
    ∃cost t,Executes input tape (code source temporary target) cost s t ∧
      cost≤2*(6*H+4)+1+((N+1)*(13*N.bits.length+25)+21*N.bits.length+27) ∧
      Word t.val target (2^N) ∧Blank t.val temporary ∧BinaryPrecision.Frame {temporary,target} s.val t.val := by
  obtain ⟨c0,a,e0,hc0,blank,f0⟩:=WordCleanup.executes [temporary,target] H input tape s old
  have expA : Word a.val source N:=word_of_eq (f0.tapes source (by simp [hst,hso])) exponent
  obtain ⟨c1,t,e1,hc1,power,clean,f1⟩:=RoutingPorts.power source temporary target hst hso hto
    input tape N a expA (blank temporary (by simp)) (blank target (by simp))
  refine ⟨c0+c1,t,e0.seq e1,?_,power,clean,(f0.mono (by simp)).trans f1⟩
  change c0≤2*(6*H+4)+1 at hc0
  omega

#print axioms executes
end Maxwell.Cost.Structured.StoredPowerOfTwo
