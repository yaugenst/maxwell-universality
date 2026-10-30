import Maxwell.Continuum.PhaseRuntimeTail

/-! A uniform Boolean phase evaluator. Numeric precision and frequency
parameters enter only as stored input words. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def core (negative : Bool) (base : RationalTaylor.Runtime.Cycle) : Code :=
  .seq setupCode (.seq machinCode (tail negative base))
def program (base : RationalTaylor.Runtime.Cycle) : Code := .branch 200 (core true base) (core false base)
def costBound (Q N W : ℕ) : ℕ := setupCost W+machinCost Q N W+tailCost Q N W+1

theorem core_executes (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (core negative base) cost s t ∧ cost+1≤costBound Q N W ∧
      NatAssign.Bank ids (finalValues negative base a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,u,e0,h0,bu,zu,fu⟩ := setup_executes a b Q N W ha hb hQ hN hW input tape s hs hz
  obtain ⟨c1,r,e1,h1,br,zr,fr⟩ := machin_executes a b Q N W ha hb hQ hN hW input tape u bu zu
  obtain ⟨c2,t,e2,h2,bt,zt,ft⟩ := tail_executes negative base a b Q N W ha hb input tape r br zr
  exact ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by unfold costBound;omega,bt,zt,fu.trans (fr.trans ft)⟩

theorem executes (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b Q N) s.val) (hz : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=negative) :
    ∃cost t,Executes input tape (program base) cost s t ∧ cost≤costBound Q N W ∧
      NatAssign.Bank ids (finalValues negative base a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c,t,e,hc,bt,zt,ft⟩ := core_executes negative base a b Q N W ha hb hQ hN hW input tape s hs hz
  refine ⟨1+c,t,?_,by omega,bt,zt,ft⟩
  cases negative with
  | false => exact Executes.no hsg e
  | true => exact Executes.yes hsg e

theorem finalValues_core (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N i : ℕ) (hi : i∈PhaseMachine.allIds) :
    finalValues negative base a b Q N i=
      PhaseMachine.fullFinal negative (RationalTaylor.Runtime.cycleSigns base) a b Q N i :=
  ite_eq_left hi

theorem finalValues_width (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N W i : ℕ) (hi : i∈ids) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) :
    (finalValues negative base a b Q N i).bits.length≤fullFinalWidth Q N W+W := by
  rcases Finset.mem_union.mp hi with hi|hi
  · rw [finalValues_core negative base a b Q N i hi]
    exact (fullFinal_width negative (RationalTaylor.Runtime.cycleSigns base) a b Q N W ha hb i hi).trans
      (Nat.le_add_right _ _)
  · rw [finalValues_extra negative base a b Q N i hi]
    split_ifs
    · exact ((Machin.Runtime.nat_bits_le_self Q.bits.length).trans hQ).trans (Nat.le_add_left _ _)
    · exact (initialValues_width a b Q N W i ha hb hQ hN).trans (Nat.le_add_left _ _)

#print axioms executes
#print axioms finalValues_width
end Maxwell.Continuum.PhaseMachine.Runtime
