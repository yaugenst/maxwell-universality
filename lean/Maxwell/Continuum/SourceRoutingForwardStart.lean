import Maxwell.Continuum.SourceRoutingTreeRoundTrip

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ForwardStart
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def output (v : ℕ→ℕ) : ℕ→ℕ := Level.Advance.decreased v
def code : Code := .seq (Division.code 811 819 811 816) (PhysicalMaterial.FixedSubtract.code 812 1)

theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉({811,812,816} : Finset ℕ)) :
    output v i=v i := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp only [output,Level.Advance.decreased,Level.Advance.divided,
    Function.update_of_ne hi.2.1,Function.update_of_ne hi.2.2,Function.update_of_ne hi.1]

theorem executes (v : ℕ→ℕ) (B : ℕ) (htwo : v 819=2) (hwidth : 0<v 812)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^110*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      BinaryPrecision.Frame Division.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩:=Division.executes 811 819 811 816
    (by decide) (by decide) (by decide) (by decide) (by decide) v hz (by omega) B hv input tape s hs hc h839
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩:=Arithmetic.decrement 812 (by decide) (Level.Advance.divided v)
    (by simpa only [Level.Advance.divided,Function.update_of_ne (by decide : (812 : ℕ)≠816),
      Function.update_of_ne (by decide : (812 : ℕ)≠811)] using hwidth) input tape a b0 z0
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,
    RationalAccumulator.blank_of_eq (f1.tapes 839 (by decide)) a839,f0.trans (f1.mono (by decide))⟩
  change c1 ≤ 29*(v 812).bits.length+31 at h1
  have hh:=hv 812 (by decide)
  have linear : 29*B+32 ≤ 32*(B+2)^2 := by nlinarith
  nlinarith only [h0,h1,hh,linear]

structure Setup (v : ℕ→ℕ) (heap rows total : ℕ) : Prop where
  positive : 1 ≤ total
  heapWord : v 806=heap
  stride : v 809=Tree.stride (2^(total+rows)) (total+rows+1)
  depth : v 810=total
  count : v 811=2^(total+rows)
  width : v 812=total+rows+1
  population : v 813=2
  first : v 814=0
  index : v 815=0
  two : v 819=2
  zero : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0
  words : ∀i∈Division.ids,(v i).bits.length ≤ Traversal.width heap rows total

theorem Setup.forward {v : ℕ→ℕ} {heap rows total : ℕ} (hs : Setup v heap rows total) :
    Traversal.Setup (output v) heap rows total := by
  refine ⟨hs.positive,⟨(output_other v 806 (by decide)).trans hs.heapWord,
    (output_other v 809 (by decide)).trans hs.stride,?_,?_,
    (output_other v 814 (by decide)).trans hs.first,
    (output_other v 815 (by decide)).trans hs.index,
    (output_other v 819 (by decide)).trans hs.two⟩,
    (output_other v 813 (by decide)).trans hs.population,?_,Level.Advance.decreased_width v _ hs.words⟩
  · change v 811/v 819=2^(total-1+rows)
    rw [hs.count,hs.two]
    have exponent : total+rows=(total-1+rows)+1 := by have hh:=hs.positive;omega
    rw [exponent,pow_succ]
    omega
  · change v 812-1=total-1+rows+1
    rw [hs.width]
    have hh:=hs.positive
    omega
  · intro i hi
    have disjoint : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts
        ({811,812,816} : Finset ℕ) := by decide
    rw [output_other v i (Finset.disjoint_left.mp disjoint hi)]
    exact hs.zero i hi

#print axioms executes
#print axioms Setup.forward
end Maxwell.Cost.RoutingPorts.Complete.Tree.ForwardStart
