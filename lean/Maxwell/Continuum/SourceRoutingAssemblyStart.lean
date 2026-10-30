import Maxwell.Continuum.SourceRoutingAssemblyTraversalExecution
import Maxwell.Continuum.SourceRoutingTraversalLoaded

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyStart
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def output (v : ℕ→ℕ) : ℕ→ℕ := AssemblyAdvance.second v
def code : Code := .seq (Division.code 813 819 813 816) (Division.code 814 819 814 817)

theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉({813,814,816,817} : Finset ℕ)) :
    output v i=v i := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp only [output,AssemblyAdvance.second,Division.result_other _ _ _ _ _ _ hi.2.1 hi.2.2.2,
    AssemblyAdvance.first,Division.result_other _ _ _ _ _ _ hi.1 hi.2.2.1]

theorem words (v : ℕ→ℕ) (B : ℕ) (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(output v i).bits.length ≤ B :=
  Division.result_width _ 814 819 814 817 B (by decide)
    (Division.result_width v 813 819 813 816 B (by decide) hv)

theorem coordinates (v : ℕ→ℕ) (heap rootCount rootWidth rows total : ℕ) (ht : 1 ≤ total)
    (hs : Coordinates.Stored v heap rootCount rootWidth total (2^rows) (rows+1) 0) :
    AssemblyCoordinates.Stored (output v) heap rootCount rootWidth (total-1) rows 0 := by
  refine ⟨(output_other v 806 (by decide)).trans hs.heap,
    (output_other v 809 (by decide)).trans hs.stride,
    (output_other v 811 (by decide)).trans hs.count,
    (output_other v 812 (by decide)).trans hs.width,?_,
    (output_other v 815 (by decide)).trans hs.index,
    (output_other v 819 (by decide)).trans hs.two⟩
  have eq : total=total-1+1 := by omega
  change v 814/v 819=2^(total-1)-1
  rw [hs.first,hs.two,eq,pow_succ,Nat.add_sub_cancel]
  have hp : 0<(2 : ℕ)^(total-1) := by positivity
  omega

theorem population (v : ℕ→ℕ) (total : ℕ) (ht : 1 ≤ total)
    (hp : v 813=2^total) (htwo : v 819=2) : output v 813=2^(total-1) := by
  change v 813/v 819=2^(total-1)
  have eq : total=total-1+1 := by omega
  rw [hp,htwo,eq,pow_succ,Nat.add_sub_cancel]
  omega

theorem zero (v : ℕ→ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,output v i=0 :=
  Division.result_zero _ 814 819 814 817 (by decide) (by decide)
    (Division.result_zero v 813 819 813 816 (by decide) (by decide) hz)

theorem executes (v : ℕ→ℕ) (B : ℕ) (htwo : v 819=2)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^102*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      BinaryPrecision.Frame Division.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩:=Division.executes 813 819 813 816
    (by decide) (by decide) (by decide) (by decide) (by decide) v hz (by omega) B hv input tape s hs hc h839
  have w1:=Division.result_width v 813 819 813 816 B (by decide) hv
  have z1:=Division.result_zero v 813 819 813 816 (by decide) (by decide) hz
  have two : AssemblyAdvance.first v 819=2 :=
    (Division.result_other v 813 819 813 816 819 (by decide) (by decide)).trans htwo
  obtain ⟨c1,t,e1,h1,b1,z1,t839,f1⟩:=Division.executes 814 819 814 817
    (by decide) (by decide) (by decide) (by decide) (by decide) (AssemblyAdvance.first v) z1
    (by omega) B w1 input tape a b0 z0 a839
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,t839,f0.trans f1⟩
  have unit : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
  nlinarith only [h0,h1,unit]

#print axioms coordinates
#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyStart
