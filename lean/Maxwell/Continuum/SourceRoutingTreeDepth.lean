import Maxwell.Continuum.SourceRoutingDivisionBounds
import Maxwell.Continuum.SourceRoutingTreeArithmetic

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Depth
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def decreased (v : ℕ→ℕ) : ℕ→ℕ := Function.update v 810 (v 810-1)
def output (v : ℕ→ℕ) : ℕ→ℕ := Division.result (decreased v) 810 819 810 816
def code : Code := .seq (PhysicalMaterial.FixedSubtract.code 810 1) (Division.code 810 819 810 816)

theorem decreased_width (v : ℕ→ℕ) (B : ℕ) (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(decreased v i).bits.length ≤ B := by
  intro i hi
  by_cases he : i=810
  · subst i
    exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le (v 810) 1)).trans (hv 810 (by decide))
  · simpa only [decreased,Function.update_of_ne he] using hv i hi

theorem output_width (v : ℕ→ℕ) (B : ℕ) (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(output v i).bits.length ≤ B :=
  Division.result_width (decreased v) 810 819 810 816 B (by decide) (decreased_width v B hv)

theorem output_other (v : ℕ→ℕ) (i : ℕ) (h810 : i≠810) (h816 : i≠816) : output v i=v i := by
  rw [output,Division.result_other _ _ _ _ _ _ h810 h816]
  exact Function.update_of_ne h810 _ _

theorem output_depth (v : ℕ→ℕ) (total : ℕ) (ht : v 810=2*total+1) (htwo : v 819=2) :
    output v 810=total := by
  change (v 810-1)/v 819=total
  rw [ht,htwo]
  omega

theorem decreased_zero (v : ℕ→ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,decreased v i=0 := by
  intro i hi
  have hn : i≠810 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  simpa only [decreased,Function.update_of_ne hn] using hz i hi

theorem output_zero (v : ℕ→ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,output v i=0 :=
  Division.result_zero _ 810 819 810 816 (by decide) (by decide) (decreased_zero v hz)

theorem executes (v : ℕ→ℕ) (B : ℕ) (ht : 0<v 810) (htwo : v 819=2)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^110*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      BinaryPrecision.Frame Division.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,f0⟩:=Arithmetic.decrement 810 (by decide) v ht input tape s hs hc
  have a839:=RationalAccumulator.blank_of_eq (f0.tapes 839 (by decide)) h839
  obtain ⟨c1,t,e1,h1,b1,z1,t839,f1⟩:=Division.executes 810 819 810 816
    (by decide) (by decide) (by decide) (by decide) (by decide) (decreased v) (decreased_zero v hz)
    (by simpa only [decreased,Function.update_of_ne (by decide : (819 : ℕ)≠810)] using
      (show 0<v 819 by omega)) B (decreased_width v B hv) input tape a b0 z0 a839
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,t839,(f0.mono (by decide)).trans f1⟩
  have hh:=hv 810 (by decide)
  have linear : 29*B+32 ≤ 32*(B+2)^2 := by nlinarith
  nlinarith only [h0,h1,hh,linear]

#print axioms output_depth
#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Depth
