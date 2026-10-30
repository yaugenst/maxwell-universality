import Maxwell.Continuum.SourceRoutingTreeArithmetic
import Maxwell.Cost.RoutingPorts.Primitives

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Power
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def code : Code := RoutingPorts.powerCode 810 830 813

theorem executes (v : ℕ→ℕ) (hz : v 813=0) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h830 : Blank s.val 830) :
    ∃steps t,Executes input tape code steps s t ∧
      steps ≤ (v 810+1)*(13*(v 810).bits.length+25)+21*(v 810).bits.length+27 ∧
      NatAssign.Bank Division.ids (Function.update v 813 (2^(v 810))) t.val ∧
      PrivateVisit.Clean t ∧ Blank t.val 830 ∧ BinaryPrecision.Frame {830,813} s.val t.val := by
  have blank : Blank s.val 813 := (RationalAccumulator.zero_word_iff_blank _ _).mp (by
    simpa only [hz] using hs 813 (by decide))
  obtain ⟨steps,t,he,hcost,wt,zt,ft⟩:=RoutingPorts.power 810 830 813 (by decide) (by decide) (by decide)
    input tape (v 810) s (hs 810 (by decide)) h830 blank
  have scratch : NatAssign.Scratch t.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (ft.tapes i (by simp;omega)) (Workspace.scratch hc i hi)
  refine ⟨steps,t,he,hcost,?_,Workspace.of_frame hc scratch ft ?_,zt,ft⟩
  · intro i hi
    by_cases he : i=813
    · subst i;simpa only [Function.update_self] using wt
    · rw [Function.update_of_ne he]
      exact RationalAccumulator.word_of_eq (ft.tapes i (by
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        refine ⟨?_,he⟩
        intro hh;subst i;exact (show (830 : ℕ)∉Division.ids by decide) hi)) (hs i hi)
  · intro i hi _
    have disjoint : Disjoint Workspace.ids ({830,813}:Finset ℕ) := by decide
    exact Finset.disjoint_left.mp disjoint hi

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Power
