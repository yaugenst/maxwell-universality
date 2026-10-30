import Maxwell.Continuum.SourceRoutingAssemblyCoordinates
import Maxwell.Continuum.SourceRoutingDivisionBounds

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyAdvance
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def first (v : ℕ→ℕ) : ℕ→ℕ := Division.result v 813 819 813 816
def second (v : ℕ→ℕ) : ℕ→ℕ := Division.result (first v) 814 819 814 817
def finish : List NatAssign.Instruction :=
  [.multiply 819 811,.literal 818 1,.add 818 812,.literal 815 0]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (second v)
def code : Code := .seq (Division.code 813 819 813 816)
  (.seq (Division.code 814 819 814 817) (NatAssign.code finish))

theorem finish_valid : ∀a∈finish,a.Valid Division.ids := by
  simp [finish,NatAssign.Instruction.Valid,Division.ids,Division.controls]

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 1 ≤ B) (htwo : v 819=2)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^110*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      BinaryPrecision.Frame Division.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩:=Division.executes 813 819 813 816
    (by decide) (by decide) (by decide) (by decide) (by decide) v hz (by omega) B hv input tape s hs hc h839
  have w1:=Division.result_width v 813 819 813 816 B (by decide) hv
  have z1:=Division.result_zero v 813 819 813 816 (by decide) (by decide) hz
  have two : first v 819=2 := (Division.result_other v 813 819 813 816 819 (by decide) (by decide)).trans htwo
  obtain ⟨c1,b,e1,h1,b1,zz1,b839,f1⟩:=Division.executes 814 819 814 817
    (by decide) (by decide) (by decide) (by decide) (by decide) (first v) z1 (by omega) B w1 input tape a b0 z0 a839
  have w2:=Division.result_width (first v) 814 819 814 817 B (by decide) w1
  have lit : ∀a∈finish,a.literalWidth ≤ B := by simp [finish,NatAssign.Instruction.literalWidth];exact hB
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩:=Arithmetic.stage finish finish_valid (second v) B w2 lit input tape b b1 zz1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,
    RationalAccumulator.blank_of_eq (f2.tapes 839 (by decide)) b839,
    f0.trans (f1.trans (f2.mono Arithmetic.work_subset))⟩
  change c2 ≤ 3000*8^4*(B+2)^2 at h2
  have unit : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
  nlinarith only [h0,h1,h2,unit]

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyAdvance
