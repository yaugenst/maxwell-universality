import Maxwell.Continuum.CalibrationInverseDescriptorBounds

/-! Execute the measured inverse-descriptor program on the stored coefficient
headers. Every destination natural and its storage bound follows from the
literal program; caller data consist only of existing canonical words. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
attribute [local irreducible] sources budget measured values rawWidth dimension slotWidth bankWidth

def changed : Finset ℕ := {0,1,2,3,300,301,302,303,304,305,306,307,308,309,530,531,532,533,534}
def costBound (v : ℕ→ℕ) (B : ℕ) : ℕ :=
  192000*(B+2)^2+sources.length*(200000*(B+1024+sources.length*B+2)^2)+1+
    3000*8^plan.length*(budget v+2)^2

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB:11≤B) (hw:∀k∈ids,(v k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hb:NatAssign.Bank ids v s.val)
    (hz:NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound v B ∧
      NatAssign.Bank ids (values v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀k∈ids,(values v k).bits.length≤bankWidth v) ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩:=NatAssign.LengthSum.initialized_executes ids ids_ge 530 531 1024
    (by decide) (by decide) (by decide) sources sources_valid v B hw
    (by simpa only [show (1024:ℕ).bits.length=11 by decide] using hB) input tape s hb hz
  have bank0:NatAssign.Bank ids (measured v) u.val:=by simpa only [measured] using b0
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩:=NatAssign.executes ids ids_ge plan plan_valid (measured v) input tape u bank0 z0
  have price:=NatAssign.price_bound ids plan plan_valid (measured v) (budget v) (measured_width v) (literals_fit v)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 (hc1.trans price),?_,z1,values_width v,
    (f0.mono (by decide)).trans (f1.mono (by decide))⟩
  simpa only [values] using b1

#print axioms executes
end Maxwell.Continuum.Calibration.InverseDescriptor
