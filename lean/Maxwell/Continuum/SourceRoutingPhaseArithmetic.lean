import Maxwell.Continuum.SourceRoutingGeometryDivisionBounds
import Maxwell.Continuum.SourceRoutingPhaseKeys

/-! One source port determines all three initial sorting-key writes through
three bounded natural divisions and a fixed arithmetic suffix. -/

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured GeometryArithmetic Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def firstDivision (v : ℕ→ℕ) : ℕ→ℕ := divided v 1202 1200 1204 1205
def secondDivision (v : ℕ→ℕ) : ℕ→ℕ := divided (firstDivision v) 1203 1200 1206 1207
def thirdDivision (v : ℕ→ℕ) : ℕ→ℕ := divided (secondDivision v) 1201 1200 1208 1209
def finish : List NatAssign.Instruction :=
  [.copy 1209 1210,.multiply 1200 1210,.add 1204 1210,.copy 1202 1211,.add 1207 1211]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (thirdDivision v)
def code : Code := .seq (divisionCode 1202 1200 1204 1205)
  (.seq (divisionCode 1203 1200 1206 1207)
    (.seq (divisionCode 1201 1200 1208 1209) (NatAssign.code finish)))

theorem finish_valid : ∀a∈finish,a.Valid GeometryArithmetic.ids := by
  simp [finish,NatAssign.Instruction.Valid,GeometryArithmetic.ids,controls]

theorem color (v : ℕ→ℕ) : output v 1204=v 1202/v 1200 := rfl
theorem targetColumn (v : ℕ→ℕ) : output v 1206=v 1203/v 1200 := rfl
theorem targetRow (v : ℕ→ℕ) : output v 1207=v 1203%v 1200 := rfl
theorem middleIndex (v : ℕ→ℕ) :
    output v 1210=v 1200*(v 1201%v 1200)+v 1202/v 1200 := Nat.add_comm _ _
theorem lastIndex (v : ℕ→ℕ) : output v 1211=v 1202+v 1203%v 1200 := Nat.add_comm _ _

theorem executes (v : ℕ→ℕ) (zero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (positive : 0<v 1200) (B : ℕ) (width : ∀i∈GeometryArithmetic.ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : NatAssign.Bank GeometryArithmetic.ids v s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^110*(B+2)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (output v) t.val ∧ GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=divide 1202 1200 1204 1205
    (by decide) (by decide) (by decide) (by decide) (by decide)
    v zero positive B width input tape s bank ready privateBlank
  have w0:=divided_width v 1202 1200 1204 1205 B (by decide) width
  have z0:=divided_zero v 1202 1200 1204 1205 (by decide) (by decide) zero
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,f1⟩:=divide 1203 1200 1206 1207
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (firstDivision v) z0 positive B w0 input tape a ba za a1249
  have w1:=divided_width (firstDivision v) 1203 1200 1206 1207 B (by decide) w0
  have z1:=divided_zero (firstDivision v) 1203 1200 1206 1207 (by decide) (by decide) z0
  obtain ⟨c2,c,e2,h2,bc,zc,c1249,f2⟩:=divide 1201 1200 1208 1209
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (secondDivision v) z1 positive B w1 input tape b bb zb b1249
  have w2:=divided_width (secondDivision v) 1201 1200 1208 1209 B (by decide) w1
  obtain ⟨c3,t,e3,h3,bt,zt,f3⟩:=stage finish finish_valid (thirdDivision v) B w2
    (by simp [finish,NatAssign.Instruction.literalWidth]) input tape c bc zc
  have frame : BinaryPrecision.Frame work c.val t.val := f3.mono (by
    intro i hi
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto)
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bt,zt,
    RationalAccumulator.blank_of_eq (f3.tapes 1249 (by decide)) c1249,
    f0.trans (f1.trans (f2.trans frame))⟩
  change c3 ≤ 3000*8^5*(B+2)^2 at h3
  have power : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
  nlinarith only [h0,h1,h2,h3,power]

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
