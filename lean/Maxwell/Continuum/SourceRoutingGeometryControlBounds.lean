import Maxwell.Continuum.SourceRoutingGeometryControlSyntax

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem decrement (target : ℕ) (ht : target∈controls) (v : ℕ→ℕ) (positive : 0<v target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (PhysicalMaterial.FixedSubtract.code target 1) steps s t ∧
      steps ≤ 29*(v target).bits.length+31 ∧
      NatAssign.Bank ids (Function.update v target (v target-1)) t.val ∧ GeometryArray.Ready t.val ∧
      Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hc,wt,ft⟩:=PhysicalMaterial.FixedSubtract.executes target 1 (v target)
    positive input tape s (bank target (Finset.mem_union_left _ ht))
  have targetRange : 1200 ≤ target ∧ target ≤ 1239 := Finset.mem_Icc.mp ht
  have frame : BinaryPrecision.Frame work s.val t.val := ft.mono (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    subst j
    exact Finset.mem_union_right _ (Finset.mem_union_left _ ht))
  have zt : NatAssign.Scratch t.val := by
    intro j hj
    exact RationalAccumulator.blank_of_eq (ft.tapes j (by simp only [Finset.mem_singleton];omega))
      (scratch ready j hj)
  refine ⟨steps,t,he,by dsimp only [PhysicalMaterial.FixedSubtract.costBound] at hc;omega,?_,
    ready_of_frame ready zt frame,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by simp only [Finset.mem_singleton];omega)) privateBlank,frame⟩
  intro j hj
  by_cases he : j=target
  · subst j;simpa only [Function.update_self] using wt
  · simpa only [Function.update_of_ne he] using RationalAccumulator.word_of_eq
      (ft.tapes j (by simpa only [Finset.mem_singleton] using he)) (bank j hj)

theorem decrement_width (v : ℕ→ℕ) (target B : ℕ) (ht : target∈ids)
    (width : ∀j∈ids,(v j).bits.length ≤ B) :
    ∀j∈ids,((Function.update v target (v target-1)) j).bits.length ≤ B := by
  intro j hj
  by_cases he : j=target
  · subst j
    simpa only [Function.update_self] using
      (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le (v target) 1)).trans (width target ht)
  · simpa only [Function.update_of_ne he] using width j hj

theorem decrement_zero (v : ℕ→ℕ) (target : ℕ) (ht : target∈controls)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Function.update v target (v target-1) j=0 := by
  intro j hj
  have different : j≠target := by
    simp only [controls,Finset.mem_Icc] at ht
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  simpa only [Function.update_of_ne different] using zero j hj

def controlCost (steps B : ℕ) : ℕ := 2^(110+3*steps)*(B+2)^2

theorem controlCost_steps (a b B : ℕ) (h : a ≤ b) : controlCost a B ≤ controlCost b B :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

theorem controlCost_one (steps B : ℕ) : 1 ≤ controlCost steps B := by
  apply Nat.succ_le_of_lt
  dsimp only [controlCost]
  positivity

theorem controlCost_successor (steps B a b : ℕ)
    (ha : a ≤ 2^104*(B+2)^2) (hb : b ≤ controlCost steps (2*B+1)) :
    a+b ≤ controlCost (1+steps) B := by
  have coefficient : 2^104 ≤ 2^(110+3*steps) := Nat.pow_le_pow_right (by decide) (by omega)
  have square : (2*B+1+2)^2 ≤ 4*(B+2)^2 := by
    calc
      _ ≤ (2*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have first:=ha.trans (Nat.mul_le_mul_right ((B+2)^2) coefficient)
  have second:=hb.trans (Nat.mul_le_mul_left (2^(110+3*steps)) square)
  have power : 110+3*(1+steps)=(110+3*steps)+3 := by omega
  simp only [controlCost,power,pow_add] at *
  nlinarith only [first,second]

#print axioms decrement
#print axioms controlCost_successor
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
