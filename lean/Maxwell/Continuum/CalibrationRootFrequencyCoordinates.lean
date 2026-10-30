import Maxwell.Continuum.CalibrationRootFrequencyStages

/-! Charged quotient/remainder decoding of the three frequency coordinates. -/
namespace Maxwell.Continuum.RationalDataflow.RootFrequency
open Maxwell.Cost Maxwell.Cost.Structured
open Calibration.ArrayDecodeMachine (divModValues divModValues_width nat_values_width)
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def coordinateCode : Code := .seq (NaturalDivMod.code 330 331 332 333)
  (.seq (NaturalDivMod.code 332 331 332 334)
    (.seq (NaturalDivMod.code 332 331 340 335)
      (.seq (NaturalDivMod.code 331 343 339 340) (NatAssign.code factor))))

theorem division_zero (n : ℕ→ℕ) (source divisor q r : ℕ)
    (hq : q∈Finset.Icc 330 344) (hr : r∈Finset.Icc 330 344)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0) :
    ∀i∈NaturalQuotient.workPorts,divModValues n source divisor q r i=0 := by
  intro i hi
  have hneq : i≠q ∧ i≠r := by
    have hiq := range_outside_work q hq
    have hir := range_outside_work r hr
    constructor <;> intro he <;> subst i <;> contradiction
  simp only [divModValues,Function.update_of_ne hneq.1,Function.update_of_ne hneq.2,hz i hi]

theorem factor_valid : ∀a∈factor,a.Valid ids := by
  simp [factor,NatAssign.Instruction.Valid,ids]

theorem factored_keep (n : ℕ→ℕ) (i : ℕ)
    (hi : i∈NaturalQuotient.workPorts ∨ i=331) : factored n i=n i := by
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  simp only [factored,factor,halved,coordinates,coordinateSecond,coordinateFirst,pair,prepared,prepare,
    divModValues,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    Function.update_of_ne (by omega : i≠340),Function.update_of_ne (by omega : i≠339),
    Function.update_of_ne (by omega : i≠335),Function.update_of_ne (by omega : i≠334),
    Function.update_of_ne (by omega : i≠333),Function.update_of_ne (by omega : i≠332),
    Function.update_of_ne (by omega : i≠330),Function.update_of_ne (by omega : i≠341),
    Function.update_of_ne (by omega : i≠343),Function.update_of_ne (by omega : i≠344)]

theorem coordinate_width (n : ℕ→ℕ) (B : ℕ)
    (hn : ∀i∈ids,(pair n i).bits.length≤B) :
    ∀i∈ids,(factored n i).bits.length≤4*(B+1) := by
  have w1 := divModValues_width (pair n) ids 330 331 332 333 B (by decide) hn
  have w2 := divModValues_width (coordinateFirst n) ids 332 331 332 334 B (by decide) w1
  have w3 := divModValues_width (coordinateSecond n) ids 332 331 340 335 B (by decide) w2
  have w4 := divModValues_width (coordinates n) ids 331 343 339 340 B (by decide) w3
  simpa only [factored,show factor.length=2 by rfl,show 2^2=4 by rfl] using
    nat_values_width ids factor factor_valid (halved n) B w4
      (by simp [factor,NatAssign.Instruction.literalWidth])

theorem coordinate_executes (n : ℕ→ℕ) (B : ℕ)
    (hn : ∀i∈ids,(pair n i).bits.length≤B)
    (hz : ∀i∈NaturalQuotient.workPorts,pair n i=0) (hp : 0 < n 331)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (pair n) s.val) (hblank : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape coordinateCode cost s t ∧ cost≤2^104*(B+2)^2 ∧
      NatAssign.Bank ids (factored n) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧ BinaryPrecision.Frame changed s.val t.val := by
  have p0 : 0 < pair n 331 := by rw [(pair_values n).2.2.1];exact hp
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := divide_executes 330 331 332 333 (by decide) (by decide)
    (by decide) (by decide) (by decide) (pair n) B hn hz p0 input tape s hb hblank
  have w1 := divModValues_width (pair n) ids 330 331 332 333 B (by decide) hn
  have zero1 := division_zero (pair n) 330 331 332 333 (by decide) (by decide) hz
  have p1 : 0 < coordinateFirst n 331 := by
    simpa only [coordinateFirst,divModValues,Function.update_of_ne (by decide : (331:ℕ)≠333),
      Function.update_of_ne (by decide : (331:ℕ)≠332)] using p0
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := divide_executes 332 331 332 334 (by decide) (by decide)
    (by decide) (by decide) (by decide) (coordinateFirst n) B w1 zero1 p1 input tape s1 b1 z1
  have w2 := divModValues_width (coordinateFirst n) ids 332 331 332 334 B (by decide) w1
  have zero2 := division_zero (coordinateFirst n) 332 331 332 334 (by decide) (by decide) zero1
  have p2 : 0 < coordinateSecond n 331 := by
    simpa only [coordinateSecond,divModValues,Function.update_of_ne (by decide : (331:ℕ)≠334),
      Function.update_of_ne (by decide : (331:ℕ)≠332)] using p1
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := divide_executes 332 331 340 335 (by decide) (by decide)
    (by decide) (by decide) (by decide) (coordinateSecond n) B w2 zero2 p2 input tape s2 b2 z2
  have w3 := divModValues_width (coordinateSecond n) ids 332 331 340 335 B (by decide) w2
  have zero3 := division_zero (coordinateSecond n) 332 331 340 335 (by decide) (by decide) zero2
  have p3 : 0 < coordinates n 343 := by
    simp only [coordinates,coordinateSecond,coordinateFirst,divModValues,
      Function.update_of_ne (by decide : (343:ℕ)≠335),Function.update_of_ne (by decide : (343:ℕ)≠340),
      Function.update_of_ne (by decide : (343:ℕ)≠334),Function.update_of_ne (by decide : (343:ℕ)≠333),
      Function.update_of_ne (by decide : (343:ℕ)≠332),(pair_values n).2.2.2.1]
    decide
  obtain ⟨c4,s4,e4,h4,b4,z4,f4⟩ := divide_executes 331 343 339 340 (by decide) (by decide)
    (by decide) (by decide) (by decide) (coordinates n) B w3 zero3 p3 input tape s3 b3 z3
  have w4 := divModValues_width (coordinates n) ids 331 343 339 340 B (by decide) w3
  obtain ⟨c5,t,e5,h5,b5,z5,f5⟩ := stage_executes factor factor_valid (by decide) (halved n) B w4
    (by simp [factor,NatAssign.Instruction.literalWidth]) input tape s4 b4 z4
  refine ⟨c1+(c2+(c3+(c4+c5))),t,e1.seq (e2.seq (e3.seq (e4.seq e5))),?_,b5,z5,
    f1.trans (f2.trans (f3.trans (f4.trans f5)))⟩
  unfold stageCost at h5
  omega

#print axioms coordinate_executes
end Maxwell.Continuum.RationalDataflow.RootFrequency
