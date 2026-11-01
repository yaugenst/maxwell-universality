import Maxwell.Continuum.RationalSquareRootMachine

/-! The complete canonical operand bank left by the executed rational root.
This permits charged reuse and cleanup without assuming fresh old words. -/
namespace Maxwell.Continuum.Calibration.RationalRoot
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def outputValues (A D N : ℕ) (i : ℕ) : ℕ :=
  if i∈NaturalRoot.fullIds then NaturalRoot.doneValues (radicand A D N) i
  else if i=548 then D*2^N else inputValues A D N i
def outputWidth (N W : ℕ) : ℕ := 8*W+12*N+8

theorem output_width (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W)
    (hN : N.bits.length≤W) (i : ℕ) : (outputValues A D N i).bits.length≤outputWidth N W := by
  have hr := NaturalRoot.done_width (radicand A D N) i
  have hb := radicand_bits A D N W hA hD
  have hd := RationalAccumulator.bits_mul_le D (2^N)
  have hp := SelectedParameters.Geometric.power_bits 2 N
  change (2^N).bits.length≤N*2+1 at hp
  have hz : (0:ℕ).bits.length=0 := rfl
  simp only [outputValues,inputValues,outputWidth]
  split_ifs <;> omega

theorem executes_bank (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W)
    (hN : N.bits.length≤W) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (inputValues A D N) s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound N W ∧
      NatAssign.Bank ids (outputValues A D N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cost,t,execution,bound,num,den,aa,dd,nn,root,st,frame⟩ :=
    executes A D N W hA hD hN input tape s bank scratch
  refine ⟨cost,t,execution,bound,?_,st,frame⟩
  intro i hi
  by_cases hr : i∈NaturalRoot.fullIds
  · simpa only [outputValues,ite_eq_left hr] using root i hr
  · have more : i∈({542,543,544,548}:Finset ℕ) := (Finset.mem_union.mp hi).resolve_left hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at more
    rcases more with rfl|rfl|rfl|rfl
    · simpa [outputValues,hr,inputValues] using aa
    · simpa [outputValues,hr,inputValues] using dd
    · simpa [outputValues,hr,inputValues] using nn
    · simpa [outputValues,hr,inputValues] using den

#print axioms executes_bank
end Maxwell.Continuum.Calibration.RationalRoot
