import Maxwell.Continuum.FourierTensorPhysicalFactorData

/-! The physical Fourier normalization is computed by one fixed program
from stored M and precision, including the three denominator products. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Calibration
open RationalAccumulator (Word)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def code : Code := .seq setupCode RationalRoot.code
def costBound (P W : ℕ) : ℕ := 2^120*(P+W+14)^7

theorem executes (M P W : ℕ) (hM : 0<M) (hm : M.bits.length≤W) (hp : P.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initial M P) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound P W ∧
      NatAssign.Bank ids (outputValues M P) t.val ∧
      Word t.val 32 (Nat.sqrt (rootArgument M P)) ∧
      Word t.val 548 (denominator M*2^P) ∧ 0<denominator M*2^P ∧
      (Nat.sqrt (rootArgument M P):ℚ)/(denominator M*2^P)=Supercell.physicalFactorApprox M P ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  have initialWidth : ∀i∈ids,(initial M P i).bits.length≤W+4 := by
    intro i _
    have hzero : (0:ℕ).bits.length=0 := rfl
    unfold initial
    split_ifs <;> omega
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := fixedBankStage_executes ids ids_ge setup setup_valid
    (by decide) (initial M P) (W+4) initialWidth
    (by simp [setup,NatAssign.Instruction.literalWidth,show (8:ℕ).bits.length=4 by decide]) input tape s hs hz
  have rootBank : NatAssign.Bank RationalRoot.ids (RationalRoot.inputValues 1 (denominator M) P) u.val := by
    intro i hi
    simpa only [setup_root_values M P i hi] using b0 i (Finset.mem_union_left _ hi)
  obtain ⟨c1,t,e1,hc1,num,den,a0,d0,p0,br,zr,fr⟩ := RationalRoot.executes 1 (denominator M) P (3*W+4)
    (by change 1≤3*W+4;omega) (denominator_width M W hm) (hp.trans (by omega)) input tape u rootBank z0
  have full : NatAssign.Bank ids (outputValues M P) t.val := by
    intro i hi
    by_cases h350 : i=350
    · subst i
      have h := RationalAccumulator.word_of_eq (fr.tapes 350 (by decide)) (b0 350 (by decide))
      simpa only [setup_values,outputValues,ite_true] using h
    by_cases h351 : i=351
    · subst i
      have h := RationalAccumulator.word_of_eq (fr.tapes 351 (by decide)) (b0 351 (by decide))
      simpa only [setup_values,outputValues,show (351:ℕ)≠350 by decide,ite_false,ite_true] using h
    have hi' : i∈RationalRoot.ids := (Finset.mem_union.mp hi).resolve_right (by simp [h350,h351])
    by_cases hfull : i∈NaturalRoot.fullIds
    · simpa only [outputValues,rootArgument,ite_eq_right h350,ite_eq_right h351,ite_eq_left hfull] using br i hfull
    · have four : i=542 ∨ i=543 ∨ i=544 ∨ i=548 := by
        simpa only [RationalRoot.ids,Finset.mem_union,hfull,false_or,Finset.mem_insert,Finset.mem_singleton] using hi'
      rcases four with rfl|rfl|rfl|rfl
      · simpa [outputValues,hfull,RationalRoot.preparedValues,RationalRoot.inputValues] using a0
      · simpa [outputValues,hfull,RationalRoot.preparedValues,RationalRoot.inputValues] using d0
      · simpa [outputValues,hfull,RationalRoot.preparedValues,RationalRoot.inputValues] using p0
      · simpa [outputValues,hfull,RationalRoot.preparedValues] using den
  refine ⟨c0+c1,t,e0.seq e1,?_,full,num,den,
    Nat.mul_pos (denominator_pos M hM) (by positivity),factor_value M P hM,zr,
    f0.trans (fr.mono (by decide))⟩
  have h1 : (W+6)^2≤(P+W+14)^2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (P+W+14)^2≤(P+W+14)^7 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : (P+3*W+4+10)^7≤(3*(P+W+14))^7 := Nat.pow_le_pow_left (by omega) 7
  rw [mul_pow] at h3
  have c0' : c0≤2^96*(P+W+14)^7 := hc0.trans (Nat.mul_le_mul_left _ (h1.trans h2))
  have c1' : c1≤(2^104*3^7)*(P+W+14)^7 := by
    exact hc1.trans (by simpa only [RationalRoot.costBound,Nat.mul_assoc,Nat.add_assoc] using Nat.mul_le_mul_left (2^104) h3)
  calc
    _ ≤ (2^96+2^104*3^7)*(P+W+14)^7 := by nlinarith only [c0',c1']
    _ ≤ costBound P W := Nat.mul_le_mul_right _ (by norm_num)

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
