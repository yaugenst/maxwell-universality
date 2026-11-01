import Maxwell.Continuum.RationalSquareRootRaw
import Maxwell.Continuum.RationalDataflowParts

/-! The literal rational square root of a nonnegative unreduced signed
fraction. Magnitude extraction and canonical reduction are both executed. -/
namespace Maxwell.Continuum.Calibration.RationalRoot.Signed
open Maxwell.Cost Maxwell.Cost.Structured
open RationalDataflow (Parts)
open RationalAccumulator (Word)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def inputValues (x : Parts) (N : ℕ) (i : ℕ) : ℕ :=
  if i=30 then x.positive else if i=31 then x.negative else Raw.inputValues 0 x.denominator N i
def magnitudeValues (x : Parts) (N : ℕ) : ℕ→ℕ :=
  Function.update (inputValues x N) 34 (IntegerNormSquare.magnitude x.positive x.negative)
def preparePlan : List NatAssign.Instruction :=
  [.copy 34 228,.literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,
   .literal 34 0,.literal 35 0,.literal 36 0]
def code : Code := .seq RationalMagnitude.program (.seq (NatAssign.code preparePlan) Raw.code)
def costBound (N W : ℕ) : ℕ := 2^130*(N+W+10)^7

theorem preparePlan_valid : ∀ a∈preparePlan,a.Valid Raw.ids := by
  simp [preparePlan,NatAssign.Instruction.Valid,Raw.ids,RationalRoot.ids,NaturalRoot.fullIds,
    NaturalRoot.ids,RationalCanonicalBank.ids]

theorem preparePlan_values (x : Parts) (N : ℕ) :
    NatAssign.values preparePlan (magnitudeValues x N)=
      Raw.inputValues (IntegerNormSquare.magnitude x.positive x.negative) x.denominator N := by
  ext i
  by_cases hlow : 30 ≤ i ∧ i≤36
  · obtain ⟨hl,hu⟩ := hlow
    interval_cases i <;>
      simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,magnitudeValues,Raw.inputValues,
        RationalCanonicalBank.inputValues]
  · have ne : i≠30 ∧ i≠31 ∧ i≠32 ∧ i≠33 ∧ i≠34 ∧ i≠35 ∧ i≠36 := by omega
    by_cases h228 : i=228
    · subst i
      simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,magnitudeValues,Raw.inputValues,
        RationalCanonicalBank.inputValues]
    · simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,magnitudeValues,inputValues,Raw.inputValues,
        RationalCanonicalBank.inputValues,ne,h228]

theorem magnitude_width (x : Parts) (N W : ℕ) (hx : x.Width W) (hn : N.bits.length≤W) (i : ℕ) :
    (magnitudeValues x N i).bits.length≤W+1 := by
  have mag := (IntegerNormSquare.magnitude_bits_length_le x.positive x.negative).trans
    (Nat.add_le_add_right (max_le hx.1 hx.2.1) 1)
  have zero : (0:ℕ).bits.length=0 := rfl
  rcases hx with ⟨hp,hm,hd⟩
  simp only [magnitudeValues,Function.update_apply,inputValues,Raw.inputValues,
    RationalCanonicalBank.inputValues]
  split_ifs <;> omega

theorem magnitude_value (x : Parts) (valid : x.Valid) (nonnegative : 0≤x.value) :
    (IntegerNormSquare.magnitude x.positive x.negative:ℚ)/x.denominator=x.value := by
  have den : (0:ℚ)<x.denominator := by exact_mod_cast valid
  have numer : (0:ℚ)≤(x.positive:ℚ)-x.negative := by
    rcases div_nonneg_iff.mp nonnegative with h|h
    · exact h.1
    · linarith [h.2]
  have le : x.negative≤x.positive := by exact_mod_cast (sub_nonneg.mp numer)
  rw [Parts.magnitude_eq_of_le x le,Nat.cast_sub le]
  rfl

theorem executes (x : Parts) (N W : ℕ) (valid : x.Valid) (nonnegative : 0≤x.value)
    (width : x.Width W) (precision : N.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Raw.ids (inputValues x N) s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t num den,Executes input tape code cost s t ∧ cost≤costBound N W ∧
      Word t.val 32 num ∧ Word t.val 548 den ∧ 0<den ∧
      (num:ℚ)/den=sqrtRationalCenter x.value N ∧
      NatAssign.Bank Raw.ids
        (Raw.outputValues (IntegerNormSquare.magnitude x.positive x.negative) x.denominator N) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame Raw.changed s.val t.val := by
  obtain ⟨c0,u,e0,h0,b0,z0,f0,_⟩ := RationalMagnitude.executes Raw.ids (by decide) Raw.ids_ge
    (inputValues x N) (by simp [inputValues,Raw.inputValues,RationalCanonicalBank.inputValues])
    input tape s bank scratch
  change NatAssign.Bank Raw.ids (magnitudeValues x N) u.val at b0
  obtain ⟨c1,v,e1,h1,b1,z1,f1⟩ := NatAssign.executes Raw.ids Raw.ids_ge preparePlan preparePlan_valid
    (magnitudeValues x N) input tape u b0 z0
  have price := NatAssign.price_bound Raw.ids preparePlan preparePlan_valid
    (magnitudeValues x N) (W+1) (fun i _=>magnitude_width x N W width precision i)
    (by simp [preparePlan,NatAssign.Instruction.literalWidth])
  have cost1 : c1≤3000*8^8*(W+3)^2 := by
    simpa only [preparePlan,List.length_cons,List.length_nil,Nat.add_assoc] using h1.trans price
  rw [preparePlan_values] at b1
  have mag := (IntegerNormSquare.magnitude_bits_length_le x.positive x.negative).trans
    (Nat.add_le_add_right (max_le width.1 width.2.1) 1)
  obtain ⟨c2,t,num,den,e2,h2,wn,wd,positive,value,_,_,zt,f2,bt⟩ := Raw.executes
    (IntegerNormSquare.magnitude x.positive x.negative) x.denominator N (W+1)
    valid mag (width.2.2.trans (by omega)) (precision.trans (by omega)) input tape v b1 z1
  refine ⟨c0+(c1+c2),t,num,den,e0.seq (e1.seq e2),?_,wn,wd,positive,?_,bt,zt,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans f2)⟩
  · have cost0 : c0≤300*(2*W+4) := by
      change c0≤300*(x.positive.bits.length+x.negative.bits.length+4) at h0
      rcases width with ⟨hp,hm,hd⟩
      exact h0.trans (Nat.mul_le_mul_left _ (by omega))
    apply (Nat.add_le_add cost0 (Nat.add_le_add cost1 h2)).trans
    unfold Raw.costBound costBound
    ring_nf
    omega
  · rwa [magnitude_value x valid nonnegative] at value

#print axioms executes
end Maxwell.Continuum.Calibration.RationalRoot.Signed
