import Maxwell.Continuum.CalibrationRootParameterPlan
import Maxwell.Cost.Structured.NatAssign.StoredLength

/-! Charged execution of all root-table sampling parameters from stored
scale and precision words. Division and word-length measurement are actual
machine programs, and all table memory and material payload tapes survive. -/
namespace Maxwell.Continuum.Calibration.RootParameters
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 3500000
attribute [local irreducible] MasterConstants.exponent

def code : Code := .seq (NatAssign.code prepare)
  (.seq (PhysicalMaterial.FixedSubtract.code 338 1)
    (.seq (NaturalQuotient.code 338 332 335)
      (.seq (NatAssign.code gridPlan)
        (.seq (WordLength.code 336 340) (NatAssign.code precisionPlan)))))

def firstWidth (B : ℕ) : ℕ := 2^10*(B+1)
def secondWidth (B : ℕ) : ℕ := 2^7*(firstWidth B+1)
def outputWidth (B : ℕ) : ℕ := 2^6*(secondWidth B+1)

theorem inputWidth_le_outputWidth (B : ℕ) : B≤outputWidth B := by
  unfold outputWidth secondWidth firstWidth
  omega

theorem outputWidth_linear (B : ℕ) : outputWidth B≤2^24*(B+2) := by
  unfold outputWidth secondWidth firstWidth
  omega
def costBound (B : ℕ) : ℕ := stageCost B+(29*firstWidth B+31)+
  2^100*(firstWidth B+2)^2+stageCost (firstWidth B)+
  (48*(secondWidth B+1)^2+1)+stageCost (secondWidth B)

private theorem stage (plan : List NatAssign.Instruction)
    (valid : ∀a∈plan,a.Valid ids) (length : plan.length≤25)
    (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (literals : ∀a∈plan,a.literalWidth≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : ∀i,i<5→Blank s.val i) :
    ∃steps t,Executes input tape (NatAssign.code plan) steps s t ∧ steps≤stageCost B ∧
      NatAssign.Bank ids (NatAssign.values plan v) t.val ∧
      (∀i,i<5→Blank t.val i) ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩ := fixedBankStage_executes ids
    (fun i hi => by have := ids_lower i hi;omega) plan valid length v B width literals
    input tape s bank (fun i hi => scratch i (by omega))
  refine ⟨steps,t,he,hc,bt,?_,ft.mono ?_⟩
  · intro i hi
    by_cases hs : i<4
    · exact zt i hs
    · have hi4 : i=4 := by omega
      subst i
      apply RationalAccumulator.blank_of_eq (ft.tapes 4 ?_) (scratch 4 (by decide))
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      exact not_or_intro (by omega) (by intro hm;have := ids_lower 4 hm;omega)
  · intro i hi
    simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto

private theorem update_width (v : ℕ→ℕ) (B target value : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B) (bound : value.bits.length≤B) :
    ∀i∈ids,((Function.update v target value) i).bits.length≤B := by
  intro i hi
  by_cases same : i=target
  · simpa only [same,Function.update_self] using bound
  · simpa only [Function.update_of_ne same] using width i hi

private theorem bits_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 3*MasterConstants.exponent+4≤B)
    (denominator : 0<v 332) (width : ∀i∈ids,(v i).bits.length≤B)
    (zero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : ∀i,i<5→Blank s.val i) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤costBound B ∧
      NatAssign.Bank ids (values v) t.val ∧ (∀i,i<5→Blank t.val i) ∧
      (∀i∈ids,(values v i).bits.length≤outputWidth B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have pwidth : ∀i∈ids,(prepared v i).bits.length≤firstWidth B := by
    intro i hi
    have hh := NatAssign.values_width_bound ids prepare prepare_valid v B width
      (prepare_literals B (by omega)) i hi
    simpa only [prepared,firstWidth,prepare_length] using (Nat.le_add_right _ _).trans hh
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := stage prepare prepare_valid (by rw [prepare_length];decide)
    v B width (prepare_literals B (by omega)) input tape s bank scratch
  have positive : 1≤prepared v 338 := by rw [prepared_numerator];omega
  obtain ⟨c1,s1,e1,hc1,w1,f1⟩ := PhysicalMaterial.FixedSubtract.executes 338 1
    (prepared v 338) positive input tape s0 (b0 338 (by decide))
  have b1 : NatAssign.Bank ids (decremented v) s1.val := by
    intro i hi
    by_cases same : i=338
    · simpa only [same,decremented,Function.update_self] using w1
    · simpa only [decremented,prepared,Function.update_of_ne same] using
        RationalAccumulator.word_of_eq (f1.tapes i (by simpa using same)) (b0 i hi)
  have z1 : ∀i,i<5→Blank s1.val i := fun i hi =>
    RationalAccumulator.blank_of_eq (f1.tapes i (by simp only [Finset.mem_singleton];omega)) (z0 i hi)
  have dwidth : ∀i∈ids,(decremented v i).bits.length≤firstWidth B :=
    update_width (prepared v) _ _ _ pwidth ((bits_mono (Nat.sub_le _ _)).trans (pwidth 338 (by decide)))
  have dden : decremented v 332=v 332 := by
    rw [decremented,Function.update_of_ne (by decide : (332:ℕ)≠338),prepared_other v 332 (by decide)]
  have dzero : ∀i∈NaturalQuotient.workPorts,decremented v i=0 := by
    intro i hi
    have bound : i≤223 := by
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    rw [decremented,Function.update_of_ne (by omega),prepared_other v i (by omega)]
    exact zero i hi
  obtain ⟨c2,s2,e2,hc2,b2,z2,f2⟩ := NaturalQuotient.executes ids ids_lower (by decide)
    338 332 335 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (decremented v) dzero (by rw [dden];exact denominator) (firstWidth B) dwidth input tape s1 b1 z1
  have qwidth : ∀i∈ids,(divided v i).bits.length≤firstWidth B :=
    update_width (decremented v) _ _ _ dwidth
      ((bits_mono (Nat.div_le_self _ _)).trans (dwidth 338 (by decide)))
  have firstLarge : 4≤firstWidth B := by unfold firstWidth;omega
  obtain ⟨c3,s3,e3,hc3,b3,z3,f3⟩ := stage gridPlan gridPlan_valid (by rw [gridPlan_length];decide)
    (divided v) (firstWidth B) qwidth (gridPlan_literals _ (by omega)) input tape s2 b2 z2
  have gwidth : ∀i∈ids,(gridded v i).bits.length≤secondWidth B := by
    intro i hi
    have hh := NatAssign.values_width_bound ids gridPlan gridPlan_valid (divided v) (firstWidth B)
      qwidth (gridPlan_literals _ (by omega)) i hi
    simpa only [gridded,secondWidth,gridPlan_length] using (Nat.le_add_right _ _).trans hh
  obtain ⟨c4,s4,e4,hc4,b4,z4,f4⟩ := NatAssign.stored_length ids 336 340
    (by decide) (by decide) (by decide) (by decide) (gridded v) (gridded_outputs v).2.2
    input tape s3 b3 (fun i hi => z3 i (by omega))
  have mwidth : ∀i∈ids,(measured v i).bits.length≤secondWidth B := by
    apply update_width (gridded v) _ _ _ gwidth
    have small : (gridded v 336).bits.length.bits.length≤(gridded v 336).bits.length := by
      rw [Nat.size_eq_bits_len,Nat.size_le]
      exact Nat.lt_two_pow_self
    exact small.trans (gwidth 336 (by decide))
  have z4' : ∀i,i<5→Blank s4.val i := fun i hi =>
    RationalAccumulator.blank_of_eq (f4.tapes i (by simp only [Finset.mem_singleton];omega)) (z3 i hi)
  have secondLarge : 4≤secondWidth B := by unfold secondWidth;omega
  obtain ⟨c5,t,e5,hc5,bt,zt,f5⟩ := stage precisionPlan precisionPlan_valid (by rw [precisionPlan_length];decide)
    (measured v) (secondWidth B) mwidth (precisionPlan_literals _ secondLarge) input tape s4 b4 z4'
  have f1' : BinaryPrecision.Frame workspace s0.val s1.val := f1.mono (by decide)
  have f4' : BinaryPrecision.Frame workspace s3.val s4.val := f4.mono (by decide)
  have twidth : ∀i∈ids,(values v i).bits.length≤outputWidth B := by
    intro i hi
    have hh := NatAssign.values_width_bound ids precisionPlan precisionPlan_valid (measured v)
      (secondWidth B) mwidth (precisionPlan_literals _ secondLarge) i hi
    simpa only [values,outputWidth,precisionPlan_length] using (Nat.le_add_right _ _).trans hh
  refine ⟨c0+(c1+(c2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),?_,
    bt,zt,twidth,f0.trans (f1'.trans (f2.trans (f3.trans (f4'.trans f5))))⟩
  have h1 : c1≤29*firstWidth B+31 := by
    have := pwidth 338 (by decide)
    unfold PhysicalMaterial.FixedSubtract.costBound at hc1
    omega
  have h4 : c4≤48*(secondWidth B+1)^2+1 := hc4.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (gwidth 336 (by decide)) _) 2)) _)
  unfold costBound
  omega

theorem costBound_polynomial (B : ℕ) : costBound B≤2^150*(B+2)^2 := by
  unfold costBound stageCost secondWidth firstWidth
  nlinarith [Nat.zero_le B]

theorem outputs {v : ℕ→ℕ} {t : Store} (denominator : 0<v 332)
    (bank : NatAssign.Bank ids (values v) t.val) :
    Word t.val 335 (rootDegree ((v 330:ℚ)/v 332) (v 333) (v 334)) ∧
    Word t.val 331 (rootSamplingGrid ((v 330:ℚ)/v 332) (v 333) (v 334)) ∧
    Word t.val 640 (rootSamplingBits ((v 330:ℚ)/v 332) (v 333) (v 334)) := by
  obtain ⟨hd,hg,hb⟩ := values_outputs v
  exact ⟨by simpa only [hd,degree_eq _ _ _ _ denominator] using bank 335 (by decide),
    by simpa only [hg,grid_eq _ _ _ _ denominator] using bank 331 (by decide),
    by simpa only [hb,bits_eq _ _ _ _ denominator] using bank 640 (by decide)⟩

theorem selected_executes (L r N : ℕ) (hL : 0<L) (v : ℕ→ℕ)
    (selected : v 330=2*FiniteAlgorithm.size L r N ∧ v 332=L ∧
      v 333=FiniteAlgorithm.precision L r N ∧ v 334=FiniteAlgorithm.rootBits L r N)
    (B : ℕ) (hB : 3*MasterConstants.exponent+4≤B)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (zero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : ∀i,i<5→Blank s.val i) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤2^150*(B+2)^2 ∧
      Word t.val 335 (rootDegree (FiniteAlgorithm.scale L r N)
        (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rootBits L r N)) ∧
      Word t.val 331 (rootSamplingGrid (FiniteAlgorithm.scale L r N)
        (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rootBits L r N)) ∧
      Word t.val 640 (rootSamplingBits (FiniteAlgorithm.scale L r N)
        (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rootBits L r N)) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have denominator : 0<v 332 := by rw [selected.2.1];exact hL
  obtain ⟨steps,t,he,hc,hbank,_,_,frame⟩ := executes v B hB denominator width zero
    input tape s bank scratch
  have result := outputs denominator hbank
  rw [selected.1,selected.2.1,selected.2.2.1,selected.2.2.2] at result
  have scale : ((2*FiniteAlgorithm.size L r N:ℕ):ℚ)/L=FiniteAlgorithm.scale L r N := by
    simp only [FiniteAlgorithm.scale,torusScale,Nat.cast_mul,Nat.cast_ofNat]
  rw [scale] at result
  exact ⟨steps,t,he,hc.trans (costBound_polynomial B),result.1,result.2.1,result.2.2,frame⟩

#print axioms executes
#print axioms costBound_polynomial
#print axioms outputs
#print axioms selected_executes
end Maxwell.Continuum.Calibration.RootParameters
