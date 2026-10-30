import Maxwell.Continuum.CalibrationArrayDecode
import Maxwell.Continuum.NaturalBankDivMod

/-! One fixed runtime program decodes an actual Fourier-array index into
its polarization and three unsigned cube coordinates. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def ports : Finset ℕ := Finset.Icc 310 320
def prepare : List NatAssign.Instruction :=
  [.literal 312 3,.literal 313 1,.add 311 313,.add 311 313,.copy 313 314,.multiply 313 314]
def prepared (v : ℕ → ℕ) : ℕ → ℕ := NatAssign.values prepare v
def divModValues (v : ℕ → ℕ) (source divisor q r : ℕ) : ℕ → ℕ :=
  Function.update (Function.update v q (v source/v divisor)) r (v source%v divisor)
def first (v : ℕ → ℕ) : ℕ → ℕ := divModValues (prepared v) 310 312 315 316
def second (v : ℕ → ℕ) : ℕ → ℕ := divModValues (first v) 315 314 317 318
def output (v : ℕ → ℕ) : ℕ → ℕ := divModValues (second v) 318 313 319 320

def code : Code := .seq (NatAssign.code prepare)
  (.seq (NaturalDivMod.code 310 312 315 316)
    (.seq (NaturalDivMod.code 315 314 317 318) (NaturalDivMod.code 318 313 319 320)))

theorem prepared_side (v : ℕ → ℕ) : prepared v 313=aliasSide (v 311) := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,aliasSide]
  omega

theorem prepared_square (v : ℕ → ℕ) : prepared v 314=aliasSide (v 311)*aliasSide (v 311) := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,aliasSide]
  ring

theorem prepared_other (v : ℕ → ℕ) (i : ℕ) (h2 : i≠312) (h3 : i≠313) (h4 : i≠314) :
    prepared v i=v i := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,h2,h3,h4]

theorem output_polarization (v : ℕ → ℕ) : output v 316=decodedPolarization (v 310) := by
  simp [output,second,first,divModValues,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,decodedPolarization]

theorem output_coordinates (v : ℕ → ℕ) (j : Fin 3) :
    ![output v 317,output v 319,output v 320] j=decodedCoordinates (v 311) (v 310) j := by
  fin_cases j <;>
    simp [output,second,first,divModValues,
      prepared,prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,decodedCoordinates,aliasSide,show ∀ r : ℕ, r+(r+1)=2*r+1 by omega]

theorem divModValues_width (v : ℕ → ℕ) (ids : Finset ℕ) (source divisor q r B : ℕ)
    (hsource : source ∈ ids) (hv : ∀ i ∈ ids, (v i).bits.length ≤ B) :
    ∀ i ∈ ids, (divModValues v source divisor q r i).bits.length ≤ B := by
  intro i hi
  by_cases hir : i=r
  · subst i
    simp only [divModValues,Function.update_self]
    exact (RationalWords.bits_mono (Nat.mod_le _ _)).trans (hv source hsource)
  · by_cases hiq : i=q
    · subst i
      simp only [divModValues,Function.update_of_ne hir,Function.update_self]
      exact (RationalWords.bits_mono (Nat.div_le_self _ _)).trans (hv source hsource)
    · simpa only [divModValues,Function.update_of_ne hir,Function.update_of_ne hiq] using hv i hi

theorem prepared_width (v : ℕ → ℕ) (ids : Finset ℕ) (hports : ports ⊆ ids) (B : ℕ)
    (hv : ∀ i ∈ ids, (v i).bits.length ≤ B) :
    ∀ i ∈ ids, (prepared v i).bits.length ≤ 2*B+8 := by
  have hR := hv 311 (hports (by decide))
  have hside : (aliasSide (v 311)).bits.length ≤ B+3 := by
    have hm := RationalAccumulator.bits_mul_le 2 (v 311)
    have ha := RationalAccumulator.bits_add_le (2*v 311) 1
    rw [show (2 : ℕ).bits.length=2 by decide] at hm
    simp only [show (1 : ℕ).bits.length=1 by decide] at ha
    unfold aliasSide
    omega
  intro i hi
  by_cases h312 : i=312
  · subst i
    have he : prepared v 312=3 := by
      simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value]
    rw [he,show (3 : ℕ).bits.length=2 by decide]
    omega
  · by_cases h313 : i=313
    · subst i
      rw [prepared_side]
      omega
    · by_cases h314 : i=314
      · subst i
        rw [prepared_square]
        have hh := RationalAccumulator.bits_mul_le (aliasSide (v 311)) (aliasSide (v 311))
        omega
      · rw [prepared_other v i h312 h313 h314]
        exact (hv i hi).trans (by omega)

theorem executes (ids : Finset ℕ) (hids : ∀ i ∈ ids, 10 ≤ i) (hports : ports ⊆ ids)
    (hwork : NaturalQuotient.workPorts ⊆ ids) (v : ℕ → ℕ)
    (hzero : ∀ i ∈ NaturalQuotient.workPorts, v i=0) (B : ℕ) (hB : 2 ≤ B)
    (hw : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank ids v s.val)
    (hz : ∀ i, i<5 → RationalAccumulator.Blank s.val i) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ 2^110*(B+5)^2 ∧
      NatAssign.Bank ids (output v) t.val ∧
      (∀ i, i<5 → RationalAccumulator.Blank t.val i) ∧
      BinaryPrecision.Frame ({0,1,2,3,4} ∪ ids) s.val t.val := by
  have port (i : ℕ) (hi : i ∈ ports) : i ∈ ids := hports hi
  have valid : ∀ a ∈ prepare, a.Valid ids := by
    simp [prepare,NatAssign.Instruction.Valid,port 311 (by decide),port 312 (by decide),
      port 313 (by decide),port 314 (by decide)]
  have literals : ∀ a ∈ prepare, a.literalWidth ≤ B := by
    norm_num [prepare,NatAssign.Instruction.literalWidth]
    rw [show (3 : ℕ).bits.length=2 by decide]
    omega
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := fixedBankStage_executes ids (fun i hi => by have := hids i hi; omega)
    prepare valid (by decide) v B hw literals input tape s hs (fun i hi => hz i (by omega))
  change NatAssign.Bank ids (prepared v) u.val at b0
  have blank0 (i : ℕ) (hi : i<5) : RationalAccumulator.Blank u.val i := by
    by_cases hlt : i<4
    · exact z0 i hlt
    · have hi4 : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (f0.tapes 4 (by
        simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        have hn : 4 ∉ ids := fun h => by have := hids 4 h; omega
        simp [hn])) (hz 4 (by decide))
  have zero0 (i : ℕ) (hi : i ∈ NaturalQuotient.workPorts) : prepared v i=0 := by
    have h := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at h
    rw [prepared_other v i (by omega) (by omega) (by omega)]
    exact hzero i hi
  have w0 := prepared_width v ids hports B hw
  obtain ⟨c1,u1,e1,hc1,b1,z1,f1⟩ := NaturalDivMod.executes ids hids hwork
    310 312 315 316 (port _ (by decide)) (port _ (by decide)) (port _ (by decide))
    (port _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (prepared v) zero0 (by simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target]) (2*B+8) w0 input tape u b0 blank0
  change NatAssign.Bank ids (first v) u1.val at b1
  have zero1 (i : ℕ) (hi : i ∈ NaturalQuotient.workPorts) : first v i=0 := by
    have h := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at h
    simpa only [first,divModValues,Function.update_of_ne (show i≠315 by omega),
      Function.update_of_ne (show i≠316 by omega)] using zero0 i hi
  have w1 := divModValues_width (prepared v) ids 310 312 315 316 (2*B+8) (port _ (by decide)) w0
  have pos1 : 0 < first v 314 := by simp [first,divModValues,prepared_square,aliasSide]
  obtain ⟨c2,u2,e2,hc2,b2,z2,f2⟩ := NaturalDivMod.executes ids hids hwork
    315 314 317 318 (port _ (by decide)) (port _ (by decide)) (port _ (by decide))
    (port _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (first v) zero1 pos1 (2*B+8) w1 input tape u1 b1 z1
  change NatAssign.Bank ids (second v) u2.val at b2
  have zero2 (i : ℕ) (hi : i ∈ NaturalQuotient.workPorts) : second v i=0 := by
    have h := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at h
    simpa only [second,divModValues,Function.update_of_ne (show i≠317 by omega),
      Function.update_of_ne (show i≠318 by omega)] using zero1 i hi
  have w2 := divModValues_width (first v) ids 315 314 317 318 (2*B+8) (port _ (by decide)) w1
  have pos2 : 0 < second v 313 := by simp [second,first,divModValues,prepared_side,aliasSide]
  obtain ⟨c3,t,e3,hc3,b3,z3,f3⟩ := NaturalDivMod.executes ids hids hwork
    318 313 319 320 (port _ (by decide)) (port _ (by decide)) (port _ (by decide))
    (port _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (second v) zero2 pos2 (2*B+8) w2 input tape u2 b2 z2
  have f0' : BinaryPrecision.Frame ({0,1,2,3,4} ∪ ids) s.val u.val :=
    f0.mono (by intro i hi; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢; tauto)
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,z3,f0'.trans (f1.trans (f2.trans f3))⟩
  unfold stageCost at hc0
  have hsq : (2*B+8+2)^2=4*(B+5)^2 := by ring
  have hs0 : (B+2)^2 ≤ (B+5)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith only [hc0,hc1,hc2,hc3,hsq,hs0,Nat.zero_le ((B+5)^2)]

#print axioms executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
