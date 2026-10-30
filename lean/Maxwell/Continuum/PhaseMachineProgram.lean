import Maxwell.Continuum.PhaseMachineStages

/-! Composed Boolean phase evaluation with runtime signed rational operands. -/

namespace Maxwell.Continuum.PhaseMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def core (negative : Bool) (base : ℕ→Sign) (Q N : ℕ) : Code :=
  .seq (Machin.program (Calibration.phaseBits Q N))
    (.seq (NatAssign.code prepareMagnitude)
      (.seq RationalMagnitude.program
        (.seq (NatAssign.code prepareTaylor) (RationalTaylor.program (fractionSigns negative base) (order Q N)))))

/-- Register 200 stores the input sign; the two rational operand words are 630 and 631. -/
def program (base : ℕ→Sign) (Q N : ℕ) : Code := .branch 200 (core true base Q N) (core false base Q N)

def costBound (Q N W : ℕ) : ℕ :=
  Machin.costBound (Calibration.phaseBits Q N)+2*stageCost Q N W+
    300*(2*Machin.wordWidth (Calibration.phaseBits Q N)+4)+
    RationalTaylor.costBound (order Q N) (preparedWidth Q N W)

theorem machin_seed_bank (a b Q N : ℕ) (s t : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val)
    (hp : Word t.val 623 (Machin.numeratorPositive (Calibration.phaseBits Q N)))
    (hn : Word t.val 624 (Machin.numeratorNegative (Calibration.phaseBits Q N)))
    (hd : Word t.val 625 (Machin.commonDenominator (Calibration.phaseBits Q N)))
    (hf : BinaryPrecision.Frame Machin.allWorkspace s.val t.val) :
    NatAssign.Bank ids (seedValues a b Q N) t.val := by
  intro i hi
  by_cases h623 : i=623
  · subst i; simpa only [seedValues,ite_true] using hp
  by_cases h624 : i=624
  · subst i; simpa [seedValues] using hn
  by_cases h625 : i=625
  · subst i; simpa [seedValues] using hd
  have ho : i∉Machin.allWorkspace := by
    simp only [ids,RationalTaylor.ids,RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [Machin.allWorkspace,Machin.allIds,RationalArctan.ids,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  simpa only [seedValues,ite_eq_right h623,ite_eq_right h624,ite_eq_right h625] using
    word_of_eq (hf.tapes i ho) (hs i hi)

theorem core_executes (negative : Bool) (base : ℕ→Sign) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val)
    (hm : NatAssign.Bank Machin.allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (core negative base Q N) cost s t ∧ cost≤costBound Q N W ∧
      Ready (argumentNumerator a Q N) (argumentDenominator b Q N) (fractionSigns negative base) (order Q N) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,p0,n0,d0,z0,f0⟩ := Machin.executes (Calibration.phaseBits Q N) input tape s hm hsc
  have b0 := machin_seed_bank a b Q N s s0 hs p0 n0 d0 f0
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := stage_executes Q N W prepareMagnitude stages_valid.1
    (by decide) (by simp [prepareMagnitude,NatAssign.Instruction.literalWidth]) (by decide)
    (seedValues a b Q N) (fun i _ => seed_width a b Q N W ha hb i) input tape s0 b0 z0
  rw [prepareMagnitude_values] at b1
  obtain ⟨c2,s2,e2,h2,b2,z2,f2,_⟩ := RationalMagnitude.executes ids (by decide) ids_ge
    (beforeMagnitude a b Q N) (beforeMagnitude_inputs a b Q N).2.2 input tape s1 b1 z1
  have b2' : NatAssign.Bank ids (afterMagnitude a b Q N) s2.val := by
    simpa only [(beforeMagnitude_inputs a b Q N).1,(beforeMagnitude_inputs a b Q N).2.1,
      afterMagnitude,piMagnitude] using b2
  have h2' : c2≤300*(2*Machin.wordWidth (Calibration.phaseBits Q N)+4) := by
    rw [(beforeMagnitude_inputs a b Q N).1,(beforeMagnitude_inputs a b Q N).2.1] at h2
    have hp := Machin.parts_width (Calibration.phaseBits Q N)
    exact h2.trans (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := stage_executes Q N W prepareTaylor stages_valid.2
    (by decide) (by simp [prepareTaylor,NatAssign.Instruction.literalWidth]; decide) (by decide)
    (afterMagnitude a b Q N) (fun i _ => afterMagnitude_width a b Q N W ha hb i) input tape s2 b2' z2
  change NatAssign.Bank ids (preparedValues a b Q N) s3.val at b3
  have hsub : RationalTaylor.ids⊆ids := by decide
  obtain ⟨c4,t,e4,h4,ht,f4⟩ := RationalTaylor.program_executes (preparedValues a b Q N)
    (fractionSigns negative base) (order Q N) (preparedWidth Q N W)
    (by unfold preparedWidth; omega)
    (fun i hi => prepared_width a b Q N W ha hb i (hsub hi)) input tape s3
    (fun i hi => b3 i (hsub hi)) z3
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,?_,
    (f0.mono (by decide)).trans (f1.trans ((f2.mono (by decide)).trans (f3.trans (f4.mono (by decide)))))⟩
  · unfold costBound
    omega
  · simpa only [(preparedValues_inputs a b Q N).1,(preparedValues_inputs a b Q N).2] using ht

theorem executes (negative : Bool) (base : ℕ→Sign) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val)
    (hm : NatAssign.Bank Machin.allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=negative) :
    ∃ cost t, Executes input tape (program base Q N) cost s t ∧ cost≤costBound Q N W+1 ∧
      Ready (argumentNumerator a Q N) (argumentDenominator b Q N) (fractionSigns negative base) (order Q N) t ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,ht,hf⟩ := core_executes negative base a b Q N W ha hb input tape s hs hm hsc
  refine ⟨1+cost,t,?_,by omega,ht,hf⟩
  cases negative with
  | false => exact Executes.no hsg he
  | true => exact Executes.yes hsg he

theorem compiled_cos_computes (negative : Bool) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val)
    (hm : NatAssign.Bank Machin.allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=negative) :
    ∃ (cost : ℕ) (t : Store) (p n d : ℕ),
      (runPriced ((program cosineSigns Q N).compile.next input tape) (costBound Q N W+2) s.val).finished=
        some (t.place (program cosineSigns Q N).size) ∧
      (runPriced ((program cosineSigns Q N).compile.next input tape) (costBound Q N W+2) s.val).instructions=cost ∧
      cost≤costBound Q N W+1 ∧ Word t.val 602 p ∧ Word t.val 603 n ∧ Word t.val 604 d ∧ 0<d ∧
      (Calibration.cosTurnApprox (signedFraction negative a b) Q N).center=((p:ℚ)-n)/d := by
  obtain ⟨cost,t,he,hc,ht,_⟩ := executes negative cosineSigns a b Q N W ha hb input tape s hs hm hsc hsg
  obtain ⟨hrun,hcost⟩ := he.compiled_run (costBound Q N W+2) (by omega)
  refine ⟨cost,t,_,_,_,hrun,hcost,hc,?_,?_,?_,?_,cosTurnApprox_center negative a b Q N hb0⟩
  · simpa [values] using ht.bank 602 (by decide)
  · simpa [values] using ht.bank 603 (by decide)
  · simpa [values] using ht.bank 604 (by decide)
  · exact RationalTaylor.denominator_pos (argumentDenominator_pos hb0 Q N) (order Q N)

theorem compiled_sin_computes (negative : Bool) (a b Q N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val)
    (hm : NatAssign.Bank Machin.allIds (fun _ => 0) s.val) (hsc : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=negative) :
    ∃ (cost : ℕ) (t : Store) (p n d : ℕ),
      (runPriced ((program sineSigns Q N).compile.next input tape) (costBound Q N W+2) s.val).finished=
        some (t.place (program sineSigns Q N).size) ∧
      (runPriced ((program sineSigns Q N).compile.next input tape) (costBound Q N W+2) s.val).instructions=cost ∧
      cost≤costBound Q N W+1 ∧ Word t.val 602 p ∧ Word t.val 603 n ∧ Word t.val 604 d ∧ 0<d ∧
      (Calibration.sinTurnApprox (signedFraction negative a b) Q N).center=((p:ℚ)-n)/d := by
  obtain ⟨cost,t,he,hc,ht,_⟩ := executes negative sineSigns a b Q N W ha hb input tape s hs hm hsc hsg
  obtain ⟨hrun,hcost⟩ := he.compiled_run (costBound Q N W+2) (by omega)
  refine ⟨cost,t,_,_,_,hrun,hcost,hc,?_,?_,?_,?_,sinTurnApprox_center negative a b Q N hb0⟩
  · simpa [values] using ht.bank 602 (by decide)
  · simpa [values] using ht.bank 603 (by decide)
  · simpa [values] using ht.bank 604 (by decide)
  · exact RationalTaylor.denominator_pos (argumentDenominator_pos hb0 Q N) (order Q N)

#print axioms core_executes
#print axioms executes
#print axioms compiled_cos_computes
#print axioms compiled_sin_computes

end Maxwell.Continuum.PhaseMachine
