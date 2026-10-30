import Maxwell.Continuum.RationalSquareRootMachinePrepare

/-! Fixed runtime code for the literal rational square-root approximation,
with all scaling arithmetic included in its polynomial bit-cost bound. -/

namespace Maxwell.Continuum.Calibration.RationalRoot

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def code : Code := .seq prepareCode NaturalRoot.code
def costBound (N W : ℕ) : ℕ := 2^104*(N+W+10)^7

theorem total_cost (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W) :
    prepareCost N W+NaturalRoot.costBound (radicand A D N)≤costBound N W := by
  have hroot := NaturalRoot.costBound_polynomial (radicand A D N)
  have hbits := radicand_bits A D N W hA hD
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hbits 6) 5
  have bound : NaturalRoot.costBound (radicand A D N)≤2^64*(2*W+3*N+7)^5 := by
    apply hroot.trans
    exact Nat.mul_le_mul_left _ (by simpa only [Nat.add_assoc] using hpow)
  apply (Nat.add_le_add_left bound _).trans
  unfold prepareCost Parameters.PowerMachine.costBound Parameters.PowerMachine.bodyCost
    SelectedParameters.DynamicPower.width costBound
  ring_nf
  omega

theorem executes (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W)
    (hN : N.bits.length≤W) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues A D N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound N W ∧
      Word t.val 32 (Nat.sqrt (radicand A D N)) ∧ Word t.val 548 (D*2^N) ∧
      Word t.val 542 A ∧ Word t.val 543 D ∧ Word t.val 544 N ∧
      NatAssign.Bank NaturalRoot.fullIds (NaturalRoot.doneValues (radicand A D N)) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := prepare_executes A D N W hA hD hN input tape s hs hz
  obtain ⟨c1,t,e1,hc1,root,b1,z1,f1⟩ := NaturalRoot.executes (radicand A D N)
    input tape u (prepared_root_bank A D N b0) z0
  have den : Word t.val 548 (D*2^N) := by
    simpa [preparedValues] using RationalAccumulator.word_of_eq (f1.tapes 548 (by decide))
      (b0 548 (by decide))
  have num : Word t.val 542 A := by
    simpa [preparedValues,inputValues] using RationalAccumulator.word_of_eq (f1.tapes 542 (by decide))
      (b0 542 (by decide))
  have denominator : Word t.val 543 D := by
    simpa [preparedValues,inputValues] using RationalAccumulator.word_of_eq (f1.tapes 543 (by decide))
      (b0 543 (by decide))
  have prec : Word t.val 544 N := by
    simpa [preparedValues,inputValues] using RationalAccumulator.word_of_eq (f1.tapes 544 (by decide))
      (b0 544 (by decide))
  exact ⟨c0+c1,t,e0.seq e1,(Nat.add_le_add hc0 hc1).trans (total_cost A D N W hA hD),
    root,den,num,denominator,prec,b1,z1,f0.trans (f1.mono (by decide))⟩

theorem rational_compiled_run (r : ℚ) (N W : ℕ)
    (hA : r.num.natAbs.bits.length≤W) (hD : r.den.bits.length≤W) (hN : N.bits.length≤W)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues r.num.natAbs r.den N) s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃ t : Store, ∃ a d : ℕ,
      (runPriced (code.compile.next input tape) (costBound N W+1) s.val).finished=
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound N W+1) s.val).instructions≤costBound N W ∧
      Word t.val 32 a ∧ Word t.val 548 d ∧ 0<d ∧
      (a:ℚ)/d=sqrtRationalCenter r N ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cost,t,run,hcost,root,den,_,_,_,_,scratch,frame⟩ :=
    executes r.num.natAbs r.den N W hA hD hN input tape s hs hz
  have hr := run.compiled_run (costBound N W+1) (by omega)
  refine ⟨t,Nat.sqrt (radicand r.num.natAbs r.den N),r.den*2^N,hr.1,hr.2 ▸ hcost,
    root,den,by positivity,?_,scratch,frame⟩
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using literal_value r N

#print axioms executes
#print axioms rational_compiled_run

end Maxwell.Continuum.Calibration.RationalRoot
