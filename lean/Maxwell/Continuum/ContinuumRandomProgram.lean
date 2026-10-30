import Maxwell.Continuum.ContinuumFairDetuning
import Maxwell.Continuum.RandomBitsLawMachine

/-! The fixed random-reading loop computes the same detuning draw used in
the continuum good-event theorem, with an explicit logarithmic work bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Cost.Structured
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem random_work (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    RandomBitsMachine.cap (randomBitCount p S hm)≤
      34*(detuningBitCoefficient p+1)^2*(logSize S)^2 := by
  have hn := randomBitCount_linear p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have h : randomBitCount p S hm+1≤(detuningBitCoefficient p+1)*logSize S := by
    nlinarith only [hn,hℓ]
  calc
    _≤34*(randomBitCount p S hm+1)^2 := RandomBitsMachine.cap_bound _
    _≤34*((detuningBitCoefficient p+1)*logSize S)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
    _=_ := by ring

theorem random_executes (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hcount : s.val.tapes 240=BitTape.ofList (randomBitCount p S hm).bits)
    (hblank : s.val.tapes 241=BitTape.blank) :
    ∃cost t, Executes input tape RandomBitsMachine.code cost s t ∧
      cost≤34*(detuningBitCoefficient p+1)^2*(logSize S)^2 ∧
      t.val.tapes 241=BitTape.atEnd (RandomBitsMachine.bits tape s.val.randomCursor
        (randomBitCount p S hm)) ∧
      addressValue (RandomBitsMachine.bits tape s.val.randomCursor (randomBitCount p S hm))=
        (randomDraw p S hm (fun i => tape (s.val.randomCursor+i.val))).val ∧
      t.val.randomCursor=s.val.randomCursor+randomBitCount p S hm ∧
      RandomBitsMachine.Frame s.val t.val := by
  obtain ⟨cost,t,he,hc,ht,hcursor,hf⟩ := RandomBitsMachine.executes input tape
    (randomBitCount p S hm) s hcount hblank
  exact ⟨cost,t,he,hc.trans (random_work p S hm hm2 hu),ht,
    RandomBitsMachine.bits_binary_value tape s.val.randomCursor _,hcursor,hf⟩

#print axioms random_work
#print axioms random_executes

end Maxwell.Continuum.RealizationParameters
