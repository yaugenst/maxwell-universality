import Maxwell.Continuum.GlueRuntimeExponential

/-! One fixed glue evaluator branches on the exact runtime threshold and
executes the stored Taylor count only on the reciprocal branch. -/
namespace Maxwell.Continuum.GlueMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def zeroValues (a b N : ℕ) : ℕ→ℕ := NatAssign.values GlueMachine.writeZero (comparisonValues a b N)
def finalValues (a b N : ℕ) : ℕ→ℕ :=
  if (a:ℚ)/b≤1/((N:ℚ)+1) then zeroValues a b N else expFinalValues a b N
def result (a b N : ℕ) : RationalDataflow.Parts :=
  if (a:ℚ)/b≤1/((N:ℚ)+1) then RationalDataflow.Parts.literal 0 else expResult a b N
def core : Code := .seq (NatAssign.code setup)
  (.seq comparisonCode (.branch 35 expCode (NatAssign.code GlueMachine.writeZero)))
def costBound (N W : ℕ) : ℕ :=
  2^60*(W+2)^2+2^25*(setupWidth W+2)^2+1+2^50*(setupWidth W+2)^2+expCost N W

theorem zeroValues_counter (a b N : ℕ) : zeroValues a b N 641=GlueMachine.order N := by
  simpa [zeroValues,GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value] using (comparisonValues_saved a b N).2.1

theorem zeroValues_output (a b N : ℕ) :
    zeroValues a b N 602=0 ∧ zeroValues a b N 603=0 ∧ zeroValues a b N 604=1 := by
  simp [zeroValues,GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem finalValues_output (a b N : ℕ) :
    finalValues a b N 602=(result a b N).positive ∧
    finalValues a b N 603=(result a b N).negative ∧
    finalValues a b N 604=(result a b N).denominator := by
  unfold finalValues result
  split_ifs
  · simpa only [RationalDataflow.Parts.literal,Rat.num_zero,Int.toNat_zero,neg_zero,Rat.den_zero]
      using zeroValues_output a b N
  · exact expFinalValues_output a b N

theorem result_value (a b N : ℕ) (hb : 0<b) :
    (result a b N).value=(Profile.glueApprox ((a:ℚ)/b) N).center := by
  unfold result Profile.glueApprox
  split_ifs with h
  · exact RationalDataflow.Parts.literal_value 0
  · have ha : 0<a := by
      have hq : (0:ℚ)<(a:ℚ)/b := lt_trans (by positivity) (lt_of_not_ge h)
      have hnum := (div_pos_iff_of_pos_right (show (0:ℚ)<b by exact_mod_cast hb)).mp hq
      exact_mod_cast hnum
    rw [expResult_value a b N ha]
    congr 2
    simp only [neg_div,one_div,inv_div]

theorem result_valid (a b N : ℕ) (hb : 0<b) : (result a b N).Valid := by
  unfold result
  split_ifs with h
  · exact RationalDataflow.Parts.literal_valid 0
  · apply expResult_valid
    have hq : (0:ℚ)<(a:ℚ)/b := lt_trans (by positivity) (lt_of_not_ge h)
    have hnum := (div_pos_iff_of_pos_right (show (0:ℚ)<b by exact_mod_cast hb)).mp hq
    exact_mod_cast hnum

theorem zero_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (comparisonValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (NatAssign.code GlueMachine.writeZero) cost s t ∧
      cost≤2^50*(setupWidth W+2)^2 ∧ NatAssign.Bank ids (zeroValues a b N) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  have hv : ∀i∈GlueMachine.writeZero,i.Valid ids := by
    simp [GlueMachine.writeZero,NatAssign.Instruction.Valid,ids,GlueMachine.ids,
      SelectedParameters.Compare.ids,GlueMachine.extra,RationalTaylor.ids]
  obtain ⟨cost,t,ex,hcost,bt,zt,ft⟩ := NatAssign.executes ids ids_ge GlueMachine.writeZero hv
    (comparisonValues a b N) input tape s hs hz
  have hp := NatAssign.price_bound ids GlueMachine.writeZero hv (comparisonValues a b N) (setupWidth W)
    (comparisonValues_width a b N W ha hb hN hW)
    (by simp [GlueMachine.writeZero,NatAssign.Instruction.literalWidth,setupWidth];omega)
  have hlen : GlueMachine.writeZero.length=3 := rfl
  rw [hlen] at hp
  exact ⟨cost,t,ex,hcost.trans (hp.trans (Nat.mul_le_mul_right _ (by norm_num))),bt,zt,ft.mono (by decide)⟩

theorem core_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t finalWord,Executes input tape core cost s t ∧ cost≤costBound N W ∧
      NatAssign.Bank (ids.erase 641) (finalValues a b N) t.val ∧ NatAssign.Scratch t.val ∧
      BankArray.Word t.val 641 finalWord ∧ finalWord.length=(GlueMachine.order N).bits.length ∧
      Word t.val 602 (result a b N).positive ∧ Word t.val 603 (result a b N).negative ∧
      Word t.val 604 (result a b N).denominator ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0,_,_⟩ := setup_executes a b N W ha hb hN hW input tape s hs hz
  obtain ⟨c1,s1,e1,hc1,sg,b1,z1,f1⟩ := comparison_executes a b N W ha hb hN hW hb0 input tape s0 b0 z0
  by_cases hsmall : (a:ℚ)/b≤1/((N:ℚ)+1)
  · obtain ⟨c2,t,e2,hc2,bt,zt,ft⟩ := zero_executes a b N W ha hb hN hW input tape s1 b1 z1
    have hfalse : s1.val.registers 35=false := by rw [sg];exact decide_eq_false (not_lt.mpr hsmall)
    have bank : NatAssign.Bank (ids.erase 641) (finalValues a b N) t.val := by
      intro i hi
      simpa only [finalValues,ite_eq_left hsmall] using bt i (Finset.mem_of_mem_erase hi)
    have hout := finalValues_output a b N
    refine ⟨c0+(c1+(1+c2)),t,(GlueMachine.order N).bits,e0.seq (e1.seq (Executes.no hfalse e2)),
      ?_,bank,zt,?_,rfl,?_,?_,?_,f0.trans (f1.trans ft)⟩
    · unfold costBound
      omega
    · obtain ⟨origin,hh⟩ := bt 641 (by decide)
      exact ⟨origin,by simpa only [zeroValues_counter] using hh⟩
    · simpa only [hout.1] using bank 602 (by decide)
    · simpa only [hout.2.1] using bank 603 (by decide)
    · simpa only [hout.2.2] using bank 604 (by decide)
  · have ha0 : 0<a := by
      have hq : (0:ℚ)<(a:ℚ)/b := lt_trans (by positivity) (lt_of_not_ge hsmall)
      have hnum := (div_pos_iff_of_pos_right (show (0:ℚ)<b by exact_mod_cast hb0)).mp hq
      exact_mod_cast hnum
    obtain ⟨c2,t,word,e2,hc2,bt,zt,wt,hl,_,ft⟩ := exp_executes a b N W ha hb hN hW ha0 input tape s1 b1 z1
    have htrue : s1.val.registers 35=true := by rw [sg];exact decide_eq_true (lt_of_not_ge hsmall)
    have bank : NatAssign.Bank (ids.erase 641) (finalValues a b N) t.val := by
      simpa only [finalValues,ite_eq_right hsmall] using bt
    have hout := finalValues_output a b N
    refine ⟨c0+(c1+(1+c2)),t,word,e0.seq (e1.seq (Executes.yes htrue e2)),
      ?_,bank,zt,wt,hl,?_,?_,?_,f0.trans (f1.trans ft)⟩
    · unfold costBound
      omega
    · simpa only [hout.1] using bank 602 (by decide)
    · simpa only [hout.2.1] using bank 603 (by decide)
    · simpa only [hout.2.2] using bank 604 (by decide)

#print axioms core_executes
#print axioms result_value
end Maxwell.Continuum.GlueMachine.Runtime
