import Maxwell.Continuum.GlueRuntimeExponentialData
import Maxwell.Continuum.RationalTaylorRuntime

/-! The glue exponential executes one fixed alternating Taylor loop, driven
by the count actually computed from the stored requested precision. -/
namespace Maxwell.Continuum.GlueMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def expCode : Code := .seq (NatAssign.code GlueMachine.prepareExp)
  (RationalTaylor.Runtime.program RationalTaylor.Runtime.negativeCycle 641)
def expCost (N W : ℕ) : ℕ := 2^50*(setupWidth W+2)^2+
  RationalTaylor.Runtime.costBound (GlueMachine.order N) (preparedWidth W) (GlueMachine.order N).bits.length
def expFinalValues (a b N i : ℕ) : ℕ :=
  if i∈RationalTaylor.Runtime.ids then RationalTaylor.Runtime.values b a negativeSigns (GlueMachine.order N) i
  else preparedValues a b N i

theorem expFinalValues_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (i : ℕ) (hi : i∈ids) :
    (expFinalValues a b N i).bits.length≤resultWidth N W := by
  have hPW : W≤preparedWidth W := by unfold preparedWidth;omega
  have hwide : preparedWidth W≤resultWidth N W := by
    unfold resultWidth RationalTaylor.width
    nlinarith
  unfold expFinalValues
  split_ifs
  · exact (RationalTaylor.Runtime.values_width b a negativeSigns (GlueMachine.order N) (GlueMachine.order N)
      (preparedWidth W) le_rfl (hb.trans hPW) (ha.trans hPW) i).trans (Nat.le_succ _)
  · exact (preparedValues_width a b N W ha hb hN hW i hi).trans hwide

theorem expFinalValues_output (a b N : ℕ) :
    expFinalValues a b N 602=(expResult a b N).positive ∧
    expFinalValues a b N 603=(expResult a b N).negative ∧
    expFinalValues a b N 604=(expResult a b N).denominator := by
  simp [expFinalValues,RationalTaylor.Runtime.ids,RationalTaylor.Runtime.values,
    RationalTaylor.ids,RationalTaylor.values,expResult]

theorem exp_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (ha0 : 0<a)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (comparisonValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t finalWord,Executes input tape expCode cost s t ∧ cost≤expCost N W ∧
      NatAssign.Bank (ids.erase 641) (expFinalValues a b N) t.val ∧ NatAssign.Scratch t.val ∧
      BankArray.Word t.val 641 finalWord ∧ finalWord.length=(GlueMachine.order N).bits.length ∧
      GlueMachine.Output (Maxwell.Certificate.Elementary.expApprox (-((b:ℚ)/a)) (N+1) N).center
        (resultWidth N W) t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,u,e0,hc0,bu,zu,f0⟩ := prepareExp_executes a b N W ha hb hN hW input tape s hs hz
  have sub : RationalTaylor.Runtime.ids⊆ids := by decide
  have wc : Word u.val 641 (GlueMachine.order N) := by
    have hh := bu 641 (by decide)
    simpa only [(preparedValues_saved a b N).2.1] using hh
  obtain ⟨origin,wc⟩ := wc
  obtain ⟨c1,t,finalWord,e1,hc1,ht,hword,hl,ft⟩ := RationalTaylor.Runtime.program_executes
    RationalTaylor.Runtime.negativeCycle 641 (GlueMachine.order N) (preparedWidth W) (preparedValues a b N)
    (by decide) (by decide) (by unfold preparedWidth;omega)
    (fun i hi => preparedValues_width a b N W ha hb hN hW i (sub hi))
    input tape (GlueMachine.order N).bits origin u (addressValue_bits _) wc (fun i hi => bu i (sub hi)) zu
  have hready : RationalTaylor.Runtime.Ready b a negativeSigns (GlueMachine.order N) t := by
    simpa only [(preparedValues_inputs a b N).1,(preparedValues_inputs a b N).2,
      RationalTaylor.Runtime.negativeCycle_signs] using ht.data
  have bank : NatAssign.Bank (ids.erase 641) (expFinalValues a b N) t.val := by
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    have him := (Finset.mem_erase.mp hi).2
    by_cases hit : i∈RationalTaylor.Runtime.ids
    · simpa only [expFinalValues,ite_eq_left hit] using hready.bank i hit
    · have hout : i∉RationalTaylor.Runtime.loopWorkspace 641 := by
        intro hx
        simp only [RationalTaylor.Runtime.loopWorkspace,RationalTaylor.Runtime.workspace,
          RationalTaylor.workspace,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hx
        have hge := ids_ge i him
        have : i∈RationalTaylor.Runtime.ids := by
          simp only [RationalTaylor.Runtime.ids,RationalTaylor.ids,Finset.mem_union,
            Finset.mem_insert,Finset.mem_singleton]
          omega
        exact hit this
      simpa only [expFinalValues,ite_eq_right hit] using word_of_eq (ft.tapes i hout) (bu i him)
  have output : GlueMachine.Output
      (Maxwell.Certificate.Elementary.expApprox (-((b:ℚ)/a)) (N+1) N).center (resultWidth N W) t := by
    have ho := expFinalValues_output a b N
    have hw := expResult_width a b N W ha hb
    refine ⟨(expResult a b N).positive,(expResult a b N).negative,(expResult a b N).denominator,
      ?_,?_,?_,expResult_valid a b N ha0,(expResult_value a b N ha0).symm,hw.1,hw.2.1,hw.2.2⟩
    · simpa only [ho.1] using bank 602 (by decide)
    · simpa only [ho.2.1] using bank 603 (by decide)
    · simpa only [ho.2.2] using bank 604 (by decide)
  exact ⟨c0+c1,t,finalWord,e0.seq e1,Nat.add_le_add hc0 hc1,bank,hready.scratch,
    ⟨origin,hword⟩,hl,output,f0.trans (ft.mono (by decide))⟩

#print axioms exp_executes
end Maxwell.Continuum.GlueMachine.Runtime
