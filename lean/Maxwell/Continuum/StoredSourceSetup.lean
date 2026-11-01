import Maxwell.Continuum.StoredSourceMultiplier
import Maxwell.Cost.Structured.StoredPowerOfTwo

/-! The source serializer's arithmetic state is initialized from retained
calibration words. The old emitted well numerator is replaced explicitly,
and the stored source precision drives its actual rounding-power generator. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def setupCode : Code:=.seq (Instruction.literal 0 0).code
  (.seq multiplierCode (StoredPowerOfTwo.code 4427 4808 144))
def setupWork : Finset ℕ:=workspace bank∪{4808,144}
def setupCost (P B H : ℕ) : ℕ:=2^122*(B+2)^2+
  (2*(6*H+4)+1+((P+1)*(13*P.bits.length+25)+21*P.bits.length+27))

theorem setup_executes (N D P B H : ℕ) (hB : 2≤B) (hN : 0<N) (hD : 0<D)
    (numWidth : N.bits.length≤B) (denWidth : D.bits.length≤B)
    (v : ℕ→Parts) (last : Parts) (canonical : v 0=Parts.literal 0)
    (width : WidthBank bank B (Function.update v 0 last)) (good : Good bank v)
    (mode : (v 1).value≠0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : Ready bank (Function.update v 0 last) s) (clean : DyadicFloor.Clean s.val)
    (num : Word s.val 506 N) (den : Word s.val 507 D) (precision : Word s.val 4427 P)
    (old : WordCleanup.Bounded [4808,144] H s.val) :
    ∃cost t,Executes input tape setupCode cost s t ∧cost≤setupCost P B H ∧
      Ready bank (multiplierValues N D v) t ∧Good bank (multiplierValues N D v) ∧
      WidthBank bank (16*(B+1)) (multiplierValues N D v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧Blank t.val 4808 ∧
      BinaryPrecision.Frame setupWork s.val t.val := by
  have zeroWidth : (Parts.literal 0).Width B:=
    (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono (by omega)
  obtain ⟨c0,a,e0,hc0,ra,f0⟩:=(Instruction.literal 0 0).executes bank (show 0∈bank from by decide)
    (Function.update v 0 last) B width zeroWidth input tape s ready
  have restored : (Instruction.literal 0 0).update (Function.update v 0 last)=v:=by
    simp only [Instruction.update,Function.update_idem,←canonical,Function.update_eq_self]
  rw [restored] at ra
  have restoredWidth : WidthBank bank B v:=by
    have h:=(width.update 0 zeroWidth)
    simpa only [Function.update_idem,←canonical,Function.update_eq_self] using h
  obtain ⟨c1,b,e1,hc1,rb,gb,wb,f1⟩:=multiplier_executes N D B hB hN hD numWidth denWidth v restoredWidth good mode
    input tape a ra (word_of_eq (f0.tapes 506 (outside_workspace bank 506 (by decide))) num)
    (word_of_eq (f0.tapes 507 (outside_workspace bank 507 (by decide))) den)
  have frame01:=f0.trans f1
  have oldB : WordCleanup.Bounded [4808,144] H b.val:=by
    intro i hi
    obtain ⟨xs,hxs,word⟩:=old i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (frame01.tapes i ?_) word⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl <;> decide
  obtain ⟨c2,t,e2,hc2,power,temp,f2⟩:=StoredPowerOfTwo.executes 4427 4808 144 (by decide) (by decide) (by decide)
    P H input tape b (word_of_eq (frame01.tapes 4427 (by decide)) precision) oldB
  have rawT : Ready bank (multiplierValues N D v) t:=by
    refine ⟨?_,?_⟩
    · intro i hi
      exact word_of_eq (f2.tapes i (fun hh=>Finset.disjoint_left.mp
        (by decide : Disjoint (ids bank) ({4808,144}:Finset ℕ)) hi hh)) (rb.1 i hi)
    · intro i hi
      exact blank_of_eq (f2.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)) (rb.2 i hi)
  have cleanB:=clean.arithmetic_frame frame01
  have cleanT : DyadicFloor.Clean t.val:=by
    refine ⟨blank_of_eq (f2.tapes 4 (by decide)) cleanB.1,?_⟩
    intro i hi
    exact blank_of_eq (f2.tapes i (fun hh=>Finset.disjoint_left.mp
      (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) ({4808,144}:Finset ℕ)) hi hh)) (cleanB.2 i hi)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,rawT,gb,wb,cleanT,power,temp,
    (frame01.mono Finset.subset_union_left).trans (f2.mono Finset.subset_union_right)⟩
  unfold setupCost operationCost at *
  nlinarith only [hc0,hc1,hc2,Nat.zero_le B]

#print axioms setup_executes
end Maxwell.Continuum.SourcePayload
