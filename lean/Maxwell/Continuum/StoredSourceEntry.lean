import Maxwell.Continuum.StoredSourceEmission
import Maxwell.Continuum.RationalDataflowResetList
import Maxwell.Continuum.StoredIntegerEmission
import Maxwell.Continuum.StoredGeometryRecord

/-! One source entry is parsed, multiplied, rounded down, emitted, and recycled.
The final rational bank has the original width bound, independent of how
many preceding entries were emitted. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def resetSlots : List ℕ := [0,12,14,15]
def entryCode : Code := .seq readCode (.seq amplitudeCode (.seq emitCode (resetList resetSlots).code))
def entryWork : Finset ℕ := readWork∪DyadicFloor.StoredPower.workspace bank
def resetValues (v : ℕ→Parts) (i : ℕ) : Parts:=if i∈resetSlots then Parts.literal 0 else v i

theorem entry_values (P : ℕ) (q : ℚ) (v : ℕ→Parts) :
    (resetList resetSlots).evaluate (amplitudeValues P (Function.update v 0 (Parts.literal q)))=resetValues v := by
  funext i
  rw [resetList_values]
  by_cases hi : i∈resetSlots
  · simp only [hi,ite_true,resetValues]
  · have h : i≠0 ∧i≠12 ∧i≠14 ∧i≠15:=by
      simpa only [resetSlots,List.mem_cons,List.not_mem_nil,or_false,not_or] using hi
    rw [amplitude_kept P _ i h.1 h.2.1 h.2.2.1 h.2.2.2,Function.update_of_ne h.1]
    simp only [resetValues,hi,ite_false]

theorem reset_width (v : ℕ→Parts) (B : ℕ) (hB : 1≤B) (width : WidthBank bank B v) :
    WidthBank bank B (resetValues v) := by
  intro i hi
  by_cases reset : i∈resetSlots
  · simp only [resetValues,reset,ite_true]
    exact (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono hB
  · simpa only [resetValues,reset,ite_false] using width i hi

theorem reset_good (v : ℕ→Parts) (good : Good bank v) : Good bank (resetValues v) := by
  intro i hi
  by_cases reset : i∈resetSlots
  · simpa only [resetValues,reset,ite_true] using Parts.literal_valid 0
  · simpa only [resetValues,reset,ite_false] using good i hi

theorem entry_executes (P B : ℕ) (hB : 2≤B) (hP : (2^P).bits.length≤B)
    (hprec : P.bits.length≤B) (q : ℚ) (v : ℕ→Parts)
    (width : WidthBank bank B v) (good : Good bank v)
    (hn : q.num.natAbs.bits.length≤B) (hd : q.den.bits.length≤B)
    (template input : List Bool) (tape : ℕ→Bool) (archiveOrigin : ℤ) (preceding suffix : List Bool) (s : Store)
    (ready : Ready bank v s) (old : WordCleanup.Bounded parseWords B s.val)
    (source : s.val.tapes 85=BitTape.translate archiveOrigin (NormalizedRecordParser.cursor
      (preceding++(Codec.rat q++suffix)) preceding.length))
    (clean : DyadicFloor.Clean s.val) (power : Word s.val 144 (2^P))
    (precision : Word s.val 4427 P) (stored : BankArray.Word s.val 992 template) :
    ∃cost t,Executes input tape entryCode cost s t ∧
      cost≤2^200*(P+B+8)^2+10*template.length ∧
      t.val.output=(payloadBits P (numerator P (Function.update v 0 (Parts.literal q))) template).reverse++s.val.output ∧
      Ready bank (resetValues v) t ∧ WidthBank bank B (resetValues v) ∧ Good bank (resetValues v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      t.val.tapes 85=BitTape.translate archiveOrigin (NormalizedRecordParser.cursor (preceding++(Codec.rat q++suffix))
        (preceding.length+(Codec.rat q).length)) ∧
      WordCleanup.Bounded parseWords B t.val ∧ GeometryOutput.OutputFrame entryWork s.val t.val := by
  let loaded:=Function.update v 0 (Parts.literal q)
  obtain ⟨c0,a,e0,hc0,ra,wa,archive,blank10,num,den,f0⟩:=read_executes bank (by decide) (by decide)
    q v B width hn hd input tape archiveOrigin preceding suffix s ready old source
  have ca : DyadicFloor.Clean a.val:=by
    refine ⟨blank_of_eq (f0.tapes 4 (by decide)) clean.1,?_⟩
    intro i hi
    exact blank_of_eq (f0.tapes i (fun hm=>Finset.disjoint_left.mp
      (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) readWork) hi hm)) (clean.2 i hi)
  obtain ⟨c1,b,e1,hc1,rb,gb,wb,cb,pb,f1⟩:=amplitude_executes P B hB hP loaded wa
    (good.update 0 (Parts.literal_valid q)) input tape a ra ca (word_of_eq (f0.tapes 144 (by decide)) power)
  have before : BinaryPrecision.Frame entryWork s.val b.val:=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have hp : Word b.val (positivePort 0) (numerator P loaded).toNat:=by
    have hh:=rb.1 (positivePort 0) (cell_mem (by decide : 0∈bank) (by simp [cellPorts]))
    simpa only [dataValues_positive,amplitude_result,Parts.literal,Rat.num_intCast] using hh
  have hm : Word b.val (negativePort 0) (-(numerator P loaded)).toNat:=by
    have hh:=rb.1 (negativePort 0) (cell_mem (by decide : 0∈bank) (by simp [cellPorts]))
    simpa only [dataValues_negative,amplitude_result,Parts.literal,Rat.num_intCast] using hh
  obtain ⟨c,e2,out,f2⟩:=emit_executes P (numerator P loaded) template input tape b
    (word_of_eq (before.tapes 4427 (by decide)) precision) hp hm
    (BankArray.word_of_eq (before.tapes 992 (by decide)) stored)
  have rc:=StoredInteger.ready_emit_frame rb f2
  obtain ⟨c3,t,e3,hc3,rt,f3⟩:=resetList_executes bank resetSlots (by decide)
    (amplitudeValues P loaded) (P+32*B+35) (by omega) wb gb input tape c rc
  have after : BinaryPrecision.Frame entryWork c.val t.val:=f3.mono (by decide)
  have same (i : ℕ) (hi : i∉entryWork) : t.val.tapes i=s.val.tapes i:=
    (after.tapes i hi).trans ((congrFun f2.2.2.2.2 i).trans (before.tapes i hi))
  have ct : DyadicFloor.Clean t.val:=by
    have cc : DyadicFloor.Clean c.val:=⟨blank_of_eq (congrFun f2.2.2.2.2 4) cb.1,
      fun i hi=>blank_of_eq (congrFun f2.2.2.2.2 i) (cb.2 i hi)⟩
    exact cc.arithmetic_frame f3
  have unchanged (i : ℕ) (hi : i∉DyadicFloor.StoredPower.workspace bank) : t.val.tapes i=a.val.tapes i:=
    (f3.tapes i (fun hh=>hi (RoundedInteger.arithmetic_workspace_subset bank hh))).trans
      ((congrFun f2.2.2.2.2 i).trans (f1.tapes i hi))
  refine ⟨c0+(c1+((20*(P.bits.length+(numerator P loaded).natAbs.bits.length)+10*template.length+64)+c3)),t,
    e0.seq (e1.seq (e2.seq e3)),?_,?_,?_,reset_width v B (by omega) width,reset_good v good,ct,
    word_of_eq (f3.tapes 144 (outside_workspace bank 144 (by decide)))
      (word_of_eq (congrFun f2.2.2.2.2 144) pb),
    (unchanged 85 (by decide)).trans archive,?_,
    ⟨after.memory.trans (f2.2.2.1.trans before.memory),after.inputHead.trans (f2.2.1.trans before.inputHead),
      after.randomCursor.trans (f2.2.2.2.1.trans before.randomCursor),same⟩⟩
  · have hz : (numerator P loaded).natAbs.bits.length≤P+32*B+35:=by
      apply StoredInteger.canonical_abs_width
      rw [←amplitude_result]
      exact wb 0 (by decide)
    change c3≤4*operationCost (P+32*B+35)+1 at hc3
    unfold operationCost at hc3
    nlinarith only [hc0,hc1,hc3,hprec,hz,Nat.zero_le P,Nat.zero_le B]
  · rw [after.output,out,before.output]
  · simpa only [loaded,entry_values] using rt
  · intro i hi
    simp only [parseWords,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl
    · exact ⟨[],by simp,(zero_word_iff_blank _ _).mpr (blank_of_eq (unchanged 10 (by decide)) blank10)⟩
    · exact ⟨q.num.natAbs.bits,hn,word_of_eq (unchanged 4801 (by decide)) num⟩
    · exact ⟨q.den.bits,hd,word_of_eq (unchanged 4802 (by decide)) den⟩

#print axioms entry_executes
end Maxwell.Continuum.SourcePayload
