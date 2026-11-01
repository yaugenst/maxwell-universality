import Maxwell.Continuum.StoredDescriptionSuffixInputs
import Maxwell.Cost.Structured.TapeSet

/-! One fixed program appends the complete physical source list, readout
placements, and finite-decoder description after chronological well output.
All arrays and operands come from the actual stored boundary. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank word_of_eq blank_of_eq zero_word_iff_blank)
set_option maxHeartbeats 500000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

theorem readout_rounding : GeometryOutput.Readout.code.protectsSet
    ({4}∪DyadicFloor.extraIds∪NaturalQuotient.workPorts)=true:=by decide +kernel

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v nv : ℕ→ℕ}

theorem suffix_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hp : Source.Promises p S) (hb : S.source≠0)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
    (dimension : nv 500=S.n) (integerBits : nv 4701=(gridReportFormat p S hm).integerBits)
    (fractionalBits : nv 4702=(gridReportFormat p S hm).fractionalBits)
    (sampleCount : nv 4703=gridCount p S hm)
    (side1 : nv 4705=gridSide p S hm 1) (side2 : nv 4706=gridSide p S hm 2)
    (normalization : (nv 4707:ℚ)/(nv 4708)=normalizationScale S)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store} {gv : ℕ→ℕ} {rv : ℕ→Parts}
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (table : PartArray.Table (siteCount saved))
    (correct : ∀i:Fin (siteCount saved),table.get i=Parts.literal (wellNumerators p S hm i.val:ℚ))
    (R H : ℕ) (metadata : table.MetadataWidth R)
    (h : SuffixStored p S hm data v nv saved table R H clock gv rv s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape suffixCode cost s t ∧
      cost≤suffixCost p S hm data v nv R H (siteCount saved) ∧
      t.val.output=(suffixBits p S hm).reverse++s.val.output ∧
      GeometryOutput.OutputFrame suffixWork s.val t.val:=by
  let H0:=H+(2^wellStoredPrecision p S hm).bits.length
  let H1:=H+(2^sourcePrecision p S).bits.length
  have countWord : Word s.val 500 S.n:=by
    rw [←dimension]
    exact h.selectors 500 (by decide)
  have powerOld : WordCleanup.Bounded [4808,144] H0 s.val:=by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · obtain ⟨xs,hw,word⟩:=h.old 4808 (by decide)
      exact ⟨xs,hw.trans (by dsimp [H0];omega),word⟩
    · obtain ⟨origin,word⟩:=h.power
      exact ⟨(2^wellStoredPrecision p S hm).bits,(by dsimp [H0];omega),origin,word⟩
  have parseOld : WordCleanup.Bounded SourcePayload.parseWords H0 s.val:=by
    intro i hi
    obtain ⟨xs,hw,word⟩:=h.old i
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi)))
    exact ⟨xs,hw.trans (by dsimp [H0];omega),word⟩
  obtain ⟨oldArchive,archiveWidth,archiveWord⟩:=h.old 85 (by decide)
  obtain ⟨oldCounter,counterWidth,counterWord⟩:=h.old 972 (by decide)
  obtain ⟨c0,a,gv0,r,e0,hc0,state,out0,f0,counter0⟩:=sources_executes physical hp hb geometry
    length_eq spacing_eq buffer_eq hlen h.geometry stored (rv 0) R H0 (h.payload.width 0 (by decide))
    h.raw h.clean h.sourceNumerator h.sourceDenominator h.sourcePrecision powerOld h.payload.templateWord h.archive
    countWord oldArchive oldCounter archiveWord counterWord parseOld input tape
  have storedA : StoredGeometry saved (v 1252) (v 1250) a.val.memory:=
    ⟨stored.positive,stored.fits,state.geometry.array⟩
  obtain ⟨countdown,oldCountWidth,oldCountWord⟩:=counter0 972 (by simp)
  have countSmall : S.n.bits.length≤geometryBudget v:=by
    have hn : S.n≤packedLength saved:=by
      have hh:=(sourceCircuit S (RealizationParameters.precision p S hm)).circuit.inputs_le_size
      unfold packedLength;omega
    have hh : S.n.bits.length≤(packedLength saved).bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hn
    exact hh.trans (sourcePlan physical hp (sourceInitialWidth p S hm data R H0) hlen stored).countWidth
  obtain ⟨c1,b,gv1,e1,hc1,gb,out1,f1,lastCount,lastCountWidth,lastCountWord⟩:=readouts_executes physical geometry
    length_eq spacing_eq buffer_eq hlen state.geometry storedA
    (word_of_eq (f0.tapes 503 (by decide)) h.first)
    (word_of_eq (f0.tapes 500 (by decide)) countWord)
    countdown oldCountWord (oldCountWidth.trans countSmall) input tape
  have frame01 : GeometryOutput.OutputFrame (SourcePayload.completeWork∪GeometryOutput.Readout.work) s.val b.val:=by
    refine ⟨f1.memory.trans f0.memory,f1.inputHead.trans f0.inputHead,f1.randomCursor.trans f0.randomCursor,?_⟩
    intro i hi
    have hh : i∉SourcePayload.completeWork ∧i∉GeometryOutput.Readout.work:=by
      simpa only [Finset.mem_union,not_or] using hi
    exact (f1.tapes i hh.2).trans (f0.tapes i hh.1)
  have storedB : StoredGeometry saved (v 1252) (v 1250) b.val.memory:=
    ⟨stored.positive,stored.fits,gb.array⟩
  have rawB : Ready StoredInteger.slots r b:=by
    refine ⟨?_,gb.ready.natural⟩
    intro i hi
    exact word_of_eq (f1.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
      Disjoint (RationalDataflow.ids StoredInteger.slots) GeometryOutput.Readout.work) hi hh))
      (state.raw.1 i ((by decide : RationalDataflow.ids StoredInteger.slots⊆RationalDataflow.ids SourcePayload.bank) hi))
  have widthB : WidthBank StoredInteger.slots (suffixRawWidth p S hm data R H) r:=by
    intro i hi
    exact state.width i ((by decide : StoredInteger.slots⊆SourcePayload.bank) hi)
  have tableB : table.Ready b:=by
    apply h.payload.table.storage_frame frame01.memory _ gb.ready.scratch gb.ready.seven
    intro i hi
    exact frame01.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
      Disjoint ({200,202,203,204,205}:Finset ℕ) (SourcePayload.completeWork∪GeometryOutput.Readout.work)) hi hh)
  have cleanB : DyadicFloor.Clean b.val:=by
    have keep (i : ℕ) (hi : i∈({4}∪DyadicFloor.extraIds∪NaturalQuotient.workPorts:Finset ℕ)):=
      e1.protectsSet _ readout_rounding i hi
    refine ⟨blank_of_eq (keep 4 (by decide)) state.clean.1,?_⟩
    intro i hi
    apply blank_of_eq (keep i ?_) (state.clean.2 i hi)
    rcases Finset.mem_union.mp hi with he|hq
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
    · exact Finset.mem_union_right _ hq
  have outputOld : WordCleanup.Bounded DecoderRow.outputList H1 b.val:=by
    intro i hi
    obtain ⟨xs,hw,word⟩:=h.old i (by
      unfold suffixOldPorts
      exact List.mem_append_left _ (List.mem_append_right _ hi))
    exact ⟨xs,hw.trans (by dsimp [H1];omega),BankArray.word_of_eq (frame01.tapes i (fun hh=>
      Finset.disjoint_left.mp (by decide : Disjoint DecoderRow.outputList.toFinset
        (SourcePayload.completeWork∪GeometryOutput.Readout.work)) (by simpa using hi) hh)) word⟩
  have workspaceB : WordCleanup.Bounded RationalCanonical.workspace H1 b.val:=by
    intro i hi
    by_cases small:i<4
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (gb.ready.natural i small)⟩
    by_cases four:i=4
    · subst i;exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr cleanB.1⟩
    by_cases quotient:i∈NaturalQuotient.workPorts
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (cleanB.2 i (Finset.mem_union_right _ quotient))⟩
    have high : i∈({230,231}:Finset ℕ):=by
      simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at quotient
      simp only [Finset.mem_insert,Finset.mem_singleton];omega
    obtain ⟨xs,hw,word⟩:=h.old i (List.mem_append_right _ hi)
    exact ⟨xs,hw.trans (by dsimp [H1];omega),BankArray.word_of_eq (frame01.tapes i (fun hh=>Finset.disjoint_left.mp
      (by decide : Disjoint ({230,231}:Finset ℕ) (SourcePayload.completeWork∪GeometryOutput.Readout.work)) high hh)) word⟩
  have selectorsB : NatAssign.Bank suffixSelectorPorts nv b.val:=by
    intro i hi
    exact word_of_eq (frame01.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
      Disjoint suffixSelectorPorts (SourcePayload.completeWork∪GeometryOutput.Readout.work)) hi hh)) (h.selectors i hi)
  have powerA : Word a.val 144 (2^sourcePrecision p S):=state.power
  have powerB : BankArray.Word b.val 144 (2^sourcePrecision p S).bits:=by
    obtain ⟨origin,word⟩:=powerA
    exact ⟨origin,(f1.tapes 144 (by decide)).trans word⟩
  have powerBound : (2^sourcePrecision p S).bits.length≤H1:=by
    change (2^sourcePrecision p S).bits.length≤H+(2^sourcePrecision p S).bits.length
    exact Nat.le_add_left _ _
  generalize powerBitsEq : (2^sourcePrecision p S).bits=sourcePowerBits at powerBound powerB
  obtain ⟨c2,t,e2,hc2,out2,f2⟩:=decoder_executes (p:=p) (S:=S) (hm:=hm) (data:=data) (v:=v) (nv:=nv)
    (saved:=saved) (clock:=clock) (s:=b) (gv:=gv1) (rv:=r) physical hb geometry length_eq spacing_eq buffer_eq
    dimension integerBits fractionalBits sampleCount side1 side2 normalization hlen gb storedB table correct
    (suffixRawWidth p S hm data R H) R H1 metadata tableB rawB widthB
    (fun i hi=>selectorsB i (Finset.mem_union_right _ hi))
    (word_of_eq (frame01.tapes 990 (by decide)) h.payload.precision)
    outputOld sourcePowerBits powerBound powerB workspaceB
    (word_of_eq (frame01.tapes 503 (by decide)) h.first) (word_of_eq (frame01.tapes 500 (by decide)) countWord)
    (siteCount saved) (word_of_eq (frame01.tapes 728 (by decide)) h.payload.index)
    (word_of_eq (frame01.tapes 727 (by decide)) h.payload.one)
    lastCount lastCountWord (fun i hi=>selectorsB i (Finset.mem_union_left _ (by simpa using hi))) input tape
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,?_,⟨f2.memory.trans frame01.memory,
    f2.inputHead.trans frame01.inputHead,f2.randomCursor.trans frame01.randomCursor,?_⟩⟩
  · have cost0 : c0≤sourceCost p S hm v (suffixSourceWidth p S hm data R H) H0 H H:=by
      unfold sourceCost at hc0 ⊢
      dsimp only [suffixSourceWidth,H0] at hc0 ⊢
      omega
    rw [lastCountWidth] at hc2
    change c2≤decoderCost _ _ _ H1 _ _ _ _ at hc2
    unfold suffixCost
    dsimp only [H0,H1] at cost0 hc2
    omega
  · rw [out2,out1,out0]
    simp only [suffixBits,List.reverse_append,List.append_assoc]
  · intro i hi
    have hh : i∉SourcePayload.completeWork∪GeometryOutput.Readout.work ∧i∉decoderWork:=by
      simpa only [suffixWork,Finset.mem_union,not_or] using hi
    exact (f2.tapes i hh.2).trans (frame01.tapes i hh.1)

#print axioms suffix_executes
end Maxwell.Continuum.WellStrengthInitialization
