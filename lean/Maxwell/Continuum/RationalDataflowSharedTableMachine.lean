import Maxwell.Continuum.RationalDataflowSharedMap
import Maxwell.Continuum.RationalDataflowSharedPassFrame

/-! Uniform shared-denominator conversion from the literal stored raw input table.
Both passes, the saved runtime counter, and every output write are executed. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def sharedTableCode : Code :=
  .seq (WordReplace.code 201 206)
    (.seq (denominatorCode 0 1) (.seq (WordReplace.code 206 201) sharedMapCode))

def sharedTableCost (n W B wordLength : ℕ) : ℕ :=
  denominatorCost n W wordLength+sharedMapCost n B wordLength+36*wordLength+42

theorem sharedTable_executes {n : ℕ} (a b : Table n) (W B : ℕ) (hW : 1≤W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (haMeta : a.MetadataWidth W) (hbMeta : b.MetadataWidth B)
    (hbudget : sharedWidth n W≤B) (hslot : sharedWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (v : ℕ→Parts) (hv : WidthBank sharedSlots W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready sharedSlots v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (h206 : Blank s.val 206) :
    ∃ cost t output, Executes input tape sharedTableCode cost s t ∧
      cost≤sharedTableCost n W B xs.length ∧ SharedConversion.Ready sharedSlots output t ∧
      a.Ready t ∧ (b.filled (SharedTable.integerParts a.get) 0).OutputReady t ∧
      output 0=⟨SharedTable.denominator a.get,0,1⟩ := by
  have hWB : W≤B := (by unfold sharedWidth; nlinarith : W≤sharedWidth n W).trans hbudget
  have empty206 : BankArray.Word s.val 206 [] := by
    obtain ⟨o,ho⟩ := h206
    exact ⟨o,by simpa only [BitTape.shifted_nil] using ho⟩
  obtain ⟨s0,e0,saved0,f0⟩ := WordReplace.executes 201 206 (by decide) input tape xs [] s
    ⟨origin,hcount⟩ empty206
  have state0 := sharedReady_copy_frame hs (Or.inr rfl) f0
  have a0 := ha.copy_frame (Or.inr rfl) f0
  have b0 := hb.copy_frame (Or.inr rfl) f0 a0.scratch a0.seven
  have count0 : s0.val.tapes 201=BitTape.shifted xs origin :=
    (f0.2.2.2.2.2.1 201 (by decide)).trans hcount
  obtain ⟨cp,s1,prepared,finalWord,ep,hcp,preparedReady,a1,preparedValue,preparedWidth,count1,countLength⟩ :=
    denominator_pass_executes a W hW haMeta haWidth v hv input tape xs origin hlen s0 hn count0
      state0.rational a0
  have state1 := sharedReady_denominator_frame state0 ep preparedReady
  have b1 := b0.denominator_frame ep a1.scratch a1.seven
  have saved1 : BankArray.Word s1.val 206 xs :=
    BankArray.word_of_eq (ep.protectsTape 206 denominator_protects_saved_count) saved0
  obtain ⟨s2,er,count2,fr⟩ := WordReplace.executes 206 201 (by decide) input tape xs finalWord s1
    saved1 ⟨origin,count1⟩
  have state2 := sharedReady_copy_frame state1 (Or.inl rfl) fr
  have a2 := a1.copy_frame (Or.inl rfl) fr
  have b2 := b1.copy_frame (Or.inl rfl) fr a2.scratch a2.seven
  obtain ⟨newOrigin,count2⟩ := count2
  have hD : (prepared 0).positive=SharedTable.denominator a.get := by rw [preparedValue]
  obtain ⟨cm,t,_,em,hcm,finalState,finalInput,finalOutput,_,_⟩ := sharedMap_executes a b W B hW
    haWidth haValid (haMeta.mono hWB) hbMeta hbudget hslot hsep hdisjoint prepared preparedWidth hD
    input tape xs newOrigin (hlen.trans hWB) s2 hn count2 state2 a2 b2
  refine ⟨(6*[].length+15*xs.length+21)+(cp+((6*finalWord.length+15*xs.length+21)+cm)),
    t,sharedState a prepared n,e0.seq (ep.seq (er.seq em)),?_,finalState,finalInput,finalOutput,?_⟩
  · unfold sharedTableCost
    simp only [List.length_nil,countLength] at *
    omega
  · rw [sharedState_denominator,preparedValue]

theorem sharedTable_computes {n : ℕ} (a b : Table n) (W B : ℕ) (hW : 1≤W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (haMeta : a.MetadataWidth W) (hbMeta : b.MetadataWidth B)
    (hbudget : sharedWidth n W≤B) (hslot : sharedWidth n W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (v : ℕ→Parts) (hv : WidthBank sharedSlots W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready sharedSlots v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (h206 : Blank s.val 206) :
    ∃ t output,
      (runPriced (sharedTableCode.compile.next input tape) (sharedTableCost n W B xs.length+1) s.val).finished=
        some (t.place sharedTableCode.size) ∧
      (runPriced (sharedTableCode.compile.next input tape) (sharedTableCost n W B xs.length+1) s.val).instructions≤
        sharedTableCost n W B xs.length ∧
      SharedConversion.Ready sharedSlots output t ∧ a.Ready t ∧
      (b.filled (SharedTable.integerParts a.get) 0).OutputReady t ∧
      output 0=⟨SharedTable.denominator a.get,0,1⟩ ∧
      (∀ i : Fin n, ((b.filled (SharedTable.integerParts a.get) 0).get i).value/
        (SharedTable.denominator a.get:ℚ)=(a.get i).value) := by
  obtain ⟨cost,t,output,hex,hcost,hstate,hinput,houtput,hD⟩ := sharedTable_executes a b W B hW haWidth haValid
    haMeta hbMeta hbudget hslot hsep hdisjoint v hv input tape xs origin hlen s hn hcount hs ha hb h206
  obtain ⟨hrun,hsteps⟩ := hex.compiled_run (sharedTableCost n W B xs.length+1) (by omega)
  refine ⟨t,output,hrun,hsteps ▸ hcost,hstate,hinput,houtput,hD,fun i => ?_⟩
  have fit (i : Fin n) : (SharedTable.integerParts a.get i).Width (addressValue b.width) := by
    apply (SharedTable.integerParts_width a.get W haWidth i).mono
    simp only [Fintype.card_fin]
    unfold sharedWidth at hslot
    nlinarith
  rw [Table.filled_get b _ fit,SharedTable.integerParts_value]
  exact SharedTable.integerValue_sound a.get haValid i

#print axioms sharedTable_computes
end Maxwell.Continuum.RationalDataflow.PartArray
