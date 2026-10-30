import Maxwell.Continuum.ProfileProducedFrame
import Maxwell.Continuum.ProfileEmissionCarry

/-! The complete fixed coefficient-table program. It computes all samples
and rounded coefficients, exchanges the actual buffers, applies the two
endpoint corrections, and stores the exact encoded profile values. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] profileDegree profileWorkBits profileGrid encodedCoefficient

def encodedTableCode : Code := .seq roundedTableCode (.seq PartArray.headerSwapCode finalizeCode)
def encodedTableWidth (D W : ℕ) : ℕ := correctionWorkingWidth D (endpointWorkingWidth D W)
def encodedTableCost (grid D P U W indexLength : ℕ) : ℕ :=
  roundedTableCost grid D P U W indexLength+256*(encodedTableWidth D W+1)+
    finalizeCost D P W (roundedWidth grid U)

theorem finalizeCode_preserves_swap : finalizeCode.protectsTape 216=true := by decide

theorem finalizeCost_mono_old (D P W x y : ℕ) (h : x≤y) :
    finalizeCost D P W x≤finalizeCost D P W y := by
  unfold finalizeCost
  omega

theorem finalizeTable_metadata {n : ℕ} (a b : PartArray.Table n) (P : ℕ) (v : ℕ→Parts) :
    tableMetadata b (finalizeTable a b P v) := ⟨rfl,rfl,rfl,rfl,rfl⟩

structure EncodedTableResult (N W : ℕ) (a : PartArray.Table (profileDegree N)) (s : Store) where
  table : PartArray.Table (profileDegree N)
  metadata : tableMetadata a table
  output : table.OutputReady s
  values : ℕ→Parts
  ready : SharedConversion.Ready dftRegisters values s
  good : Good dftRegisters values
  width : WidthBank dftRegisters (encodedTableWidth (profileDegree N) W) values
  countWord : List Bool
  count : BankArray.Word s.val 201 countWord
  countLength : countWord.length=(profileDegree N).bits.length
  correct : ∀i:Fin (profileDegree N),(table.get i).Valid ∧
    (table.get i).Width (encodedTableWidth (profileDegree N) W) ∧
    (table.get i).value=(encodedCoefficient N i.val).value
  input : PartArray.Table (profileDegree N)
  inputReady : input.Ready s
  inputMetadata : input.MetadataWidth W
  inputSeparated : input.Separated
  disjoint : input.SeparatedFrom table
  swapBlank : Blank s.val 216
  degreeWord : Word s.val 661 (profileDegree N)
  precisionWord : Word s.val 663 (profileWorkBits N)
  powerWord : Word s.val 144 (2^profileWorkBits N)
  floorClean : DyadicFloor.Clean s.val

theorem encoded_table_executes (N U W : ℕ) (hW : 1≤W)
    (a b : PartArray.Table (profileDegree N))
    (hg : profileGrid N≤U) (hD : profileDegree N≤U) (hP : profileWorkBits N≤U)
    (ham : a.MetadataWidth W) (hfit : roundedRawWidth U≤addressValue a.width)
    (has : a.Separated) (hdis : b.SeparatedFrom a)
    (hbm : b.MetadataWidth (encodedTableWidth (profileDegree N) W))
    (hslot : encodedTableWidth (profileDegree N) W≤addressValue b.width) (hbs : b.Separated)
    (hbank : roundedWidth (profileGrid N) U≤W)
    (hn : (profileDegree N).bits.length≤W)
    (hpow : ((2:ℕ)^profileWorkBits N).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (hvalue : addressValue xs=profileDegree N) (s : Store)
    (hp : ProducerState (profileGrid N) (profileDegree N) (profileWorkBits N) U s)
    (ha : a.OutputReady s) (hb : b.Ready s)
    (hsize : Word s.val 661 (profileDegree N)) (hblank : Blank s.val 216)
    (hcounter : s.val.tapes 700=BitTape.shifted xs origin) :
    ∃(cost : ℕ) (t : Store) (_result : EncodedTableResult N W b t),
      Executes input tape encodedTableCode cost s t ∧
      cost≤encodedTableCost (profileGrid N) (profileDegree N) (profileWorkBits N) U W xs.length := by
  let D := profileDegree N
  let P := profileWorkBits N
  let M := encodedTableWidth D W
  have hWM : W≤M := by dsimp [M,encodedTableWidth,correctionWorkingWidth,endpointWorkingWidth];omega
  obtain ⟨c0,s0,_,r,e0,_,_,hc0,b0,size0,z0⟩ := rounded_table_spare_executes
    (profileGrid N) D P U W a b (profileGrid_pos N) hg hD hP ham hfit has hdis
    input tape xs origin hlen hvalue s hp ha hb hsize hblank hcounter
  have am0 := tableMetadata_width r.metadata ham
  obtain ⟨c1,s1,e1,hc1,_,a1,b1,swap1,f1⟩ := PartArray.headerSwap_executes b r.table M hbm
    (am0.mono hWM) dftRegisters r.values input tape s0 r.ready b0 r.output z0
  have state1 := sharedReady_headerSwap (clean_shared_ready r.ready r.floorClean) f1
  have size1 := word_of_eq (f1.tapes 661 (by decide)) size0
  have power1 := word_of_eq (f1.tapes 144 (by decide)) r.power
  have precision1 := word_of_eq (f1.tapes 663 (by decide)) r.parameters.precision
  have floorClean1 := floorClean_headerSwap r.floorClean f1
  have count1 := BankArray.word_of_eq (f1.tapes 201 (by decide)) r.innerCounter
  have dis1 : r.table.SeparatedFrom b :=
    tableSeparatedFrom_symm (tableMetadata_separatedFrom r.metadata b hdis)
  obtain ⟨c2,t,word,e2,hc2,state2,good2,width2,b2,a2,count2,len2,correct2,size2,power2⟩ :=
    finalize_executes N W hW r.table b (fun i => r.table.get_width W am0 s1 a1 i)
      (fun i => (r.profile_correct N U a i).2.1) (fun i => (r.profile_correct N U a i).2.2)
      am0 hbm hslot hbs dis1 hn hpow r.values (r.width.mono hbank) input tape r.innerWord s1
      state1 a1 b1 count1 size1 power1
  refine ⟨c0+(c1+c2),t,⟨finalizeTable r.table b P r.values,?_,b2,
    finalizeOutputValues r.table P r.values,state2,good2,width2,word,count2,len2,correct2,
    r.table,a2,am0,tableMetadata_separated r.metadata has,
    tableMetadata_separatedFrom (finalizeTable_metadata r.table b P r.values) r.table dis1,
    blank_of_eq (e2.protectsTape 216 finalizeCode_preserves_swap) swap1,
    size2,word_of_eq (e2.protectsSet emissionPorts finalizeCode_preserves_emission 663 (by decide)) precision1,
    power2,finalize_floorClean e2 floorClean1 state2⟩,
    e0.seq (e1.seq e2),?_⟩
  · exact finalizeTable_metadata r.table b P r.values
  · have hc2' : c2≤finalizeCost D P W (roundedWidth (profileGrid N) U) := by
      exact hc2.trans (finalizeCost_mono_old D P W _ _ r.innerLength)
    dsimp only [D,P,M] at hc0 hc1 hc2' ⊢
    unfold encodedTableCost
    omega

#print axioms encoded_table_executes
end Maxwell.Continuum.Profile.Runtime
