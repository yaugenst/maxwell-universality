import Maxwell.Continuum.CalibrationNeumannCopyFrame
import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Cost.Structured.WordCleanup

/-! The copied coefficient table, runtime setup, and Neumann loop execute
as one fixed program. The only source table premise is its literal stored
raw integer values, as produced by shared-denominator conversion. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 3000000

def retiredWords : List ℕ := [4,37,201,205,215,220,221,222,223]

def copiedCode : Code := .seq PartArray.copyCode initializedCode
def copiedCost (n width heap D N B : ℕ) : ℕ :=
  PartArray.copyCost (tableSize n) B+initializedCost n width heap D N B

theorem copied_executes {n : ℕ} (coeff : CoefficientIndex n→Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (hw : 0<addressValue a.width) (hB : 0<B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hslot : commonWidth n N (W+1)≤addressValue a.width)
    (haWidth : ∀ i, (a.get i).Width B)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hbSlot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (logical : ℕ→Parts) (hlogicalWidth : WidthBank {1} B logical) (hlogicalGood : Good {1} logical)
    (v : ℕ→ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap (SharedTable.denominator coeff) N)
    (hbits : ∀ i∈Descriptors.ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=tableSize n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (hs : SharedConversion.Ready {1} logical s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ (cost : ℕ) (t : Store) (out : Snapshot n), Executes input tape copiedCode cost s t ∧
      cost≤copiedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B ∧
      out.Ready n.bits (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) t.val ∧
      out.data.Sized (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 N ∧
      RationalAccumulator.Blank t.val 140 ∧
      (∃numbers : ℕ→ℕ,NatAssign.Bank Descriptors.retainedIds numbers t.val ∧
        ∀k∈Descriptors.retainedIds,(numbers k).bits.length ≤ Descriptors.retainedWidth B) ∧
      WordCleanup.Bounded retiredWords B t.val ∧
      RationalAccumulator.Blank t.val 105 ∧
      (∃last : Parts,StoredParts.Stored (positivePort 1) last t.val ∧ last.Width B) ∧
      ∀ i : Fin n, ((Horner.channels out.words 10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(N+1)=
        rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) (N+1) i := by
  have haValid (i) : (a.get i).Valid := by
    rw [haValues]
    exact SharedTable.integerParts_valid _ _
  obtain ⟨c0,u,finalWord,e0,hc0,hs',ha',hb',finalCounter,finalLength⟩ := PartArray.copy_executes a b logical B hB haWidth haValid
    hlogicalWidth hlogicalGood haMeta hbMeta hbSlot hsep hdisjoint
    input tape xs origin hlen s hn hcount hs ha hb
  have bank := copied_descriptor_bank a b logical _ v e0 hs hs' ha ha' hb hb' hbank
  have filledLayout : TableLayout a (b.filled a.get 0) heap :=
    ⟨hl.canonical,hl.width,hl.positive,hl.negative,hl.copyPositive,hl.copyNegative⟩
  have values := PartArray.Table.filled_get b a.get (fun i => (haWidth i).mono hbSlot)
  obtain ⟨c1,t,e1,hc1,ht,sized,denominator,counter,blank,retained,clock205,hv⟩ := initialized_executes coeff hvalid W hwidth a (b.filled a.get 0)
    heap N B hw hB filledLayout haValues values hslot v hi hbits input tape u bank ha' hb' (shared_blank_clock hs')
  have blank105 : RationalAccumulator.Blank u.val 105 := by
    have h:=hs'.rational.1 105 (Finset.mem_union_right _ (by decide))
    simpa only [dataValues_small _ (by decide : 105<1000),RationalAccumulator.zero_word_iff_blank] using h
  have final105:=RationalAccumulator.blank_of_eq (e1.protectsTape 105 (by decide)) blank105
  have entry:=Cells.of_ready hs'.rational 1 (by simp)
  have finalEntry : StoredParts.Stored (positivePort 1)
      (PartArray.iterate a 1 .done logical (tableSize n) 1) t.val:=
    ⟨RationalAccumulator.word_of_eq (e1.protectsTape _ (by decide)) entry.1,
      RationalAccumulator.word_of_eq (e1.protectsTape _ (by decide)) entry.2.1,
      RationalAccumulator.word_of_eq (e1.protectsTape _ (by decide)) entry.2.2⟩
  have finalWidth:=PartArray.copy_width a logical B hB haWidth hlogicalWidth (tableSize n) 1 (by simp)
  have quotient (k : ℕ) (hk : k∈NaturalQuotient.workPorts) : RationalAccumulator.Word t.val k 0 := by
    have protect : ∀k∈NaturalQuotient.workPorts,initializedCode.protectsTape k=true := by decide
    apply RationalAccumulator.word_of_eq (e1.protectsTape k (protect k hk))
    simpa only [SharedConversion.work_values_zero _ k hk] using hs'.1 k (Finset.mem_union_right _ hk)
  have retired : WordCleanup.Bounded retiredWords B t.val := by
    intro k hk
    simp only [retiredWords,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨[],Nat.zero_le _,(RationalAccumulator.zero_word_iff_blank _ _).mpr
        (RationalAccumulator.blank_of_eq (e1.protectsTape 4 (by decide)) (hs'.2 4 (by decide)))⟩
    · obtain ⟨_,_,_,_,_,_,_,_,packing,_,_⟩:=ht.1
      exact ⟨[],Nat.zero_le _,(RationalAccumulator.zero_word_iff_blank _ _).mpr packing⟩
    · exact ⟨finalWord,finalLength.trans_le hlen,
        BankArray.word_of_eq (e1.protectsTape 201 (by decide)) ⟨origin,finalCounter⟩⟩
    · exact ⟨a.clock,haMeta.clock,clock205⟩
    · exact ⟨b.clock,hbMeta.clock,
        BankArray.word_of_eq (e1.protectsTape 215 (by decide)) hb'.clock⟩
    all_goals exact ⟨[],Nat.zero_le _,quotient _ (by decide)⟩
  exact ⟨c0+c1,t,_,e0.seq e1,Nat.add_le_add hc0 hc1,ht,sized,denominator,counter,blank,retained,retired,final105,
    ⟨_,finalEntry,finalWidth⟩,hv⟩

theorem copied_computes {n : ℕ} (coeff : CoefficientIndex n→Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (hw : 0<addressValue a.width) (hB : 0<B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hslot : commonWidth n N (W+1)≤addressValue a.width)
    (haWidth : ∀ i, (a.get i).Width B)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hbSlot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (logical : ℕ→Parts) (hlogicalWidth : WidthBank {1} B logical) (hlogicalGood : Good {1} logical)
    (v : ℕ→ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap (SharedTable.denominator coeff) N)
    (hbits : ∀ i∈Descriptors.ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=tableSize n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (hs : SharedConversion.Ready {1} logical s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ (t : Store) (out : Snapshot n),
      (runPriced (copiedCode.compile.next input tape)
        (copiedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) s.val).finished=
          some (t.place copiedCode.size) ∧
      (runPriced (copiedCode.compile.next input tape)
        (copiedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) s.val).instructions≤
          copiedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B ∧
      out.Ready n.bits (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) t.val ∧
      ∀ i : Fin n, ((Horner.channels out.words 10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(N+1)=
        rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) (N+1) i := by
  obtain ⟨cost,t,out,he,hcost,hr,_,_,_,_,_,_,_,_,hv⟩ := copied_executes coeff hvalid W hwidth a b heap N B hw hB hl
    haValues hslot haWidth haMeta hbMeta hbSlot hsep hdisjoint logical hlogicalWidth hlogicalGood
    v hi hbits input tape xs origin hlen s hn hcount hbank hs ha hb
  obtain ⟨hrun,hsteps⟩ := he.compiled_run
    (copiedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) (by omega)
  exact ⟨t,out,hrun,hsteps ▸ hcost,hr,hv⟩

#print axioms copied_executes
#print axioms copied_computes

end Maxwell.Continuum.Calibration.NeumannMachine
