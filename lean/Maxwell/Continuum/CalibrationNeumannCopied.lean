import Maxwell.Continuum.CalibrationNeumannCopyFrame

/-! The copied coefficient table, runtime setup, and Neumann loop execute
as one fixed program. The only source table premise is its literal stored
raw integer values, as produced by shared-denominator conversion. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 3000000

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
      ∀ i : Fin n, ((Horner.channels out.words 10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(N+1)=
        rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) (N+1) i := by
  have haValid (i) : (a.get i).Valid := by
    rw [haValues]
    exact SharedTable.integerParts_valid _ _
  obtain ⟨c0,u,_,e0,hc0,hs',ha',hb',_,_⟩ := PartArray.copy_executes a b logical B hB haWidth haValid
    hlogicalWidth hlogicalGood haMeta hbMeta hbSlot hsep hdisjoint
    input tape xs origin hlen s hn hcount hs ha hb
  have bank := copied_descriptor_bank a b logical _ v e0 hs hs' ha ha' hb hb' hbank
  have filledLayout : TableLayout a (b.filled a.get 0) heap :=
    ⟨hl.canonical,hl.width,hl.positive,hl.negative,hl.copyPositive,hl.copyNegative⟩
  have values := PartArray.Table.filled_get b a.get (fun i => (haWidth i).mono hbSlot)
  obtain ⟨c1,t,e1,hc1,ht,sized,denominator,counter,_,hv⟩ := initialized_executes coeff hvalid W hwidth a (b.filled a.get 0)
    heap N B hw hB filledLayout haValues values hslot v hi hbits input tape u bank ha' hb' (shared_blank_clock hs')
  exact ⟨c0+c1,t,_,e0.seq e1,Nat.add_le_add hc0 hc1,ht,sized,denominator,counter,hv⟩

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
  obtain ⟨cost,t,out,he,hcost,hr,_,_,_,hv⟩ := copied_executes coeff hvalid W hwidth a b heap N B hw hB hl
    haValues hslot haWidth haMeta hbMeta hbSlot hsep hdisjoint logical hlogicalWidth hlogicalGood
    v hi hbits input tape xs origin hlen s hn hcount hbank hs ha hb
  obtain ⟨hrun,hsteps⟩ := he.compiled_run
    (copiedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) (by omega)
  exact ⟨t,out,hrun,hsteps ▸ hcost,hr,hv⟩

#print axioms copied_executes
#print axioms copied_computes

end Maxwell.Continuum.Calibration.NeumannMachine
