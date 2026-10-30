import Maxwell.Continuum.CalibrationNeumannCopyWidths

/-! One fixed executed program allocates the copy descriptors, duplicates
the converted coefficient table, initializes the inverse buffers, and
runs the runtime-length Neumann recurrence. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 3000000

def preparedCode : Code := .seq copyPrepareCode copiedCode
def preparedCost (n width heap D N B oldWidth : ℕ) : ℕ :=
  copyPrepareCost B width oldWidth+copiedCost n width heap D N width

theorem prepared_executes {n m : ℕ} (coeff : CoefficientIndex n → Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a : PartArray.Table (tableSize n)) (old : PartArray.Table m) (heap N B : ℕ)
    (hw : 0<addressValue a.width) (hl : SourceLayout a heap)
    (haValues : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hslot : commonWidth n N (W+1) ≤ addressValue a.width)
    (haWidth : ∀ i, (a.get i).Width (addressValue a.width))
    (haMeta : a.MetadataWidth (addressValue a.width))
    (haddress : heap.bits.length+2*n.bits.length+(addressValue a.width).bits.length+10 ≤
      addressValue a.width)
    (hprepare : 2^CopyPlan.plan.length*(B+1) ≤ addressValue a.width)
    (logical : ℕ → Parts) (hlogicalWidth : WidthBank {1} (addressValue a.width) logical)
    (hlogicalGood : Good {1} logical)
    (v : ℕ → ℕ)
    (hi : CopyPlan.Inputs v n (addressValue a.width) heap (SharedTable.denominator coeff) N)
    (hbits : ∀ i ∈ CopyPlan.ids, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length ≤ addressValue a.width) (s : Store) (hn : addressValue xs=tableSize n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hbank : NatAssign.Bank CopyPlan.ids v s.val)
    (hs : SharedConversion.Ready {1} logical s) (ha : a.Ready s) (ho : old.OutputReady s) :
    ∃ (cost : ℕ) (t : Store) (out : Snapshot n), Executes input tape preparedCode cost s t ∧
      cost ≤ preparedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B
        (addressValue old.width) ∧
      out.Ready n.bits
        (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N
          (addressValue a.width)) t.val ∧
      out.data.Sized (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N
        (addressValue a.width)) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 N ∧
      ∀ i : Fin n, ((Horner.channels out.words 10 11).value i : ℚ) /
          (SharedTable.denominator coeff : ℚ)^(N+1) =
        rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) (N+1) i := by
  obtain ⟨c0,u,e0,hc0,hs',ha',hb',bank,count,_⟩ := copyPrepare_executes a old heap
    (SharedTable.denominator coeff) N B hl v hi hbits {1} logical input tape s hbank hs ha ho
  have hbits' (i : ℕ) (hi : i ∈ Descriptors.ids) :
      (NatAssign.values CopyPlan.plan v i).bits.length ≤ addressValue a.width :=
    (CopyPlan.output_width v B hbits i hi).trans hprepare
  obtain ⟨c1,t,out,e1,hc1,ht,sized,denominator,counter,heq⟩ := copied_executes coeff hvalid W hwidth a
    (copyTarget a heap s.val.memory) heap N (addressValue a.width) hw hw
    (copyTarget_layout a heap s.val.memory hl) haValues hslot haWidth haMeta
    (copyTarget_metadata a heap (addressValue a.width) s.val.memory haMeta haddress)
    le_rfl (copyTarget_separated a heap s.val.memory) (copyTarget_disjoint a heap s.val.memory hl)
    logical hlogicalWidth hlogicalGood (NatAssign.values CopyPlan.plan v)
    (CopyPlan.outputs v n (addressValue a.width) heap (SharedTable.denominator coeff) N hi)
    hbits' input tape xs origin hlen u hn (count.trans hcount) bank hs' ha' hb'
  exact ⟨c0+c1,t,out,e0.seq e1,Nat.add_le_add hc0 hc1,ht,sized,denominator,counter,heq⟩

#print axioms prepared_executes

end Maxwell.Continuum.Calibration.NeumannMachine
