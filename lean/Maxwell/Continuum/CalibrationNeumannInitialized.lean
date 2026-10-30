import Maxwell.Continuum.CalibrationNeumannSetupWidth

/-! One fixed execution now includes the runtime descriptor setup and all
Neumann layers. Actual raw coefficient values determine the result, and
all array-write and metadata widths are derived rather than assumed. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2500000

theorem Snapshot.ready_mono {n B C : ℕ} {a : Snapshot n} {xs : List Bool} {s : BitRAMState}
    (h : a.Ready xs B s) (hBC : B≤C) : a.Ready xs C s := by
  obtain ⟨⟨vi,hvi,hvl,hw⟩,hs,hp⟩ := h
  exact ⟨⟨vi,hvi,hvl.trans hBC,hw⟩,hs,hp⟩

def initializedCode : Code := .seq setupCode code
def initializedWidth (n width heap D N B : ℕ) : ℕ := B+setupWidth n width heap D N
def initializedCost (n width heap D N B : ℕ) : ℕ :=
  setupCost B width+costCap N n (initializedWidth n width heap D N B)

theorem Snapshot.iterate_denominator {n : ℕ} (a : Snapshot n) (k : ℕ) :
    (a.iterate k).data.K=a.data.K := by
  induction k <;> simp_all [Snapshot.iterate,Snapshot.advance,recycleData,Horner.Data.permute]

theorem initialized_executes {n : ℕ} (coeff : CoefficientIndex n→Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (hw : 0<addressValue a.width) (hB : 0<B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hbValues : ∀ i, b.get i=a.get i)
    (hslot : commonWidth n N (W+1)≤addressValue a.width)
    (v : ℕ→ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap (SharedTable.denominator coeff) N)
    (hbits : ∀ i∈Descriptors.ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (ha : a.Ready s) (hb : b.OutputReady s) (h101 : RationalAccumulator.Blank s.val 101) :
    ∃ cost t, Executes input tape initializedCode cost s t ∧
      cost ≤ initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B ∧
      ((initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory).iterate N).Ready
        n.bits (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) t.val ∧
      ((initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory).iterate N).data.Sized
        (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 N ∧
      RationalAccumulator.Blank t.val 140 ∧
      ∀ i : Fin n,
        ((Horner.channels
          ((initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory).iterate N).words
          10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(N+1)=
          rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
            (fun i => (coeff (.inl i)).value) (N+1) i := by
  let start := initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory
  let width := initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B
  have decode := initialSnapshot_decodes coeff a b heap hw s.val.memory haValues hbValues
  have hfit := Snapshot.iterate_fits decode (rawMatrix_bounded coeff W hwidth)
    (rawSource_bounded coeff W hwidth) N ((rawTable_uniformWidth coeff W N hwidth).trans hslot)
  have hsized : start.data.Sized width := by
    have h := initialData_sized a heap (SharedTable.denominator coeff) N hw hl.canonical
    have hm : setupWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N≤width := by
      dsimp [width,initializedWidth]; omega
    exact ⟨h.1.trans hm,h.2.1.trans hm,h.2.2.1.trans hm,h.2.2.2.1.trans hm,
      fun i => (h.2.2.2.2.1 i).trans hm,h.2.2.2.2.2.1.trans hm,h.2.2.2.2.2.2.trans hm⟩
  have hsize := setupWidth_dimension n (addressValue a.width) heap (SharedTable.denominator coeff) N
  have hcount := setupWidth_count n (addressValue a.width) heap (SharedTable.denominator coeff) N
  have hbwidth : B≤width := by dsimp [width,initializedWidth]; omega
  have hwidth' : setupWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N≤width := by
    dsimp [width,initializedWidth]; omega
  have hm := hsize.1.trans_le (Nat.pow_le_pow_right (by decide) hwidth')
  have hn := hsize.2.trans_le (Nat.pow_le_pow_right (by decide) hwidth')
  obtain ⟨c0,u,e0,hc0,hu,hu140,hu304,_⟩ := setup_executes a b heap (SharedTable.denominator coeff) N B
    hw hB hl v hi hbits input tape s hbank ha hb h101
  obtain ⟨origin,h140⟩ := hu140
  obtain ⟨c1,t,hc1,e1,ht,hblank,_⟩ := executes start N width hsized hm hn hfit input tape n.bits N.bits
    (addressValue_bits n) (hcount.1.trans hwidth') (addressValue_bits N) (hcount.2.trans hwidth')
    origin u (Snapshot.ready_mono hu hbwidth) h140
  have denominator : RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) := by
    simpa only [Snapshot.iterate_denominator,start,initialSnapshot,initialData] using ht.2.1.K
  have counter := RationalAccumulator.word_of_eq (e1.protectsTape 304 (by decide)) hu304
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,ht,start.iterate_sized hsized N,
    denominator,counter,hblank,?_⟩
  intro i
  have hdec := Snapshot.iterate_decodes decode N hfit
  rw [hdec.value,channels_rational_value _ _ (SharedTable.denominator_pos coeff hvalid),
    rawTable_iteration coeff hvalid]

theorem initialized_computes {n : ℕ} (coeff : CoefficientIndex n→Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (hw : 0<addressValue a.width) (hB : 0<B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hbValues : ∀ i, b.get i=a.get i)
    (hslot : commonWidth n N (W+1)≤addressValue a.width)
    (v : ℕ→ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap (SharedTable.denominator coeff) N)
    (hbits : ∀ i∈Descriptors.ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (ha : a.Ready s) (hb : b.OutputReady s) (h101 : RationalAccumulator.Blank s.val 101) :
    ∃ t : Store,
      (runPriced (initializedCode.compile.next input tape)
        (initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) s.val).finished=
          some (t.place initializedCode.size) ∧
      (runPriced (initializedCode.compile.next input tape)
        (initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) s.val).instructions≤
          initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B ∧
      ((initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory).iterate N).Ready
        n.bits (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) t.val ∧
      ∀ i : Fin n,
        ((Horner.channels
          ((initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory).iterate N).words
          10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(N+1)=
          rationalAffineIteration (fun i j => (coeff (.inr (i,j))).value)
            (fun i => (coeff (.inl i)).value) (N+1) i := by
  obtain ⟨cost,t,he,hcost,hr,_,_,_,_,hv⟩ := initialized_executes coeff hvalid W hwidth a b heap N B hw hB
    hl haValues hbValues hslot v hi hbits input tape s hbank ha hb h101
  obtain ⟨hrun,hsteps⟩ := he.compiled_run
    (initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hcost,hr,hv⟩

#print axioms initialized_executes
#print axioms initialized_computes

end Maxwell.Continuum.Calibration.NeumannMachine
