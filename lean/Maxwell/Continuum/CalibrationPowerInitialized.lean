import Maxwell.Continuum.CalibrationPowerChannels
import Maxwell.Continuum.CalibrationNeumannInitialized

/-! Runtime descriptor setup followed by exact fixed-matrix powers. All
per-iteration write bounds follow from the original raw coefficient table. -/

namespace Maxwell.Continuum.Calibration.PowerMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
open NeumannMachine
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def bufferChannels {n : ℕ} (b : Buffers n) : Channels n :=
  ⟨fun i => addressValue (b.data.vectorPositive.get i),
   fun i => addressValue (b.data.vectorNegative.get i)⟩

theorem bufferChannels_eq {n : ℕ} {b : Buffers n} {A : ChannelMatrix n} {x : Channels n}
    (h : b.data.Decodes A x) : bufferChannels b = x := by
  apply congrArg₂ Channels.mk <;> funext i
  · exact h.vectorPositive i
  · exact h.vectorNegative i

def initializedCode : Code := .seq setupCode powerCode

def initializedCost (n width heap D N B : ℕ) : ℕ :=
  setupCost B width+powerCost N n (initializedWidth n width heap D N B)

theorem initialized_executes {n : ℕ} (coeff : CoefficientIndex n → Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (hw : 0 < addressValue a.width) (hB : 0 < B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i = SharedTable.integerParts (paddedCoefficients coeff) i)
    (hbValues : ∀ i, b.get i = a.get i)
    (hslot : rawPowerWidth n W N ≤ addressValue a.width)
    (v : ℕ → ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap
      (SharedTable.denominator coeff) N)
    (hbits : ∀ i ∈ Descriptors.ids, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (ha : a.Ready s) (hb : b.OutputReady s) (h101 : RationalAccumulator.Blank s.val 101) :
    ∃ (cost : ℕ) (t : Store) (out : Buffers n),
      Executes input tape initializedCode cost s t ∧
      cost ≤ initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B ∧
      out.Ready n.bits
        (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) t.val ∧
      out.Sized (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 N ∧
      out.data.Decodes (rawMatrix coeff) (matrixPower (rawMatrix coeff) (rawSource coeff) N) ∧
      (0<N → ∀ i : Fin n,
        (addressValue (out.positive.get i):ℤ)-addressValue (out.negative.get i)=
          (matrixPower (rawMatrix coeff) (rawSource coeff) (N-1)).value i) ∧
      RationalAccumulator.Blank t.val 140 ∧
      ∀ i : Fin n, ((bufferChannels out).value i : ℚ)/(SharedTable.denominator coeff : ℚ)^(N+1) =
        rationalPower (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) N i := by
  let start := initialSnapshot a b heap (SharedTable.denominator coeff) hw s.val.memory
  let buffers := start.data.productBuffers start.words 10 11 5 4
  let width := initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B
  have decode := initialSnapshot_decodes coeff a b heap hw s.val.memory haValues hbValues
  have db : buffers.data.Decodes (rawMatrix coeff) (rawSource coeff) := by
    have h := decode.matrix.product start.words 10 11
    rw [decode.value] at h
    exact h
  have hpb (k : ℕ) (hk : k ≤ N) (i : Fin n) := rawTable_power_width coeff W N hwidth k hk i
  have hbound := Buffers.iterate_fits_of_bits db N
    (fun k hk i => (hpb k hk i).1.trans hslot)
    (fun k hk i => (hpb k hk i).2.trans hslot)
  have previous : 0<N → ∀ i : Fin n,
      (addressValue ((buffers.iterate N).positive.get i):ℤ)-
          addressValue ((buffers.iterate N).negative.get i)=
        (matrixPower (rawMatrix coeff) (rawSource coeff) (N-1)).value i := by
    intro hN i
    cases N with
    | zero => omega
    | succ k =>
      have hk := Buffers.iterate_fits_of_bits db k
        (fun j hj i => (hpb j (by omega) i).1.trans hslot)
        (fun j hj i => (hpb j (by omega) i).2.trans hslot)
      change (bufferChannels (buffers.iterate k)).value i=
        (matrixPower (rawMatrix coeff) (rawSource coeff) k).value i
      rw [bufferChannels_eq hk.2]
  have hsized : start.data.Sized width := by
    have h := initialData_sized a heap (SharedTable.denominator coeff) N hw hl.canonical
    have hm : setupWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N ≤ width := by
      dsimp [width,initializedWidth]; omega
    exact ⟨h.1.trans hm,h.2.1.trans hm,h.2.2.1.trans hm,h.2.2.2.1.trans hm,
      fun i => (h.2.2.2.2.1 i).trans hm,h.2.2.2.2.2.1.trans hm,h.2.2.2.2.2.2.trans hm⟩
  have hsize := setupWidth_dimension n (addressValue a.width) heap (SharedTable.denominator coeff) N
  have hcount := setupWidth_count n (addressValue a.width) heap (SharedTable.denominator coeff) N
  have hbwidth : B ≤ width := by dsimp [width,initializedWidth]; omega
  have hwidth' : setupWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N ≤ width := by
    dsimp [width,initializedWidth]; omega
  obtain ⟨c0,u,e0,hc0,hu,hu140,hu304,_⟩ := setup_executes a b heap (SharedTable.denominator coeff) N B
    hw hB hl v hi hbits input tape s hbank ha hb h101
  have hu' := Snapshot.ready_mono hu hbwidth
  have hr : buffers.Ready n.bits width u.val := Horner.productBuffers_ready hu'.1 hu'.2.1 hu'.2.2
  obtain ⟨origin,h140⟩ := hu140
  obtain ⟨c1,t,hc1,e1,ht,hblank,frame,_⟩ := power_executes buffers N width
    (Horner.productBuffers_sized start.words 10 11 5 4 hsized)
    (Horner.productBuffers_separated start.data start.words 10 11 5 4
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hbound.1
    (hsize.1.trans_le (Nat.pow_le_pow_right (by decide) hwidth'))
    (hsize.2.trans_le (Nat.pow_le_pow_right (by decide) hwidth'))
    hw input tape n.bits N.bits (addressValue_bits n) (hcount.1.trans hwidth')
    (addressValue_bits N) (hcount.2.trans hwidth') origin u hr h140
  have keep (i : ℕ) (hi : i=126 ∨ i=304) : t.val.tapes i=u.val.tapes i :=
    frame.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have denominator : RationalAccumulator.Word u.val 126 (SharedTable.denominator coeff) := by
    simpa only [start,initialSnapshot,initialData] using hu.2.1.K
  refine ⟨c0+c1,t,buffers.iterate N,e0.seq e1,Nat.add_le_add hc0 hc1,
    ht,(Horner.productBuffers_sized start.words 10 11 5 4 hsized).iterate N,
    RationalAccumulator.word_of_eq (keep 126 (Or.inl rfl)) denominator,
    RationalAccumulator.word_of_eq (keep 304 (Or.inr rfl)) hu304,hbound.2,previous,hblank,?_⟩
  intro i
  rw [bufferChannels_eq hbound.2]
  exact rawTable_power coeff hvalid N i

theorem initialized_computes {n : ℕ} (coeff : CoefficientIndex n → Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap N B : ℕ)
    (hw : 0 < addressValue a.width) (hB : 0 < B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i = SharedTable.integerParts (paddedCoefficients coeff) i)
    (hbValues : ∀ i, b.get i = a.get i)
    (hslot : rawPowerWidth n W N ≤ addressValue a.width)
    (v : ℕ → ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap
      (SharedTable.denominator coeff) N)
    (hbits : ∀ i ∈ Descriptors.ids, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank Descriptors.ids v s.val)
    (ha : a.Ready s) (hb : b.OutputReady s) (h101 : RationalAccumulator.Blank s.val 101) :
    ∃ (t : Store) (out : Buffers n),
      (runPriced (initializedCode.compile.next input tape)
        (initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) s.val).finished =
          some (t.place initializedCode.size) ∧
      (runPriced (initializedCode.compile.next input tape)
        (initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) s.val).instructions ≤
          initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B ∧
      out.Ready n.bits
        (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) N B) t.val ∧
      ∀ i : Fin n, ((bufferChannels out).value i : ℚ)/(SharedTable.denominator coeff : ℚ)^(N+1) =
        rationalPower (fun i j => (coeff (.inr (i,j))).value)
          (fun i => (coeff (.inl i)).value) N i := by
  obtain ⟨cost,t,out,he,hcost,hr,_,_,_,_,_,_,hv⟩ := initialized_executes coeff hvalid W hwidth a b heap N B
    hw hB hl haValues hbValues hslot v hi hbits input tape s hbank ha hb h101
  obtain ⟨hrun,hsteps⟩ := he.compiled_run
    (initializedCost n (addressValue a.width) heap (SharedTable.denominator coeff) N B+1) (by omega)
  exact ⟨t,out,hrun,hsteps ▸ hcost,hr,hv⟩

#print axioms initialized_executes
#print axioms initialized_computes

end Maxwell.Continuum.Calibration.PowerMachine
