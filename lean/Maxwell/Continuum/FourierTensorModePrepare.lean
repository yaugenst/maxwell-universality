import Maxwell.Continuum.FourierTensorModeDecodeSemantics
import Maxwell.Continuum.RationalDataflowRowWritePlan

/-! One actual row preparation reads the two calibrated Fourier channels,
decodes their alias, multiplies by the stored physical normalization and
frequency scale, and rounds the two amplitudes. The program is fixed. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code (j : Fin 3) : Code := .seq (ModeIndex.code j)
  (.seq ModeIndex.readCode (.seq ArrayDecodeMachine.decodeLoadCode RowArithmetic.code))

def values (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) : ℕ→Parts :=
  RowArithmetic.output P (ModeDecode.rowValues R a j r v)

theorem floor_table_frame {m : ℕ} {a : Table m} {s t : Store}
    (h : a.Ready s)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace RowArithmetic.bank) s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,200,202,203,204,205}:Finset ℕ)) :=
    f.tapes i (by
      have hd : Disjoint ({5,6,7,8,9,200,202,203,204,205}:Finset ℕ)
        (DyadicFloor.StoredPower.workspace RowArithmetic.bank) := by decide
      exact fun hm => Finset.disjoint_left.mp hd hi hm)
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven,
    BankArray.word_of_eq (keep 200 (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem floor_output_frame {m : ℕ} {a : Table m} {s t : Store}
    (h : a.OutputReady s)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace RowArithmetic.bank) s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hm : i∈({37,210,212,213,214,215}:Finset ℕ) := by simpa using hi
  have hd : Disjoint ({37,210,212,213,214,215}:Finset ℕ)
    (DyadicFloor.StoredPower.workspace RowArithmetic.bank) := by decide
  exact f.tapes i (fun h => Finset.disjoint_left.mp hd hm h)

theorem floor_natural_frame {n : ℕ→ℕ} {s t : Store}
    (h : NatAssign.Bank ModeIndex.ports n s.val)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace RowArithmetic.bank) s.val t.val) :
    NatAssign.Bank ModeIndex.ports n t.val := by
  intro i hi
  have hd : Disjoint ModeIndex.ports (DyadicFloor.StoredPower.workspace RowArithmetic.bank) := by decide
  exact RationalAccumulator.word_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h i hi)

theorem executes {m : ℕ} (P R W : ℕ) (hW : 2≤W)
    (a : Table (2*aliasArraySize R)) (b : Table m) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts)
    (hma : a.MetadataWidth W) (hw : WidthBank RowArithmetic.bank W v)
    (hg : Good RowArithmetic.bank v) (hav : ∀i,(a.get i).Valid)
    (hR : R.bits.length≤W) (hsize : (aliasArraySize R).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (hrow : addressValue word=r.val) (s : Store)
    (hr : RationalDataflow.Ready RowArithmetic.bank v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hc : BankArray.Word s.val 201 word)
    (hn : NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) s.val)
    (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape (code j) cost s t ∧ cost≤2^190*(P+W+10)^2 ∧
      RationalDataflow.Ready RowArithmetic.bank (values P R a j r v) t ∧
      WidthBank RowArithmetic.bank (2^15*(P+W+1)) (values P R a j r v) ∧
      Good RowArithmetic.bank (values P R a j r v) ∧ a.Ready t ∧ b.OutputReady t ∧
      NatAssign.Bank ModeIndex.ports
        (ModeDecode.after (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val)) t.val ∧
      (∀i∈ModeIndex.ports,
        (ModeDecode.after (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val) i).bits.length
          ≤128*(W+1)+8) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 201 word ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,s0,e0,hc0,n0,wn0,z0,f0⟩ := ModeIndex.executes j R (aliasArraySize R) W hW hR hsize
    input tape word hlen s hc hn hr.2
  rw [hrow] at n0 wn0
  have a0 := ModeIndex.table_frame ha f0 z0
  have b0 := ModeIndex.output_frame hb f0 a0.scratch a0.seven
  have p0 := RationalAccumulator.word_of_eq (f0.tapes 144 (by decide)) hp
  obtain ⟨c1,s1,e1,hc1,r1,w1,g1,a1,n1,z1,f1⟩ := ModeIndex.read_executes R W a j r v hma hw hg hav wn0
    input tape s0 (ModeIndex.ready_frame hr f0 z0) a0 n0 (ModeIndex.floor_frame hz f0)
  have b1 := b0.rowPlan_frame f1 a1.scratch a1.seven
  have p1 : Word s1.val 144 (2^P) :=
    RationalAccumulator.word_of_eq (f1.tapes 144 (by decide) (by decide) (by decide)) p0
  obtain ⟨c2,s2,e2,hc2,r2,g2,w2,n2,wn2,z2,f2⟩ := ModeDecode.executes _ _ (64*(W+1)) (by omega)
    (w1.mono (by omega)) g1 wn0 input tape s1 r1 n1 z1
  have a2 := ModeDecode.table_frame a1 f2 r2.2
  have b2 := ModeDecode.output_frame b1 f2 a2.scratch a2.seven
  have p2 := RationalAccumulator.word_of_eq (f2.tapes 144 (by decide)) p1
  obtain ⟨c3,t,e3,hc3,r3,w3,g3,z3,p3,f3⟩ := RowArithmetic.executes P (2*(64*(W+1))+8) _ w2 g2
    input tape s2 r2 z2 p2
  have a3 := floor_table_frame a2 f3 r3.2
  have b3 := floor_output_frame b2 f3 a3.scratch a3.seven
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,r3,w3.mono ?_,g3,a3,b3,
    floor_natural_frame n2 f3,?_,z3,p3,?_,?_,f3.output.trans (f2.output.trans (f1.output.trans f0.output))⟩
  · nlinarith only [hc0,hc1,hc2,hc3,Nat.zero_le P,Nat.zero_le W]
  · omega
  · intro i hi
    convert wn2 i hi using 1
    ring
  · exact BankArray.word_of_eq
      ((f3.tapes 201 (by decide)).trans ((f2.tapes 201 (by decide)).trans
        (f1.counter.trans (f0.tapes 201 (by decide))))) hc
  · exact (f3.tapes 201 (by decide)).trans ((f2.tapes 201 (by decide)).trans
      (f1.counter.trans (f0.tapes 201 (by decide))))

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
