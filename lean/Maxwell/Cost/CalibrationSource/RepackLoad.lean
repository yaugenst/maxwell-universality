import Maxwell.Cost.ModeRead
import Maxwell.Cost.CalibrationSource.RepackWrite

/-! Read the two channels of the retained shared mode without changing its
storage width. The following write stage pads them to the calibration width. -/
namespace Maxwell.Cost.CalibrationSource.Repack
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

def readLayout : ModeRead.Layout := ModeRead.retained 104 ![30,31,288]

theorem readLayout_valid : readLayout.Valid := by
  apply ModeRead.retained_valid
  · decide
  · intro a; fin_cases a <;> decide
  · intro a b h; fin_cases a <;> fin_cases b <;> simp_all
  · intro a; fin_cases a <;> decide

def readCode : Code := .seq (ModeRead.channelCode readLayout 0)
  (ModeRead.channelCode readLayout 1)

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j = 4 ∨ 10 ≤ j → j ≠ 30 → j ≠ 31 → j ≠ 37 → j ≠ 104 →
    t.tapes j = s.tapes j

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.inputHead.trans h.inputHead, k.randomCursor.trans h.randomCursor,
    k.output.trans h.output,
    fun j hj h30 h31 h37 h104 =>
      (k.tapes j hj h30 h31 h37 h104).trans (h.tapes j hj h30 h31 h37 h104)⟩

theorem Frame.of_row {s t : BitRAMState} (h : RowFrame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun j hj h30 h31 h37 _ => h.2.2.2.1 j hj h30 h31 h37⟩

theorem modeReady {s : BitRAMState} (h : Ready s (dotValues 0 0)) (h4 : Blank s 4) :
    ModeRead.Ready s := by
  rcases h.2.1 with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  intro j hj
  interval_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h.2.2
  · exact h8
  · exact h9

/-- Actual indexed reads into the signed accumulator ports, retaining the
same physical array data and every persistent metadata word. -/
theorem read {m : ℕ} (d : ModeRead.Data m) (i : Fin m) (B : ℕ) (hd : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hs : Ready s.val (dotValues 0 0)) (h4 : Blank s.val 4)
    (h37 : Blank s.val 37) (hst : ModeRead.Stored readLayout d s.val)
    (h104 : BankArray.Word s.val 104 index) :
    ∃ cost t, cost ≤ 40000*(B+2)^2 ∧ Executes input tape readCode cost s t ∧
      Ready t.val (dotValues (d.value i 0) (d.value i 1)) ∧ Blank t.val 4 ∧
      Blank t.val 37 ∧ ModeRead.Stored readLayout d t.val ∧
      t.val.memory = s.val.memory ∧ Frame s.val t.val ∧ BankArray.Word t.val 104 index := by
  have hz (j : ℕ) (hj : 30 ≤ j) (hj' : j ≤ 36) : Blank s.val j := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa [dotValues] using hs.1 j hj hj'
  obtain ⟨c0,a,hc0,e0,r0,st0,w0,f0,same0⟩ := ModeRead.channel readLayout
    readLayout_valid d i 0 B hd input tape index hi hil s (modeReady hs h4) hst h104 (hz 30 (by omega) (by omega))
  obtain ⟨c1,t,hc1,e1,r1,st1,w1,f1,same1⟩ := ModeRead.channel readLayout
    readLayout_valid d i 1 B hd input tape index hi hil a r0 st0
      (BankArray.word_of_eq (same0 104 (Or.inr (by omega)) (by simp [readLayout,ModeRead.retained])) h104)
      (RationalAccumulator.blank_of_eq (same0 31 (Or.inr (by omega)) (by simp [readLayout,ModeRead.retained]))
        (hz 31 (by omega) (by omega)))
  have keep (j : ℕ) (hj : j = 4 ∨ 10 ≤ j) (h30 : j ≠ 30) (h31 : j ≠ 31) :
      t.val.tapes j = s.val.tapes j :=
    (same1 j hj h31).trans (same0 j hj h30)
  refine ⟨c0+c1,t,by omega,e0.seq e1,⟨?_,?_,r1 7 (by decide)⟩,r1 4 (by decide),
    RationalAccumulator.blank_of_eq (keep 37 (Or.inr (by omega)) (by omega) (by omega)) h37,
    st1,f1.memory.trans f0.memory,?_,BankArray.word_of_eq (keep 104 (by omega) (by omega) (by omega)) h104⟩
  · intro j hj hj'
    by_cases h30 : j = 30
    · subst j
      simpa [dotValues,readLayout,ModeRead.retained] using RationalAccumulator.word_of_eq
        (same1 30 (Or.inr (by omega)) (by simp [readLayout,ModeRead.retained])) w0
    · by_cases h31 : j = 31
      · subst j; simpa [dotValues,readLayout,ModeRead.retained] using w1
      · have : dotValues (d.value i 0) (d.value i 1) j = dotValues 0 0 j := by
          simp [dotValues,h30,h31]
        rw [this]
        exact RationalAccumulator.word_of_eq (keep j (Or.inr (by omega)) h30 h31) (hs.1 j hj hj')
  · exact ⟨r1 0 (by decide),r1 1 (by decide),r1 2 (by decide),r1 3 (by decide),
      r1 5 (by decide),r1 6 (by decide),r1 8 (by decide),r1 9 (by decide)⟩
  · exact ⟨f1.inputHead.trans f0.inputHead,f1.randomCursor.trans f0.randomCursor,
      f1.output.trans f0.output,fun j hj h30 h31 _ _ => keep j hj h30 h31⟩

end Maxwell.Cost.CalibrationSource.Repack
