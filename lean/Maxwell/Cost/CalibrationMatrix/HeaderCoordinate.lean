import Maxwell.Cost.CalibrationMatrix.HeaderWords
import Maxwell.Cost.CalibrationMatrix.Residue
import Maxwell.Cost.CalibrationMatrix.Phase

namespace Maxwell.Cost.CalibrationMatrix.HeaderCoordinate
open Structured BankArray
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

def changes : Finset ℕ := {0, 1, 2, 3, 4, 80, 81, 82, 83, 84, 85, 86, 90}
def WorkBlank (s : BitRAMState) : Prop := ∀ i, 80 ≤ i → i ≤ 86 → Blank s i
def ScratchBlank (s : BitRAMState) : Prop := ∀ i, i < 10 → Blank s i

theorem join {a b : Finset ℕ} {s t u : BitRAMState}
    (h : BinaryPrecision.Frame a s t) (k : BinaryPrecision.Frame b t u) :
    BinaryPrecision.Frame (a ∪ b) s u :=
  (h.mono Finset.subset_union_left).trans (k.mono Finset.subset_union_right)

def code (source : ℕ) : Code :=
  .seq (Residue.code 131 source 81)
  (.seq (padWordCode 81 130 80)
  (.seq (padWordCode 127 130 82)
  (.seq (.call (TapeOps.copyClear 80 86))
  (.seq (.call (TapeOps.copyClear 82 86))
  (.seq (.call (Rewind.program 86))
  (.seq (Phase.code 86 84 85)
  (.seq (padWordCode 84 130 83)
  (.seq (.call (TapeOps.copyClear 83 90))
  (.seq (.call (TapeOps.clear 81)) (.call (TapeOps.clear 84)))))))))))

/-- One physical coordinate is reduced, shifted to the period20 cell, and
appended as five bits. Every temporary word is consumed or cleared. -/
theorem executes (source : ℕ) (hsource : 150 ≤ source)
    (input : List Bool) (tape : ℕ → Bool) (raw preceding : List Bool)
    (r : ℕ) (hr : r < 20) (origin : ℤ) (s : Store)
    (hraw : Word s.val source raw) (hR : Word s.val 127 r.bits)
    (hclock : Word s.val 130 (31 : ℕ).bits) (hradix : Word s.val 131 (20 : ℕ).bits)
    (hout : s.val.tapes 90 = BitTape.shiftedEnd preceding origin)
    (hwork : WorkBlank s.val) (hscratch : ScratchBlank s.val) :
    ∃ cost t, cost ≤ 700*(raw.length+8)^2+1000 ∧
      Executes input tape (code source) cost s t ∧
      t.val.tapes 90 = BitTape.shiftedEnd
        (preceding ++ TableKey.field 5 (Phase.phase (addressValue raw % 20) r)) origin ∧
      WorkBlank t.val ∧ ScratchBlank t.val ∧ BinaryPrecision.Frame changes s.val t.val := by
  let x := addressValue raw % 20
  have hx : x < 20 := Nat.mod_lt _ (by decide)
  obtain ⟨c1, s1, hc1, e1, w1, len1, scratch1, f1⟩ := Residue.executes 131 source 81
    (by omega) (by omega) (by omega) input tape raw s hradix hraw
    (hwork 81 (by omega) (by omega)) (fun i hi => hscratch i (by omega))
  obtain ⟨c2, s2, hc2, e2, w2, f2⟩ := HeaderWords.pad_raw 81 130 80
    (by decide) (by decide) (by decide) input tape 5 (31 : ℕ).bits x.bits (by decide) s1 w1
    (f1.word (by simp [Residue.changes]) hclock)
    (f1.blank (by simp [Residue.changes]) (hwork 80 (by omega) (by omega)))
  have f02 := join f1 f2
  obtain ⟨c3, s3, hc3, e3, w3, f3⟩ := HeaderWords.pad_raw 127 130 82
    (by decide) (by decide) (by decide) input tape 5 (31 : ℕ).bits r.bits (by decide) s2
    (f02.word (by simp [Residue.changes]) hR)
    (f02.word (by simp [Residue.changes]) hclock)
    (f02.blank (by simp [Residue.changes]) (hwork 82 (by omega) (by omega)))
  have f03 := join f02 f3
  obtain ⟨ko, hk⟩ := hwork 86 (by omega) (by omega)
  have keyEmpty : s3.val.tapes 86 = BitTape.shiftedEnd [] ko := by
    rw [f03.tapes 86 (by simp [Residue.changes]), hk]
    simp [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank]
  obtain ⟨s4, e4, z4, k4, f4⟩ := HeaderWords.append 80 86 (by decide) input tape
    (TableKey.field 5 x) [] ko s3 (f3.word (by simp) w2) keyEmpty
  obtain ⟨s5, e5, z5, k5, f5⟩ := HeaderWords.append 82 86 (by decide) input tape
    (TableKey.field 5 r) (TableKey.field 5 x) ko s4 (f4.word (by simp) w3) (by simpa using k4)
  obtain ⟨s6, e6, k6, f6⟩ := HeaderWords.rewind 86 input tape (Phase.encode x r) ko s5 k5
  have f06 := join (join (join f03 f4) f5) f6
  obtain ⟨c7, s7, hc7, e7, w7, z7, k7, f7raw⟩ := Phase.executes 86 84 85
    (by decide) (by decide) (by decide) input tape x r hx hr ko s6 k6
    (f06.blank (by simp [Residue.changes]) (hwork 84 (by omega) (by omega)))
    (f06.blank (by simp [Residue.changes]) (hwork 85 (by omega) (by omega)))
  have f7 : BinaryPrecision.Frame {86,84,85} s6.val s7.val := f7raw
  have f07 := join f06 f7
  obtain ⟨c8, s8, hc8, e8, w8, f8⟩ := HeaderWords.pad_raw 84 130 83
    (by decide) (by decide) (by decide) input tape 5 (31 : ℕ).bits (Phase.phase x r).bits
    (by decide) s7 w7 (f07.word (by simp [Residue.changes]) hclock)
    (f07.blank (by simp [Residue.changes]) (hwork 83 (by omega) (by omega)))
  have f08 := join f07 f8
  obtain ⟨s9, e9, z9, out9, f9⟩ := HeaderWords.append 83 90 (by decide) input tape
    (TableKey.field 5 (Phase.phase x r)) preceding origin s8 w8
    ((f08.tapes 90 (by simp [Residue.changes])).trans hout)
  have f19 := join (join (join (join (join (join (join f2 f3) f4) f5) f6) f7) f8) f9
  obtain ⟨s10, e10, z10, f10⟩ := HeaderWords.clear 81 input tape x.bits s9
    (f19.word (by simp) w1)
  have f710 := join (join f8 f9) f10
  obtain ⟨t, e11, z11, f11⟩ := HeaderWords.clear 84 input tape (Phase.phase x r).bits s10
    (f710.word (by simp) w7)
  have f79 := join f8 f9
  have f711 := join (join f79 f10) f11
  have f611 := join f7 f711
  have f511 := join f6 f611
  have f411 := join f5 f511
  have f311 := join f4 f411
  have f211 := join f3 f311
  have f111 := join f2 f211
  have f011 := join f1 f111
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq
    (e8.seq (e9.seq (e10.seq e11)))))))))
  simp only [TableKey.field_length, Phase.encode_length] at he
  refine ⟨_, t, ?_, he, ?_, ?_, ?_, f011.mono ?_⟩
  · have hxlen : x.bits.length ≤ 5 := by simpa only [Nat.size_eq_bits_len] using len1
    have hplen : (Phase.phase x r).bits.length ≤ 5 := by
      simpa only [Nat.size_eq_bits_len] using Phase.phase_bits x r
    omega
  · exact ((join f10 f11).tapes 90 (by simp)).trans out9
  · intro i hi hi'
    interval_cases i
    · exact f411.blank (by simp) z4
    · exact f11.blank (by simp) z10
    · exact f511.blank (by simp) z5
    · exact (join f10 f11).blank (by simp) z9
    · exact z11
    · exact f711.blank (by simp) z7
    · exact f711.blank (by simp) ⟨ko+10, k7⟩
  · intro i hi
    by_cases hi5 : i < 5
    · exact f111.blank (by simp; omega) (scratch1 i hi5)
    · exact f011.blank (by simp [Residue.changes]; omega) (hscratch i hi)
  · intro i hi
    simpa [changes, Residue.changes, or_assoc, or_left_comm, or_comm] using hi

end Maxwell.Cost.CalibrationMatrix.HeaderCoordinate
