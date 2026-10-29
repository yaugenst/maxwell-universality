import Maxwell.Cost.RoutingPorts.Complete.Common

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 8192

def probeCode (indexBank baseBank : ℕ) : Code :=
  .seq (BankArray.readBankCode 711 indexBank baseBank 718 752)
    (.seq (BankArray.compareCode 752 709) (.call (TapeOps.clear 752)))

/-- Read the actual table slot and compare it to the stored sentinel. The
read word is erased before returning; all metadata and cursor words survive. -/
theorem probe {n : ℕ} (indexBank baseBank : ℕ) (hiBank : 10 ≤ indexBank)
    (hbBank : 10 ≤ baseBank) (values : Vector ℕ n) (i : Fin n) (base : ℕ)
    (clock : List Bool) (hn : 0 < n) (hclock : clock.length=n.bits.length)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready s.val)
    (hcount : RationalAccumulator.Word s.val 709 n)
    (hwidth : RationalAccumulator.Word s.val 711 n.bits.length)
    (hindex : RationalAccumulator.Word s.val indexBank i.val)
    (hbase : RationalAccumulator.Word s.val baseBank base)
    (hclockWord : BankArray.Word s.val 718 clock)
    (harray : BitArray.Represents s.val.memory base n.bits.length (encode values))
    (hvalue : values.get i ≤ n) :
    ∃ cost t, cost ≤ BankArray.costCap n.bits.length.bits i.val.bits base.bits clock+
        102*n.bits.length+95 ∧
      Executes input tape (probeCode indexBank baseBank) cost s t ∧
      (t.val.registers 2=true ↔ values.get i < n) ∧ Ready t.val ∧
      t.val.memory=s.val.memory ∧ Frame {752} s.val t.val := by
  have hN : 0 < n.bits.length := RationalAccumulator.bits_nonempty hn
  have hW : 0 < n.bits.length.bits.length := RationalAccumulator.bits_nonempty hN
  obtain ⟨rc,r,hrc,er,hrword,hrs,hr7,hrm,_,fr⟩ := BankArray.read_bank
    711 indexBank baseBank 718 752 (by decide) hiBank hbBank (by decide) (by decide)
    input tape n.bits.length.bits i.val.bits base.bits clock (encode values) i hW
    (addressValue_bits _) (by simpa only [addressValue_bits] using hclock) s hs.scratch hs.seven hs.probe
    hwidth hindex hbase hclockWord (by simpa only [addressValue_bits] using harray)
  have countR := RationalAccumulator.word_of_eq (fr.2.2.2.1 709 (by decide) (by decide)) hcount
  have hlen : ((encode values).get i).length=n.bits.length := by simp [encode_get,FixedWidth.bits_length]
  obtain ⟨a,ea,ha2,has,ham,hak,fa⟩ := BankArray.compare_bank 752 709 (by decide) (by decide)
    input tape ((encode values).get i) n.bits hlen r hrword countR hrs
  obtain ⟨origin,ho⟩ := hrword
  obtain ⟨t,et,ht,ft⟩ := WordCall.clear 752 input tape ((encode values).get i) origin a
    ((hak 752 (by decide)).trans ho)
  have tc : Frame {752} a.val t.val := by
    refine ⟨ft.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_,?_⟩
    · intro j _ hj
      simp only [Finset.mem_singleton] at hj
      simp [ht,hj]
    · intro j hj _ _ h26 h27 _ _
      exact ft.2.2.2.2.2.2 j h26 h27
  have frame := (Frame.of_bankExcept fr).trans ((Frame.of_bank fa).trans tc)
  have keep (j : ℕ) (hj : j ≠ 752) : t.val.tapes j=a.val.tapes j := by simp [ht,hj]
  have hreg : t.val.registers 2=a.val.registers 2 := ft.2.2.2.2.2.2 2 (by decide) (by decide)
  refine ⟨_,t,?_,er.seq (ea.seq et),?_,?_,ft.2.2.1.trans (ham.trans hrm),frame⟩
  · simp only [addressValue_bits] at hrc
    rw [hlen]
    omega
  · rw [hreg,ha2,encode_value values i hvalue,addressValue_bits]
  · refine ⟨?_,?_,?_,⟨origin+((encode values).get i).length,by simp [ht]⟩⟩
    · rcases has with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
      exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
        RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
        RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
        RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
        RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
        RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
        RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
        RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩
    · exact RationalAccumulator.blank_of_eq ((keep 7 (by decide)).trans (hak 7 (by decide))) hr7
    · exact RationalAccumulator.blank_of_eq (frame.tapes 37 (by decide) (by decide)) hs.pack

end Maxwell.Cost.RoutingPorts.Complete
