import Maxwell.Cost.RoutingPorts.Complete.Probe

/-! A fixed two-write stage fills an actual forward/inverse routing pair.
The two existing arrays and all non-array memory are preserved as specified
by the literal memory writes; no destination snapshot is supplied. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def pairCode : Code :=
  .seq (BankArray.writeCanonicalCode 711 730 716 718 731)
    (BankArray.writeCanonicalCode 711 731 717 718 730)

def pairCost {n : ℕ} (l : Layout n) (i j : Fin n) : ℕ :=
  BankArray.costCap n.bits.length.bits i.val.bits l.forward.bits
      (FixedWidth.bits n.bits.length j.val.bits)+100*n.bits.length+100+
    (BankArray.costCap n.bits.length.bits j.val.bits l.backward.bits
      (FixedWidth.bits n.bits.length i.val.bits)+100*n.bits.length+100)

theorem pair_write {n : ℕ} (l : Layout n) (forward backward : Vector ℕ n)
    (i j : Fin n) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (hm : Metadata l s.val) (ha : Stored l forward backward s.val)
    (hi : RationalAccumulator.Word s.val 730 i.val)
    (hj : RationalAccumulator.Word s.val 731 j.val) :
    ∃cost t, Executes input tape pairCode cost s t ∧ cost≤pairCost l i j ∧
      Ready t.val ∧ Metadata l t.val ∧
      Stored l (forward.set i j.val) (backward.set j i.val) t.val ∧
      t.val.memory=MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory (l.forward+i.val*n.bits.length)
          (FixedWidth.bits n.bits.length j.val.bits))
        (l.backward+j.val*n.bits.length) (FixedWidth.bits n.bits.length i.val.bits) ∧
      Frame {37} s.val t.val := by
  have hn : 0<n.bits.length := RationalAccumulator.bits_nonempty l.positive
  have hwidth : 0<n.bits.length.bits.length := RationalAccumulator.bits_nonempty hn
  have hfit (k : Fin n) : k.val.bits.length≤n.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size k.isLt.le
  obtain ⟨ca,a,hca,ea,ma,aa,sa,a7,a37,fa⟩ := BankArray.write_canonical
    711 730 716 718 731 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape n.bits.length.bits i.val.bits
    l.forward.bits l.clock (encode forward) i j.val hwidth (addressValue_bits _)
    (by simpa only [addressValue_bits] using l.clock_length)
    (by simpa only [addressValue_bits] using hn)
    (by simpa only [addressValue_bits] using hfit j) s hs.scratch hs.seven hs.pack
    hm.width hi hm.forward hm.clock hj
    (by simpa only [addressValue_bits] using ha.forward)
  simp only [addressValue_bits] at ma aa hca
  have af : Frame {37} s.val a.val := Frame.of_bankExcept fa
  have am : Metadata l a.val := hm.frame af (by intro k hk; simp only [Finset.mem_singleton] at hk; exact Or.inr hk)
  have ab : BitArray.Represents a.val.memory l.backward n.bits.length (encode backward) := by
    rw [ma]
    exact IncidenceEncoding.represents_write_disjoint ha.backward l.forward n.bits.length i
      (FixedWidth.bits n.bits.length j.val.bits) (FixedWidth.bits_length _ _) l.separated.symm
  obtain ⟨cb,t,hcb,eb,mt,ta,st,t7,t37,fb⟩ := BankArray.write_canonical
    711 731 717 718 730 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape n.bits.length.bits j.val.bits
    l.backward.bits l.clock (encode backward) j i.val hwidth (addressValue_bits _)
    (by simpa only [addressValue_bits] using l.clock_length)
    (by simpa only [addressValue_bits] using hn)
    (by simpa only [addressValue_bits] using hfit i) a sa a7 a37
    am.width (RationalAccumulator.word_of_eq (af.tapes 731 (by decide) (by decide)) hj)
    am.backward am.clock
    (RationalAccumulator.word_of_eq (af.tapes 730 (by decide) (by decide)) hi)
    (by simpa only [addressValue_bits] using ab)
  simp only [addressValue_bits] at mt ta hcb
  have bf : Frame {37} a.val t.val := Frame.of_bankExcept fb
  have tf := af.trans bf
  have tat : BitArray.Represents t.val.memory l.forward n.bits.length
      (encode (forward.set i j.val)) := by
    rw [mt,encode_set]
    exact IncidenceEncoding.represents_write_disjoint aa l.backward n.bits.length j
      (FixedWidth.bits n.bits.length i.val.bits) (FixedWidth.bits_length _ _) l.separated
  refine ⟨ca+cb,t,ea.seq eb,?_,⟨st,t7,t37,?_⟩,
    hm.frame tf (by intro k hk; simp only [Finset.mem_singleton] at hk; exact Or.inr hk),
    ⟨tat,?_⟩,?_,tf⟩
  · exact Nat.add_le_add hca hcb
  · exact RationalAccumulator.blank_of_eq (tf.tapes 752 (by decide) (by decide)) hs.probe
  · simpa only [encode_set] using ta
  · rw [mt,ma]

#print axioms pair_write

end Maxwell.Cost.RoutingPorts.Complete
