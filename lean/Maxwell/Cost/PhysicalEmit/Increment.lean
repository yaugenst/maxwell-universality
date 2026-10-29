import Maxwell.Cost.RationalCanonical
import Maxwell.Cost.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator

structure LoopFrame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ changed → t.tapes i = s.tapes i
  registers : ∀ i, 4 < i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i

theorem LoopFrame.trans {a b : Finset ℕ} {s t u : BitRAMState}
    (h : LoopFrame a s t) (k : LoopFrame b t u) : LoopFrame (a∪b) s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i (fun hb => hi (Finset.mem_union_right a hb))).trans
      (h.tapes i (fun ha => hi (Finset.mem_union_left b ha))),
    fun i hi h24 h25 h26 h27 h28 h29 => (k.registers i hi h24 h25 h26 h27 h28 h29).trans
      (h.registers i hi h24 h25 h26 h27 h28 h29)⟩

theorem LoopFrame.mono {a b : Finset ℕ} {s t : BitRAMState}
    (h : LoopFrame a s t) (hab : a ⊆ b) : LoopFrame b s t :=
  {h with tapes := fun i hi => h.tapes i (fun ha => hi (hab ha))}

theorem LoopFrame.ofCounted {count : ℕ} {s t : Store} (h : Counted.Frame count s t) :
    LoopFrame {count} s.val t.val :=
  ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by simpa using hi),
    fun i hi h24 h25 _ _ _ h29 => h.2.2.2.2.2.2 i hi h24 h25 h29⟩

private theorem carry_false (word : List Bool) : Increment.carryBits false word = word := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [Increment.carryBits,ih]

theorem increment_bits (n : ℕ) : Increment.bits n.bits = (n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit bit n hn ih =>
    rw [Nat.bits_append_bit n bit hn]
    cases bit
    · have hn0 : n ≠ 0 := by intro h; have := hn h; contradiction
      simp [Increment.bits,Increment.carryBits,carry_false,Nat.bit]
    · simp only [Increment.bits,Increment.carryBits,Bool.xor_true,Bool.not_true,Bool.true_and]
      rw [show Nat.bit true n+1 = 2*(n+1) by simp [Nat.bit]; omega,
        Nat.bit0_bits (n+1) (by omega)]
      exact congrArg (List.cons false) ih

def incrementCode (index : ℕ) : Code :=
  .seq (.call (Increment.program index)) (.call (Rewind.program index))

theorem increment (index n : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hw : Word s.val index n) :
    ∃ cost t, cost ≤ 12*n.bits.length+18 ∧ Executes input tape (incrementCode index) cost s t ∧
      Word t.val index (n+1) ∧ LoopFrame {index} s.val t.val := by
  obtain ⟨origin,ho⟩ := hw
  obtain ⟨c,u,hc,eu,pu,wu,fu⟩ := Increment.simulation index input tape n.bits origin s.val s.property ho
  let v := Store.ofState u
  have e1 : Executes input tape (.call (Increment.program index)) (c+1) s v :=
    .call _ _ _ _ eu (by rw [pu]; rfl)
  obtain ⟨er,wr⟩ := WordTransfer.rewind_shifted index origin input tape (Increment.bits n.bits) v.val v.property wu
  let t := Store.ofState (Rewind.finishAt index origin v.val)
  have e2 : Executes input tape (.call (Rewind.program index)) (4*(Increment.bits n.bits).length+6) v t :=
    .call _ _ _ _ er rfl
  have fr := WordTransfer.frame_rewind index index index (Or.inl rfl) origin v.val
  refine ⟨_,t,by have hl := Increment.bits_length_le n.bits; omega,e1.seq e2,
    ⟨origin,by simpa only [t,Store.ofState,increment_bits] using wr⟩,?_⟩
  refine ⟨fr.1.trans fu.1,fr.2.2.1.trans fu.2.2.1,fr.2.1.trans fu.2.1,
    fr.2.2.2.1.trans fu.2.2.2.1,fr.2.2.2.2.1.trans fu.2.2.2.2.1,?_,?_⟩
  · intro i hi
    have hi' : i ≠ index := by simpa using hi
    exact (fr.2.2.2.2.2.1 i hi' hi').trans (fu.2.2.2.2.2.1 i hi')
  · intro i _ h24 h25 h26 h27 h28 h29
    exact (fr.2.2.2.2.2.2 i h24 h25 h26 h27).trans (fu.2.2.2.2.2.2 i h26 h27 h28 h29)

end Maxwell.Cost.PhysicalEmit
