import Maxwell.Cost.RoutingPorts.Complete.Data
import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.BankArray.Compare
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.PhysicalEmit.Increment
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
open RationalAccumulator (Blank)

structure Layout (n : ℕ) where
  forward : ℕ
  backward : ℕ
  clock : List Bool
  positive : 0 < n
  clock_length : clock.length=n.bits.length
  separated : IncidenceEncoding.Separated forward (n*n.bits.length) backward (n*n.bits.length)

def encode {n : ℕ} (values : Vector ℕ n) : Vector (List Bool) n :=
  values.map (fun v => FixedWidth.bits n.bits.length v.bits)

theorem encode_get {n : ℕ} (values : Vector ℕ n) (i : Fin n) :
    (encode values).get i=FixedWidth.bits n.bits.length (values.get i).bits := by
  simp [encode,Vector.get,Fin.cast]

theorem encode_value {n : ℕ} (values : Vector ℕ n) (i : Fin n)
    (hi : values.get i ≤ n) : addressValue ((encode values).get i)=values.get i := by
  rw [encode_get,FixedWidth.bits_value]
  · exact addressValue_bits _
  · simpa only [addressValue_bits,Nat.size_eq_bits_len] using hi.trans_lt (Nat.lt_size_self n)

theorem encode_set {n : ℕ} (values : Vector ℕ n) (i : Fin n) (v : ℕ) :
    encode (values.set i v)=(encode values).set i (FixedWidth.bits n.bits.length v.bits) := by
  apply Vector.ext
  intro j hj
  let k : Fin n := ⟨j,hj⟩
  change (encode (values.set i v)).get k=((encode values).set i (FixedWidth.bits n.bits.length v.bits)).get k
  rw [encode_get,DummyFill.get_set,DummyFill.get_set,encode_get]
  split <;> rfl

structure Ready (s : BitRAMState) : Prop where
  scratch : BankArray.Scratch s
  seven : Blank s 7
  pack : Blank s 37
  probe : Blank s 752

structure Metadata {n : ℕ} (l : Layout n) (s : BitRAMState) : Prop where
  count : RationalAccumulator.Word s 709 n
  width : RationalAccumulator.Word s 711 n.bits.length
  forward : RationalAccumulator.Word s 716 l.forward
  backward : RationalAccumulator.Word s 717 l.backward
  clock : BankArray.Word s 718 l.clock

structure Stored {n : ℕ} (l : Layout n) (forward backward : Vector ℕ n) (s : BitRAMState) : Prop where
  forward : BitArray.Represents s.memory l.forward n.bits.length (encode forward)
  backward : BitArray.Represents s.memory l.backward n.bits.length (encode backward)

structure Frame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ i, (i=4 ∨ 10 ≤ i) → i ∉ work → t.tapes i=s.tapes i
  registers : ∀ i, 15 ≤ i → i≠24 → i≠25 → i≠26 → i≠27 → i≠28 → i≠29 →
    t.registers i=s.registers i

theorem Frame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : Frame work s t) (k : Frame work t u) : Frame work s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hw => (k.tapes i hi hw).trans (h.tapes i hi hw),
    fun i hi h24 h25 h26 h27 h28 h29 => (k.registers i hi h24 h25 h26 h27 h28 h29).trans
      (h.registers i hi h24 h25 h26 h27 h28 h29)⟩

theorem Frame.mono {work larger : Finset ℕ} {s t : BitRAMState}
    (h : Frame work s t) (hle : work ⊆ larger) : Frame larger s t :=
  {h with tapes := fun i hi hn => h.tapes i hi (fun hh => hn (hle hh))}

theorem Frame.of_bank {work : Finset ℕ} {s t : BitRAMState} (h : BankArray.Frame s t) :
    Frame work s t := ⟨h.1,h.2.1,h.2.2.1,fun i hi _ => h.2.2.2.1 i hi,h.2.2.2.2⟩

theorem Frame.of_bankExcept {bank : ℕ} {s t : BitRAMState} (h : BankArray.FrameExcept bank s t) :
    Frame {bank} s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hn => h.2.2.2.1 i hi (by simpa using hn),h.2.2.2.2⟩

theorem Metadata.frame {n : ℕ} {l : Layout n} {s t : BitRAMState}
    (h : Metadata l s) {work : Finset ℕ} (hf : Frame work s t)
    (hwork : ∀ i∈work,730 ≤ i ∨ i=37) : Metadata l t := by
  have keep (i : ℕ) (hi : 700 ≤ i) (hil : i < 730) : t.tapes i=s.tapes i :=
    hf.tapes i (Or.inr (by omega)) (by intro hh;have := hwork i hh;omega)
  exact ⟨RationalAccumulator.word_of_eq (keep 709 (by decide) (by decide)) h.count,
    RationalAccumulator.word_of_eq (keep 711 (by decide) (by decide)) h.width,
    RationalAccumulator.word_of_eq (keep 716 (by decide) (by decide)) h.forward,
    RationalAccumulator.word_of_eq (keep 717 (by decide) (by decide)) h.backward,
    BankArray.word_of_eq (keep 718 (by decide) (by decide)) h.clock⟩

/-- Quadratic bit work per access; the full cursor pass charges only
linearly many accesses and increments. -/
def scale {n : ℕ} (l : Layout n) : ℕ := n.bits.length+l.forward.bits.length+l.backward.bits.length+6

def operationCap {n : ℕ} (l : Layout n) : ℕ := 10000*(scale l)^2

end Maxwell.Cost.RoutingPorts.Complete
