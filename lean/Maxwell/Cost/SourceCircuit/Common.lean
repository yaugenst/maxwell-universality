import Maxwell.Cost.SourceCircuit.Archive
import Maxwell.Cost.BankArray.Increment

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

/-- Persistent data and the coefficient sign survive allocation. Address
workspace and scratch registers are deliberately outside this frame. -/
structure Frame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, (j = 4 ∨ 10 ≤ j) → j ∉ changed → t.tapes j = s.tapes j
  sign : t.registers 23 = s.registers 23
  control : ∀ j, 30 ≤ j → t.registers j = s.registers j

theorem Frame.trans {changed : Finset ℕ} {s t u : BitRAMState}
    (h : Frame changed s t) (k : Frame changed t u) : Frame changed s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun j hj hc => (k.tapes j hj hc).trans (h.tapes j hj hc),k.sign.trans h.sign,
    fun j hj => (k.control j hj).trans (h.control j hj)⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState} (h : Frame a s t)
    (hab : a ⊆ b) : Frame b s t :=
  ⟨h.inputHead,h.randomCursor,h.output,
    fun j hj hh => h.tapes j hj (fun ha => hh (hab ha)),h.sign,h.control⟩

theorem frame_bank {s t : BitRAMState} (h : BankArray.Frame s t) : Frame ∅ s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun j hj _ => h.2.2.2.1 j hj,
    h.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    fun j hj => h.2.2.2.2 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_except {bank : ℕ} {s t : BitRAMState} (h : BankArray.FrameExcept bank s t) :
    Frame {bank} s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun j hj hn => h.2.2.2.1 j hj (by simpa using hn),
    h.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    fun j hj => h.2.2.2.2 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_transfer {source target : ℕ} {s t : BitRAMState} {changed : Finset ℕ}
    (h : WordTransfer.Frame source target s t)
    (ht : ∀ j ∉ changed, t.tapes j = s.tapes j) : Frame changed s t :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,fun j _ hj => ht j hj,
    h.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega),
    fun j hj => h.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)⟩

theorem scratch_of_tapes {s t : BitRAMState} (h : BankArray.Scratch s)
    (ht : ∀ j, j < 10 → t.tapes j = s.tapes j) : BankArray.Scratch t := by
  rcases h with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  exact ⟨RationalAccumulator.blank_of_eq (ht 0 (by omega)) h0,
    RationalAccumulator.blank_of_eq (ht 1 (by omega)) h1,
    RationalAccumulator.blank_of_eq (ht 2 (by omega)) h2,
    RationalAccumulator.blank_of_eq (ht 3 (by omega)) h3,
    RationalAccumulator.blank_of_eq (ht 5 (by omega)) h5,
    RationalAccumulator.blank_of_eq (ht 6 (by omega)) h6,
    RationalAccumulator.blank_of_eq (ht 8 (by omega)) h8,
    RationalAccumulator.blank_of_eq (ht 9 (by omega)) h9⟩

/-- Carry propagation does not lengthen a padded identifier when its
increment still fits the allocated width. -/
theorem carry_length (carry : Bool) (bits : List Bool)
    (h : addressValue bits + carry.toNat < 2 ^ bits.length) :
    (Increment.carryBits carry bits).length = bits.length := by
  induction bits generalizing carry with
  | nil => cases carry <;> simp_all [Increment.carryBits]
  | cons b bits ih =>
    simp only [Increment.carryBits, List.length_cons]
    congr 1
    apply ih
    simp only [addressValue, List.length_cons, pow_succ] at h
    cases b <;> cases carry <;> simp_all <;> omega

theorem increment_length (bits : List Bool)
    (h : addressValue bits + 1 < 2 ^ bits.length) :
    (Increment.bits bits).length = bits.length := by
  simpa [Increment.bits] using carry_length true bits (by simpa using h)

/-- Three-bit instruction tags leave room for zero, half, negation, copy,
and addition without using a value-dependent program. -/
def copyTag : List Bool := [false, true, true]

def copiesCode : Code :=
  .seq (gateCode 94 97 copyTag) (gateCode 94 97 copyTag)

theorem copies_executes (input : List Bool) (randomTape : ℕ → Bool)
    (word preceding : List Bool) (s : Store)
    (hp : BankArray.Word s.val 94 word)
    (ha : s.val.tapes 97 = BitTape.atEnd preceding) :
    ∃ t, Executes input randomTape copiesCode (22 * word.length + 58) s t ∧
      t.val.tapes = Function.update s.val.tapes 97
        (BitTape.atEnd (preceding ++ copyTag ++ word ++ copyTag ++ word)) ∧
      t.val.memory = s.val.memory ∧ Frame {97} s.val t.val := by
  obtain ⟨origin,hp⟩ := hp
  obtain ⟨a,ea,ha',af⟩ := gate_executes 94 97 (by omega) input randomTape copyTag word preceding
    origin s hp ha
  obtain ⟨t,et,ht,tf⟩ := gate_executes 94 97 (by omega) input randomTape copyTag word
    (preceding ++ copyTag ++ word) origin a (by simpa [ha'] using hp) (by simp [ha'])
  have tapes : t.val.tapes = Function.update s.val.tapes 97
      (BitTape.atEnd (preceding ++ copyTag ++ word ++ copyTag ++ word)) := by simp [ht,ha']
  refine ⟨t,?_,tapes,tf.2.2.1.trans af.2.2.1,frame_transfer (af.trans tf) ?_⟩
  · convert ea.seq et using 1 <;> first | rfl | simp [copyTag]; omega
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [tapes,hj]

end Maxwell.Cost.SourceCircuit
