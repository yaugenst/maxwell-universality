import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.WordTransfer
import Maxwell.Cost.CanonicalBits

namespace Maxwell.Cost.PowerOfTwo
open Structured

/-- Three literal primitive instructions, each with its charged return. -/
def appendBit (target : ℕ) (b : Bool) : Code :=
  .seq (Code.atom (.literal 28 b))
    (.seq (Code.atom (.writeTape target 28)) (Code.atom (.tapeRight target)))

def appendState (target : ℕ) (b : Bool) (s : Store) : Store :=
  Store.ofState {s.val with
    registers := Function.update s.val.registers 28 b
    tapes := Function.update s.val.tapes target
      {(s.val.tapes target).write (some b) with head := (s.val.tapes target).head + 1}}

theorem append_executes (target : ℕ) (b : Bool) (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) : Executes input randomTape (appendBit target b) 6 s (appendState target b s) := by
  have hl := Executes.literal input randomTape s 28 b
  let s1 := Store.ofState (s.val.setRegister 28 b)
  have hw := Executes.writeTape input randomTape s1 target 28
  let s2 := Store.ofState (s1.val.setTape target ((s1.val.tapes target).write (some (s1.val.registers 28))))
  have hr := Executes.tapeRight input randomTape s2 target
  convert hl.seq (hw.seq hr) using 1 <;>
    simp [appendBit, appendState, s1, s2, Store.ofState, BitRAMState.setRegister,
      BitRAMState.setTape, BitTape.write]

theorem append_word (target : ℕ) (b : Bool) (s : Store) (word : List Bool) (origin : ℤ)
    (h : s.val.tapes target = BitTape.shiftedEnd word origin) :
    (appendState target b s).val.tapes target = BitTape.shiftedEnd (word ++ [b]) origin := by
  simpa [appendState, Store.ofState, h] using BitTape.shiftedEnd_append_write word origin b

def Frame (counter target : ℕ) (s t : Store) : Prop :=
  t.val.address = s.val.address ∧ t.val.inputHead = s.val.inputHead ∧ t.val.memory = s.val.memory ∧
  t.val.randomCursor = s.val.randomCursor ∧ t.val.output = s.val.output ∧
  (∀ i, i ≠ counter → i ≠ target → t.val.tapes i = s.val.tapes i) ∧
  (∀ i, 4 < i → i ≠ 24 → i ≠ 25 → i ≠ 28 → i ≠ 29 → t.val.registers i = s.val.registers i)

theorem Frame.refl (counter target : ℕ) (s : Store) : Frame counter target s s := by simp [Frame]

theorem Frame.trans {counter target : ℕ} {s t u : Store}
    (h : Frame counter target s t) (k : Frame counter target t u) : Frame counter target s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hc ht' => (kt i hc ht').trans (ht i hc ht'),
    fun i h4 h24 h25 h28 h29 => (kg i h4 h24 h25 h28 h29).trans (hg i h4 h24 h25 h28 h29)⟩

theorem frame_of_test {counter target : ℕ} {s t : Store}
    (h : Counted.Frame counter s t) : Frame counter target s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hc _ => ht i hc,
    fun i h4 h24 h25 _ h29 => hg i h4 h24 h25 h29⟩

theorem append_frame (counter target : ℕ) (b : Bool) (s : Store) :
    Frame counter target s (appendState target b s) := by
  simp [Frame, appendState, Store.ofState]
  constructor <;> intros <;> simp_all

def core (counter target : ℕ) : Code :=
  .seq (Counted.code counter (appendBit target false)) (appendBit target true)

theorem power_bits (n : ℕ) : (2 ^ n).bits = List.replicate n false ++ [true] := by
  apply Eq.symm
  have hcanonical : TapeOps.CanonicalBits (List.replicate n false ++ [true]) := Or.inr ⟨_, rfl⟩
  have hval : addressValue (List.replicate n false ++ [true]) = 2 ^ n := by
    clear hcanonical
    induction n with
    | zero => simp [addressValue]
    | succ n ih => simp [List.replicate_succ, addressValue, ih, pow_succ, Nat.mul_comm]
  rw [← TapeOps.canonicalBits_bits hcanonical, hval]

/-- A binary counter drives a unary output loop. The exponent is read from
its actual tape, so producing 2^n requires n explicitly charged zero writes. -/
theorem core_executes (counter target : ℕ) (hne : counter ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (exponent : List Bool)
    (counterOrigin targetOrigin : ℤ) (s : Store)
    (hc : s.val.tapes counter = BitTape.shifted exponent counterOrigin)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ cost t finalCounter, Executes input randomTape (core counter target) cost s t ∧
      cost ≤ (addressValue exponent + 1) * (13 * exponent.length + 21) ∧
      t.val.tapes counter = BitTape.shifted finalCounter counterOrigin ∧
      finalCounter.length = exponent.length ∧
      t.val.tapes target = BitTape.shiftedEnd (2 ^ addressValue exponent).bits targetOrigin ∧
      Frame counter target s t := by
  let N := addressValue exponent
  let invariant (n : ℕ) (t : Store) : Prop := n ≤ N ∧
    t.val.tapes target = BitTape.shiftedEnd (List.replicate (N - n) false) targetOrigin ∧
    Frame counter target s t
  have hstable : ∀ n a b, Counted.Frame counter a b → invariant n a → invariant n b := by
    intro n a b hf hi
    refine ⟨hi.1, (hf.2.2.2.2.2.1 target (Ne.symm hne)).trans hi.2.1,
      hi.2.2.trans (frame_of_test hf)⟩
  have hbody : ∀ n xs a, invariant (n + 1) a →
      a.val.tapes counter = BitTape.shifted xs counterOrigin → addressValue xs = n →
      ∃ c b, Executes input randomTape (appendBit target false) c a b ∧ invariant n b ∧
        b.val.tapes counter = BitTape.shifted xs counterOrigin ∧ c ≤ 6 := by
    intro n xs a hi hcounter _
    refine ⟨6, appendState target false a, append_executes target false input randomTape a,
      ⟨by omega, ?_, hi.2.2.trans (append_frame counter target false a)⟩, ?_, le_rfl⟩
    · rw [append_word target false a _ targetOrigin hi.2.1]
      have hn : N - n = (N - (n + 1)) + 1 := by omega
      rw [hn, List.replicate_add]
      rfl
    · simpa [appendState, Store.ofState, hne] using hcounter
  obtain ⟨cost, t, finalCounter, he, hi, hw, hl, _, hb⟩ :=
    CountedShifted.executes counter counterOrigin (appendBit target false) input randomTape
      invariant (fun _ => 6) hstable hbody N exponent s rfl hc
      ⟨le_rfl, by simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using ht,
        Frame.refl counter target s⟩
  refine ⟨cost + 6, appendState target true t, finalCounter,
    he.seq (append_executes target true input randomTape t), ?_, ?_, hl, ?_,
    hi.2.2.trans (append_frame counter target true t)⟩
  · simp at hb
    nlinarith
  · simpa [appendState, Store.ofState, hne] using hw
  · rw [append_word target true t _ targetOrigin hi.2.1, power_bits]
    simp [N]

/-- Full generator preserves its exponent word and clears its private counter. -/
def code (source counter target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source counter))
    (.seq (core counter target) (.call (TapeOps.clear counter)))

def BankFrame (counter target : ℕ) (s t : Store) : Prop :=
  t.val.address = s.val.address ∧ t.val.inputHead = s.val.inputHead ∧ t.val.memory = s.val.memory ∧
  t.val.randomCursor = s.val.randomCursor ∧ t.val.output = s.val.output ∧
  (∀ i, i ≠ counter → i ≠ target → t.val.tapes i = s.val.tapes i) ∧
  (∀ i, 4 < i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.val.registers i = s.val.registers i)

theorem BankFrame.trans {counter target : ℕ} {s t u : Store}
    (h : BankFrame counter target s t) (k : BankFrame counter target t u) :
    BankFrame counter target s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hc ht' => (kt i hc ht').trans (ht i hc ht'),
    fun i h4 h24 h25 h26 h27 h28 h29 =>
      (kg i h4 h24 h25 h26 h27 h28 h29).trans (hg i h4 h24 h25 h26 h27 h28 h29)⟩

theorem executes (source counter target : ℕ)
    (hsc : source ≠ counter) (hst : source ≠ target) (hct : counter ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (exponent : List Bool)
    (sourceOrigin counterOrigin targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted exponent sourceOrigin)
    (hc : s.val.tapes counter = {BitTape.blank with head := counterOrigin})
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ cost t, Executes input randomTape (code source counter target) cost s t ∧
      cost ≤ (addressValue exponent + 1) * (13 * exponent.length + 21) + 21 * exponent.length + 21 ∧
      t.val.tapes source = BitTape.shifted exponent sourceOrigin ∧
      t.val.tapes counter = {BitTape.blank with head := counterOrigin + exponent.length} ∧
      t.val.tapes target = BitTape.shiftedEnd (2 ^ addressValue exponent).bits targetOrigin ∧
      BankFrame counter target s t := by
  obtain ⟨cloned, hclone, hp, hsource, hcounter, hcf⟩ := WordTransfer.clone_steps
    source counter hsc input randomTape exponent sourceOrigin counterOrigin s.val s.property hs hc
  let c := Store.ofState cloned
  have ec : Executes input randomTape (.call (WordTransfer.clone source counter))
      (15 * exponent.length + 17) s c := by
    simpa using Executes.call _ s cloned _ hclone (by rw [hp]; rfl)
  have cf : BankFrame counter target s c := by
    rcases hcf with ⟨ha, hi, hm, hr, ho, htapes, hregs⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
    · intro i hcounter' _
      by_cases hi : i = source
      · subst i; exact hsource.trans hs.symm
      · exact htapes i hi hcounter'
    · intro i _ h24 h25 h26 h27 _ _
      exact hregs i h24 h25 h26 h27
  have hctarget : c.val.tapes target = {BitTape.blank with head := targetOrigin} :=
    (hcf.2.2.2.2.2.1 target (Ne.symm hst) (Ne.symm hct)).trans ht
  obtain ⟨coreCost, middle, finalCounter, em, hbound, hmCounter, hmLength, hmTarget, hmf⟩ :=
    core_executes counter target hct input randomTape exponent counterOrigin targetOrigin c hcounter hctarget
  have mf : BankFrame counter target c middle := by
    rcases hmf with ⟨ha, hi, hm, hr, ho, htapes, hregs⟩
    exact ⟨ha, hi, hm, hr, ho, htapes, fun i h4 h24 h25 _ _ h28 h29 => hregs i h4 h24 h25 h28 h29⟩
  obtain ⟨cleared, hclear, hcp, hblank, hclearFrame⟩ := TapeOps.clear_steps
    counter input randomTape finalCounter counterOrigin middle.val middle.property hmCounter
  let finish := Store.ofState cleared
  have ef : Executes input randomTape (.call (TapeOps.clear counter))
      (6 * finalCounter.length + 4) middle finish := by
    simpa using Executes.call _ middle cleared _ hclear (by rw [hcp]; rfl)
  have ff : BankFrame counter target middle finish := by
    rcases hclearFrame with ⟨ha, hi, hm, hr, ho, htapes, hregs⟩
    exact ⟨ha, hi, hm, hr, ho, fun i hc _ => htapes i hc hc,
      fun i _ _ _ h26 h27 _ _ => hregs i h26 h27⟩
  have frame := (cf.trans mf).trans ff
  refine ⟨_, finish, ec.seq (em.seq ef), ?_,
    (frame.2.2.2.2.2.1 source hsc hst).trans hs, ?_, ?_, frame⟩
  · rw [hmLength]
    omega
  · simpa [finish, Store.ofState, hmLength] using hblank
  · exact (hclearFrame.2.2.2.2.2.1 target (Ne.symm hct) (Ne.symm hct)).trans hmTarget

end Maxwell.Cost.PowerOfTwo
