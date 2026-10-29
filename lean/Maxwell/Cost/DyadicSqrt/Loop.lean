import Maxwell.Cost.DyadicSqrt.Step

namespace Maxwell.Cost.DyadicSqrt

open Structured RationalAccumulator
open Maxwell.Defect.DyadicSqrt.Integer

def LoopFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (4 ≤ i ∧ i < 30 ∨ 37 ≤ i ∧ i ≠ 40) → t.tapes i = s.tapes i) ∧
  (∀ i, 36 ≤ i → t.registers i = s.registers i)

theorem LoopFrame.refl (s : BitRAMState) : LoopFrame s s := by simp [LoopFrame]

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) :
    LoopFrame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi => (kt i hi).trans (ht i hi), fun i hi => (kg i hi).trans (hg i hi)⟩

theorem LoopFrame.of_cycle {s t : BitRAMState} (h : Frame s t) : LoopFrame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi => ht i (by omega) (by omega),
    fun i hi => hg i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem LoopFrame.of_counter {s t : Store} (h : Counted.Frame 40 s t) : LoopFrame s.val t.val := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi => ht i (by omega),
    fun i hi => hg i (by omega) (by omega) (by omega) (by omega)⟩

def loopCode : Code := Counted.code 40 cycle

def loopBudget (A B p : ℕ) : ℕ :=
  (p + 1) * (13 * p.bits.length + 15) +
    p * cycleBudget (A.bits.length + B.bits.length + 2 * p + 1)

theorem counter_preserves_bank {s t : Store} (h : Counted.Frame 40 s t)
    (v : ℕ → ℕ) (hb : Bank s.val v) : Bank t.val v := by
  intro i hi hi'
  exact word_of_eq (h.2.2.2.2.2.1 i (by omega)) (hb i hi hi')

theorem counter_preserves_scratch {s t : Store} (h : Counted.Frame 40 s t)
    (hs : Scratch s.val 0) : Scratch t.val 0 := by
  exact ⟨blank_of_eq (h.2.2.2.2.2.1 0 (by decide)) hs.1,
    word_of_eq (h.2.2.2.2.2.1 1 (by decide)) hs.2.1,
    blank_of_eq (h.2.2.2.2.2.1 2 (by decide)) hs.2.2.1,
    blank_of_eq (h.2.2.2.2.2.1 3 (by decide)) hs.2.2.2⟩

/-- One fixed compiled loop performs exactly the requested number of
bisections, reading the binary precision counter from tape 40. -/
theorem loop_executes (input : List Bool) (tape : ℕ → Bool) (A B p : ℕ)
    (origin : ℤ) (s : Store)
    (hbank : Bank s.val (bank A B 0 1)) (hready : Scratch s.val 0)
    (hcounter : s.val.tapes 40 = BitTape.shifted p.bits origin) :
    ∃ cost, ∃ t : Store, ∃ counter,
      cost ≤ loopBudget A B p ∧ Executes input tape loopCode cost s t ∧
      Bank t.val (bank (A * 4^p) B (lowerNum A B p) (2^p)) ∧
      Scratch t.val 0 ∧ t.val.tapes 40 = BitTape.shifted counter origin ∧
      counter.length = p.bits.length ∧ LoopFrame s.val t.val := by
  let W := A.bits.length + B.bits.length + 2 * p + 1
  let invariant (n : ℕ) (t : Store) : Prop := n ≤ p ∧
    Bank t.val (bank (A * 4^(p-n)) B (lowerNum A B (p-n)) (2^(p-n))) ∧
    Scratch t.val 0 ∧ LoopFrame s.val t.val
  have stable : ∀ n a b, Counted.Frame 40 a b → invariant n a → invariant n b := by
    intro n a b hf hi
    exact ⟨hi.1, counter_preserves_bank hf _ hi.2.1,
      counter_preserves_scratch hf hi.2.2.1, hi.2.2.2.trans (LoopFrame.of_counter hf)⟩
  have body : ∀ n xs a, invariant (n + 1) a →
      a.val.tapes 40 = BitTape.shifted xs origin → addressValue xs = n →
      ∃ cost t, Executes input tape cycle cost a t ∧ invariant n t ∧
        t.val.tapes 40 = BitTape.shifted xs origin ∧ cost ≤ cycleBudget W := by
    intro n xs a hi hword _
    let k := p - (n + 1)
    have hk : k + 1 = p - n := by dsimp [k]; omega
    have hkBound : k ≤ p := by dsimp [k]; omega
    have hA : (A * 4^k).bits.length ≤ W :=
      (scaledNumerator_bits_length_le A k).trans (by dsimp [W]; omega)
    have hB : B.bits.length ≤ W := by dsimp [W]; omega
    have hL : (lowerNum A B k).bits.length ≤ W :=
      (lowerNum_bits_length_le A B k).trans (by dsimp [W]; omega)
    have hP : (2^k).bits.length ≤ W := by
      have hp : (2^k : ℕ).bits.length ≤ k + 1 := by
        rw [Nat.size_eq_bits_len]
        apply Nat.size_le.mpr
        rw [pow_succ]
        have hh : 0 < (2:ℕ)^k := by positivity
        omega
      exact hp.trans (by dsimp [W]; omega)
    obtain ⟨cost, t, hc, he, hb, hr, hf⟩ := cycle_executes input tape (A * 4^k) B
      (lowerNum A B k) (2^k) W hA hB hL hP (by dsimp [W]; omega) a hi.2.1 hi.2.2.1
    have hscaled : 4 * (A * 4^k) = A * 4^(k+1) := by rw [pow_succ]; ring
    have hlower : nextLower (A * 4^k) B (lowerNum A B k) = lowerNum A B (k+1) := by
      simp only [nextLower, lowerNum, hscaled]
    have hp : 2 * 2^k = (2:ℕ)^(k+1) := by rw [pow_succ]; omega
    rw [hscaled, hlower, hp, hk] at hb
    exact ⟨cost, t, he, ⟨by omega, hb, hr, hi.2.2.2.trans (LoopFrame.of_cycle hf)⟩,
      (hf.2.2.2.2.2.1 40 (by decide) (by decide)).trans hword, hc⟩
  obtain ⟨cost, t, counter, he, hi, hw, hl, _, hc⟩ := CountedShifted.executes 40 origin cycle
    input tape invariant (fun _ => cycleBudget W) stable body p p.bits s (address_bits p) hcounter
    ⟨le_rfl, by simpa [lowerNum] using hbank, hready, LoopFrame.refl s.val⟩
  refine ⟨cost, t, counter, ?_, he, ?_, hi.2.2.1, hw, hl, hi.2.2.2⟩
  · simpa [loopBudget, W] using hc
  · simpa using hi.2.1

theorem loop_run (input : List Bool) (tape : ℕ → Bool) (A B p : ℕ)
    (origin : ℤ) (s : Store)
    (hbank : Bank s.val (bank A B 0 1)) (hready : Scratch s.val 0)
    (hcounter : s.val.tapes 40 = BitTape.shifted p.bits origin) :
    ∃ t : Store,
      (runPriced (loopCode.compile.next input tape) (loopBudget A B p + 1) s.val).finished =
        some (t.place loopCode.size) ∧
      (runPriced (loopCode.compile.next input tape) (loopBudget A B p + 1) s.val).instructions ≤
        loopBudget A B p ∧
      Bank t.val (bank (A * 4^p) B (lowerNum A B p) (2^p)) ∧
      Scratch t.val 0 ∧ LoopFrame s.val t.val := by
  obtain ⟨cost, t, _, hc, he, hb, hr, _, _, hf⟩ :=
    loop_executes input tape A B p origin s hbank hready hcounter
  have run := he.compiled_run (loopBudget A B p + 1) (by omega)
  exact ⟨t, run.1, run.2 ▸ hc, hb, hr, hf⟩

end Maxwell.Cost.DyadicSqrt
