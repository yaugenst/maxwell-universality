import Maxwell.Cost.CalibrationMatrix.Product
import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.CalibrationMatrix.NatPower
open Structured RationalAccumulator
set_option maxHeartbeats 900000

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → i ≠ 141 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, k.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i hi hj hk => (k.2.2.2.2.2.1 i hi hj hk).trans (h.2.2.2.2.2.1 i hi hj hk),
    fun i hi a b c d e f => (k.2.2.2.2.2.2 i hi a b c d e f).trans (h.2.2.2.2.2.2 i hi a b c d e f)⟩

theorem Frame.of_counter {s t : Store} (h : CountedShifted.Frame 141 s t) : Frame s.val t.val :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i _ _ hi => h.2.2.2.2.2.1 i hi,
    fun i hi h24 h25 _ _ _ h29 => h.2.2.2.2.2.2 i (by omega) h24 h25 h29⟩

theorem Frame.of_product {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi hj _ => h.2.2.2.2.2.1 i hi hj,
    fun i hi h24 h25 h26 h27 _ _ => h.2.2.2.2.2.2 i hi h24 h25 h26 h27⟩

def values (v : ℕ → ℕ) (base k : ℕ) : ℕ → ℕ := Function.update v 36 (base^k*v 36)

@[simp] theorem values_zero (v : ℕ → ℕ) (base : ℕ) : values v base 0 = v := by simp [values]

def Invariant (v : ℕ → ℕ) (base N : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ N ∧ Bank s.val (values v base (N-remaining)) ∧ Scratch s.val base ∧ Frame initial s.val

theorem invariant_stable (v : ℕ → ℕ) (base N : ℕ) (initial : BitRAMState)
    (remaining : ℕ) (s t : Store) (hf : CountedShifted.Frame 141 s t)
    (hs : Invariant v base N initial remaining s) : Invariant v base N initial remaining t := by
  have keep := hf.2.2.2.2.2.1
  exact ⟨hs.1,
    fun i hi hi' => word_of_eq (keep i (by omega)) (hs.2.1 i hi hi'),
    ⟨blank_of_eq (keep 0 (by omega)) hs.2.2.1.1,
      word_of_eq (keep 1 (by omega)) hs.2.2.1.2.1,
      blank_of_eq (keep 2 (by omega)) hs.2.2.1.2.2.1,
      blank_of_eq (keep 3 (by omega)) hs.2.2.1.2.2.2⟩,
    hs.2.2.2.trans (Frame.of_counter hf)⟩

def code : Code := .seq (CountedShifted.code 141 (productCode 36)) (.call (TapeOps.clear 141))

def costCap (N B : ℕ) : ℕ := (N+1)*(13*B+15)+N*(1000*(2*B+3)^2)+6*B+4

/-- An actual counted product constructs the unreduced denominator power;
the base remains canonical on tape1 and the accumulator on tape36. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (base N B : ℕ)
    (hb : base.bits.length ≤ B) (hfit : ∀ k, k ≤ N → (base^k*v 36).bits.length ≤ B)
    (count : List Bool) (hc : addressValue count = N) (hcl : count.length ≤ B)
    (origin : ℤ) (s : Store) (hcounter : s.val.tapes 141 = BitTape.shifted count origin)
    (hbank : Bank s.val v) (hscratch : Scratch s.val base) :
    ∃ cost, ∃ t : Store, cost ≤ costCap N B ∧ Executes input tape code cost s t ∧
      Bank t.val (values v base N) ∧ Scratch t.val base ∧ Blank t.val 141 ∧ Frame s.val t.val := by
  let inv := Invariant v base N s.val
  have stable : ∀ r a b, CountedShifted.Frame 141 a b → inv r a → inv r b :=
    invariant_stable v base N s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 141 = BitTape.shifted xs origin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape (productCode 36) bodyCost u t ∧ inv r t ∧
        t.val.tapes 141 = BitTape.shifted xs origin ∧ bodyCost ≤ 1000*(2*B+3)^2 := by
    intro r xs u hu hcounter _
    obtain ⟨hr, hbank, hs, hf⟩ := hu
    obtain ⟨cost, t, hcost, he, htbank, hts, htf⟩ := product 36 (by omega) (by omega)
      input tape (values v base (N-(r+1))) base u hbank hs
    have hn : N-r = N-(r+1)+1 := by omega
    have hv : Function.update (values v base (N-(r+1))) 36
        (base * values v base (N-(r+1)) 36) = values v base (N-r) := by
      rw [hn]
      simp [values, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
    refine ⟨cost, t, he, ⟨by omega, hv ▸ htbank, hts, hf.trans (Frame.of_product htf)⟩,
      (htf.2.2.2.2.2.1 141 (by omega) (Or.inr (by omega))).trans hcounter, ?_⟩
    have hvlen : (values v base (N-(r+1)) 36).bits.length ≤ B := by
      simpa [values] using hfit (N-(r+1)) (by omega)
    exact hcost.trans (by gcongr; omega)
  have hi : inv N s := by exact ⟨le_rfl, by simpa [inv] using hbank, hscratch, Frame.refl s.val⟩
  obtain ⟨cost, a, finalCount, he, haInv, haCount, haLen, _, haCost⟩ :=
    CountedShifted.executes 141 origin (productCode 36) input tape inv (fun _ => 1000*(2*B+3)^2)
      stable bodyCorrect N count s hc hcounter hi
  obtain ⟨_, hab, has, haf⟩ := haInv
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 141 input tape finalCount origin a haCount
  have keep (i : ℕ) (hi : i ≠ 141) : t.val.tapes i = a.val.tapes i := by simp [ht, hi]
  have frame : Frame a.val t.val :=
    ⟨ft.1, ft.2.1, ft.2.2.1, ft.2.2.2.1, ft.2.2.2.2.1, fun i _ _ hi => keep i hi,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨cost+(6*finalCount.length+4), t, ?_, he.seq et, ?_,
    ⟨blank_of_eq (keep 0 (by omega)) has.1, word_of_eq (keep 1 (by omega)) has.2.1,
      blank_of_eq (keep 2 (by omega)) has.2.2.1, blank_of_eq (keep 3 (by omega)) has.2.2.2⟩,
    ⟨origin+finalCount.length, by simp [ht]⟩, haf.trans frame⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at haCost
    have hlen := haLen.trans_le hcl
    have hcounter : (N+1)*(13*count.length+15) ≤ (N+1)*(13*B+15) := by gcongr
    dsimp [costCap]
    omega
  · intro i hi hi'
    exact word_of_eq (keep i (by omega)) (by simpa using hab i hi hi')

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (base N B : ℕ)
    (hb : base.bits.length ≤ B) (hfit : ∀ k, k ≤ N → (base^k*v 36).bits.length ≤ B)
    (count : List Bool) (hc : addressValue count = N) (hcl : count.length ≤ B)
    (origin : ℤ) (s : Store) (hcounter : s.val.tapes 141 = BitTape.shifted count origin)
    (hbank : Bank s.val v) (hscratch : Scratch s.val base) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap N B+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap N B+1) s.val).instructions ≤ costCap N B ∧
      Bank t.val (values v base N) ∧ Scratch t.val base ∧ Blank t.val 141 ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hcost, he, ht⟩ := executes input tape v base N B hb hfit count hc hcl origin s hcounter hbank hscratch
  have hr := he.compiled_run (costCap N B+1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hcost, ht⟩

end Maxwell.Cost.CalibrationMatrix.NatPower
