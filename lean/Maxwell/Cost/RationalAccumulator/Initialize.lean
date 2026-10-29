import Maxwell.Cost.RationalAccumulator.Reset
import Maxwell.Cost.RationalAccumulator.Push
import Maxwell.Cost.TakeParsed

namespace Maxwell.Cost.RationalAccumulator

open Structured

def ParseFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 12 → i ≠ 13 → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem ParseFrame.trans {s t u : BitRAMState} (h : ParseFrame s t) (k : ParseFrame t u) :
    ParseFrame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 h12 h13 hb => (kt i h4 h12 h13 hb).trans (ht i h4 h12 h13 hb),
    fun i h15 h24 h25 h26 h27 =>
      (kg i h15 h24 h25 h26 h27).trans (hg i h15 h24 h25 h26 h27)⟩

theorem parseFrame_of_frame {s t : BitRAMState} (h : Frame s t) : ParseFrame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 _ _ hb => ht i h4 hb, hg⟩

theorem take_bank (source target : ℕ) (hsource : source = 12 ∨ source = 13)
    (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (n : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) (hzero : v target = 0)
    (hword : s.val.tapes source = BitTape.atEnd n.bits) :
    ∃ t : Store, Executes input tape (TakeParsed.code source target) (21*n.bits.length+22) s t ∧
      Bank t.val (Function.update v target n) ∧ Scratch t.val 0 ∧
      t.val.tapes source = BitTape.blank ∧
      WordTransfer.Frame source target s.val t.val ∧ ParseFrame s.val t.val := by
  have htarget := hbank target ht ht'
  rw [hzero, zero_word_iff_blank] at htarget
  obtain ⟨origin, ho⟩ := htarget
  obtain ⟨t, he, hs, htape, hf⟩ := TakeParsed.steps source target (by omega) input tape n.bits origin s hword ho
  refine ⟨t, he, ?_, ?_, hs, hf, ?_⟩
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨origin, by simpa only [Function.update_self] using htape⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hf.2.2.2.2.2.1 i (by omega) hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      word_of_eq (hf.2.2.2.2.2.1 1 (by omega) (by omega)) hready.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩
  · rcases hf with ⟨ha, hi, hm, hr, ho, htapes, hg⟩
    exact ⟨ha, hi, hm, hr, ho, fun i h4 h12 h13 hb => htapes i (by omega) (by omega),
      fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

def initializeCode : Code :=
  .seq resetCode (.seq (.branch 23 (TakeParsed.code 12 31) (TakeParsed.code 12 30))
    (TakeParsed.code 13 32))

def initialized (v : ℕ → ℕ) (q : Codec.RationalPair) : ℕ → ℕ :=
  Function.update (Function.update (resetBank v) (selected (decide (q.numerator < 0)))
    q.numerator.natAbs) 32 q.denominator

theorem initialize_bank (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (q : Codec.RationalPair) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hsign : s.val.registers 23 = decide (q.numerator < 0)) :
    ∃ t : Store, Executes input tape initializeCode
      (6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length) +
        21*(q.numerator.natAbs.bits.length+q.denominator.bits.length)+57) s t ∧
      Bank t.val (initialized v q) ∧ Scratch t.val 0 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ ParseFrame s.val t.val := by
  obtain ⟨r, hr, hrb, hrr, hrf⟩ := reset input tape v s hbank hready
  have hrnum : r.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits :=
    (hrf.2.2.2.2.2.1 12 (by decide) (Or.inl (by decide))).trans hnum
  have hrden : r.val.tapes 13 = BitTape.atEnd q.denominator.bits :=
    (hrf.2.2.2.2.2.1 13 (by decide) (Or.inl (by decide))).trans hden
  have hrsign : r.val.registers 23 = decide (q.numerator < 0) :=
    (hrf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsign
  have hselected := selected_bounds (decide (q.numerator < 0))
  have hzero : resetBank v (selected (decide (q.numerator < 0))) = 0 := by
    cases decide (q.numerator < 0) <;> simp [selected, resetBank]
  obtain ⟨a, ha, hab, har, hanum, haf, haf'⟩ := take_bank 12
    (selected (decide (q.numerator < 0))) (Or.inl rfl) hselected.1 (by omega)
    input tape (resetBank v) q.numerator.natAbs r hrb hrr hzero hrnum
  have habranch : Executes input tape
      (.branch 23 (TakeParsed.code 12 31) (TakeParsed.code 12 30))
      (1 + (21*q.numerator.natAbs.bits.length+22)) r a := by
    cases he : decide (q.numerator < 0)
    · rw [he] at hrsign
      simpa only [he, selected, Bool.false_eq_true, ↓reduceIte] using Executes.no hrsign ha
    · rw [he] at hrsign
      simpa only [he, selected, ↓reduceIte] using Executes.yes hrsign ha
  have haden : a.val.tapes 13 = BitTape.atEnd q.denominator.bits :=
    (haf.2.2.2.2.2.1 13 (by decide) (by omega)).trans hrden
  let v1 := Function.update (resetBank v) (selected (decide (q.numerator < 0))) q.numerator.natAbs
  have hv132 : v1 32 = 0 := by
    simp [v1, Function.update_of_ne (show 32 ≠ selected (decide (q.numerator < 0)) by omega), resetBank]
  obtain ⟨t, ht, htb, htr, htden, htf, htf'⟩ := take_bank 13 32 (Or.inr rfl)
    (by decide) (by decide) input tape v1 q.denominator a hab har hv132 haden
  refine ⟨t, ?_, htb, htr, (htf.2.2.2.2.2.1 12 (by decide) (by decide)).trans hanum,
    htden, ((parseFrame_of_frame hrf).trans haf').trans htf'⟩
  have he := Executes.seq hr (Executes.seq habranch ht)
  have hcost : 6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length)+12 +
      (1+(21*q.numerator.natAbs.bits.length+22) + (21*q.denominator.bits.length+22)) =
      6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length) +
        21*(q.numerator.natAbs.bits.length+q.denominator.bits.length)+57 := by omega
  simpa only [hcost, initializeCode] using he

theorem initialized_numerator (v : ℕ → ℕ) (q : Codec.RationalPair) :
    (initialized v q 30 : ℤ) - initialized v q 31 = q.numerator := by
  cases hq : q.numerator with
  | ofNat n =>
    have hn : ¬(n : ℤ) < 0 := by omega
    simp [initialized, selected, resetBank, hq, hn]
  | negSucc n =>
    simp [initialized, selected, resetBank, hq]
    omega

@[simp] theorem initialized_denominator (v : ℕ → ℕ) (q : Codec.RationalPair) :
    initialized v q 32 = q.denominator := by simp [initialized]

theorem initialized_value (v : ℕ → ℕ) (q : Codec.RationalPair) :
    bankValue (initialized v q) = q.value := by
  unfold bankValue Codec.RationalPair.value
  rw [initialized_denominator]
  congr 1
  have hh := congrArg (fun z : ℤ => (z : ℚ)) (initialized_numerator v q)
  simpa using hh

end Maxwell.Cost.RationalAccumulator
