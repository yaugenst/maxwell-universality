import Maxwell.Cost.MagnitudeMax.Body
import Maxwell.Cost.Structured.Counted

namespace Maxwell.Cost.MagnitudeMax.Loop

open Structured RationalAccumulator

def code : Code := Counted.code 14 Body.code

def records (qs : List ℚ) : List Bool := qs.flatMap Codec.rat

def price (counterBits : List Bool) (qs : List ℚ) (B : ℕ) : ℕ :=
  (qs.length + 1) * (13 * counterBits.length + 15) + qs.length * (11000 * (B + 2)^2)

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 14 → i ≠ 20 → (i < 30 ∨ 36 < i) →
    t.tapes i = s.tapes i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.1.trans h.2.2.2.1,
    fun i h4 h10 h12 h13 h14 h20 hb =>
      (k.2.2.2.2 i h4 h10 h12 h13 h14 h20 hb).trans
        (h.2.2.2.2 i h4 h10 h12 h13 h14 h20 hb)⟩

theorem frame_counter {s t : Store} (h : Counted.Frame 14 s t) : Frame s.val t.val :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i _ _ _ _ h14 _ _ => h.2.2.2.2.2.1 i h14⟩

theorem frame_body {s t : BitRAMState} (h : Body.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i h4 h10 h12 h13 _ h20 hb => h.2.2.2.2 i h4 h10 h12 h13 h20 hb⟩

theorem ready_counter {s t : Store} (h : Counted.Frame 14 s t) (hr : LogRat.Ready s.val) :
    LogRat.Ready t.val :=
  ⟨(h.2.2.2.2.2.1 10 (by decide)).trans hr.1,
    (h.2.2.2.2.2.1 12 (by decide)).trans hr.2.1,
    (h.2.2.2.2.2.1 13 (by decide)).trans hr.2.2⟩

theorem scratch_counter {s t : Store} (h : Counted.Frame 14 s t) (hr : Scratch s.val 0) :
    Scratch t.val 0 :=
  ⟨blank_of_eq (h.2.2.2.2.2.1 0 (by decide)) hr.1,
    word_of_eq (h.2.2.2.2.2.1 1 (by decide)) hr.2.1,
    blank_of_eq (h.2.2.2.2.2.1 2 (by decide)) hr.2.2.1,
    blank_of_eq (h.2.2.2.2.2.1 3 (by decide)) hr.2.2.2⟩

theorem bank_counter {s t : Store} (h : Counted.Frame 14 s t) {v : ℕ → ℕ}
    (hr : Bank s.val v) : Bank t.val v := by
  intro i hi hi'
  exact word_of_eq (h.2.2.2.2.2.1 i (by omega)) (hr i hi hi')

/-- The only loop control is the physical binary countdown word. Each fixed
body parses one rational, compares two raw pairs, and logs the signed input. -/
theorem executes (qs : List ℚ) (current : Pair) (B : ℕ) (counterBits : List Bool)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hvalue : addressValue counterBits = qs.length)
    (hcounter : s.val.tapes 14 = BitTape.ofList counterBits)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hwidth : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogRat.Ready s.val) (harchive : s.val.tapes 20 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ price counterBits qs B ∧
      Executes (preceding ++ (records qs ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (records qs).length ∧
      Bank t.val (bankOf (scan current qs)) ∧ Scratch t.val 0 ∧ LogRat.Ready t.val ∧
      t.val.tapes 20 = BitTape.atEnd (archive ++ records qs) ∧ Frame s.val t.val := by
  induction qs generalizing current counterBits preceding archive s with
  | nil =>
    obtain ⟨t, ht, _, hz, hf⟩ := Counted.test_executes 14
      (preceding ++ (records [] ++ suffix)) tape s counterBits hcounter
    refine ⟨13 * counterBits.length + 15, t, by simp [price],
      ht.seq (Executes.done (hz.mpr hvalue)), ?_, bank_counter hf hbank,
      scratch_counter hf hready, ready_counter hf hparser, ?_, frame_counter hf⟩
    · simpa [records] using hf.2.1
    · simpa [records] using (hf.2.2.2.2.2.1 20 (by decide)).trans harchive
  | cons q qs ih =>
    let input := preceding ++ (records (q :: qs) ++ suffix)
    obtain ⟨tested, ht, hw, hz, hf⟩ := Counted.test_executes 14 input tape s counterBits hcounter
    have hpred : addressValue (subtractBit true counterBits) = qs.length := by
      rw [subtractBit_pred counterBits (by simp [hvalue]), hvalue]
      simp
    have htrue : tested.val.registers 29 = true := by
      cases hb : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp hb; simp only [List.length_cons] at hvalue; omega
    have htestedhead := hf.2.1.trans hhead
    obtain ⟨c, middle, hc, hm, hmhead, hmbank, hmready, hmparser, hmlog, hmf⟩ :=
      Body.executes q current B preceding (records qs ++ suffix) archive tape tested htestedhead
        hpositive hcurrent (hwidth q (by simp)) (bank_counter hf hbank)
        (scratch_counter hf hready) (ready_counter hf hparser)
        ((hf.2.2.2.2.2.1 20 (by decide)).trans harchive)
    have hi : preceding ++ (Codec.rat q ++ (records qs ++ suffix)) = input := by
      simp [input, records, List.append_assoc]
    rw [hi] at hm
    have hmiddlehead : middle.val.inputHead = (preceding ++ Codec.rat q).length := by
      simpa [htestedhead] using hmhead
    have hmiddleword : middle.val.tapes 14 = BitTape.ofList (subtractBit true counterBits) :=
      (hmf.2.2.2.2 14 (by decide) (by decide) (by decide) (by decide) (by decide)
        (Or.inl (by decide))).trans hw
    obtain ⟨c', t, hc', hrest, hthead, htbank, htready, htparser, htlog, htf⟩ :=
      ih (select current q) (subtractBit true counterBits) (preceding ++ Codec.rat q)
        (archive ++ Codec.rat q) middle hmiddlehead hpred hmiddleword
        (select_pos current q hpositive) (select_width current q B hcurrent (hwidth q (by simp)))
        (fun r hr => hwidth r (by simp [hr])) hmbank hmready hmparser hmlog
    have hi' : (preceding ++ Codec.rat q) ++ (records qs ++ suffix) = input := by
      simp [input, records, List.append_assoc]
    rw [hi'] at hrest
    change Executes input tape (.seq (Counted.test 14) (.loop 29 (.seq Body.code (Counted.test 14))))
      c' middle t at hrest
    cases hrest with
    | seq restTest restLoop =>
      refine ⟨_, t, ?_, ht.seq (Executes.more htrue (hm.seq restTest) restLoop), ?_,
        htbank, htready, htparser, ?_, ((frame_counter hf).trans (frame_body hmf)).trans htf⟩
      · dsimp [price] at hc' ⊢
        simp only [subtractBit_length] at hc' ⊢
        nlinarith
      · simp only [records, List.flatMap_cons, List.length_append] at *
        omega
      · simpa [records, List.append_assoc] using htlog

end Maxwell.Cost.MagnitudeMax.Loop
