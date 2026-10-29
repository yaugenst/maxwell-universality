import Maxwell.Cost.BankArray.ReadCanonical
import Maxwell.Cost.CalibrationMatrix.Affine.Load
import Maxwell.Cost.RationalCanonical.Transfer

/-! A shared actual indexed reader for signed-channel mode arrays. Metadata and
output ports are parameters; the retained source mode uses banks 510--515. -/
namespace Maxwell.Cost.ModeRead
open Structured RationalAccumulator

structure Layout where
  width : ℕ
  clock : ℕ
  positive : ℕ
  negative : ℕ
  denominator : ℕ
  index : ℕ
  output : Fin 3 → ℕ

def Layout.inputs (l : Layout) : Finset ℕ :=
  {l.width, l.clock, l.positive, l.negative, l.denominator, l.index}

def Layout.Valid (l : Layout) : Prop :=
  (∀ j ∈ l.inputs, 10 ≤ j) ∧ (∀ j, 10 ≤ l.output j) ∧
  Function.Injective l.output ∧ (∀ j, l.output j ∉ l.inputs)

def Layout.changed (l : Layout) : Finset ℕ := Finset.univ.image l.output

def Layout.base (l : Layout) (a : Fin 2) : ℕ := if a = 0 then l.positive else l.negative

structure Data (n : ℕ) where
  width : List Bool
  clock : List Bool
  bases : Fin 2 → List Bool
  words : Fin 2 → Vector (List Bool) n
  denominator : ℕ
  width_nonempty : 0 < width.length
  clock_length : clock.length = addressValue width

def Data.value {n : ℕ} (d : Data n) (i : Fin n) (a : Fin 2) : ℕ :=
  addressValue ((d.words a).get i)

def Data.Sized {n : ℕ} (d : Data n) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧
  (∀ a, (d.bases a).length ≤ B) ∧ d.denominator.bits.length ≤ B

structure Stored {n : ℕ} (l : Layout) (d : Data n) (s : BitRAMState) : Prop where
  width : BankArray.Word s l.width d.width
  clock : BankArray.Word s l.clock d.clock
  bases : ∀ a, BankArray.Word s (l.base a) (d.bases a)
  denominator : Word s l.denominator d.denominator
  arrays : ∀ a, BitArray.Represents s.memory (addressValue (d.bases a))
    (addressValue d.width) (d.words a)

def Ready (s : BitRAMState) : Prop := ∀ j, j < 10 → Blank s j

structure Frame (changed : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j = 4 ∨ 10 ≤ j → j ∉ changed → t.tapes j = s.tapes j
  registers : ∀ j, 30 ≤ j → t.registers j = s.registers j

theorem Frame.trans {c : Finset ℕ} {s t u : BitRAMState}
    (h : Frame c s t) (k : Frame c t u) : Frame c s u :=
  ⟨k.memory.trans h.memory, k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun j hj hn => (k.tapes j hj hn).trans (h.tapes j hj hn),
    fun j hj => (k.registers j hj).trans (h.registers j hj)⟩

theorem Layout.input_ne_output {l : Layout} (hl : l.Valid)
    {j : ℕ} (hj : j ∈ l.inputs) (a : Fin 3) : j ≠ l.output a :=
  fun he => hl.2.2.2 a (he ▸ hj)

theorem Layout.input_unchanged {l : Layout} (hl : l.Valid)
    {j : ℕ} (hj : j ∈ l.inputs) : j ∉ l.changed := by
  simp only [Layout.changed, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro a he
  exact l.input_ne_output hl hj a he.symm

theorem Stored.of_frame {n : ℕ} {l : Layout} {d : Data n} {s t : BitRAMState}
    (hl : l.Valid) (h : Stored l d s) (hf : Frame l.changed s t) : Stored l d t := by
  have same (j : ℕ) (hj : j ∈ l.inputs) : t.tapes j = s.tapes j :=
    hf.tapes j (Or.inr (hl.1 j hj)) (l.input_unchanged hl hj)
  refine ⟨BankArray.word_of_eq (same _ (by simp [Layout.inputs])) h.width,
    BankArray.word_of_eq (same _ (by simp [Layout.inputs])) h.clock, ?_,
    word_of_eq (same _ (by simp [Layout.inputs])) h.denominator, ?_⟩
  · intro a
    apply BankArray.word_of_eq (same _ _) (h.bases a)
    fin_cases a <;> simp [Layout.base, Layout.inputs]
  · intro a
    simpa only [hf.memory] using h.arrays a

def channelCode (l : Layout) (a : Fin 2) : Code :=
  BankArray.readCanonicalCode l.width l.index (l.base a) l.clock
    (l.output ⟨a.val, by omega⟩)

theorem channel {n : ℕ} (l : Layout) (hl : l.Valid) (d : Data n) (i : Fin n)
    (a : Fin 2) (B : ℕ) (hd : d.Sized B) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hs : Ready s.val) (hst : Stored l d s.val)
    (hindex : BankArray.Word s.val l.index index)
    (hz : Blank s.val (l.output ⟨a.val, by omega⟩)) :
    ∃ cost t, cost ≤ 20000 * (B+2)^2 ∧
      Executes input tape (channelCode l a) cost s t ∧ Ready t.val ∧
      Stored l d t.val ∧ Word t.val (l.output ⟨a.val, by omega⟩) (d.value i a) ∧
      Frame l.changed s.val t.val ∧
      (∀ j, j = 4 ∨ 10 ≤ j → j ≠ l.output ⟨a.val, by omega⟩ →
        t.val.tapes j = s.val.tapes j) := by
  have hbase : l.base a ∈ l.inputs := by fin_cases a <;> simp [Layout.base, Layout.inputs]
  have hscratch : BankArray.Scratch s.val :=
    ⟨hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide),
      hs 5 (by decide), hs 6 (by decide), hs 8 (by decide), hs 9 (by decide)⟩
  obtain ⟨cost, t, hc, he, hw, ht, h7, hm, _, hf⟩ := BankArray.read_canonical
    l.width l.index (l.base a) l.clock (l.output ⟨a.val, by omega⟩)
    (hl.1 _ (by simp [Layout.inputs])) (hl.1 _ (by simp [Layout.inputs]))
    (hl.1 _ hbase) (hl.1 _ (by simp [Layout.inputs])) (hl.2.1 _)
    input tape d.width index (d.bases a) d.clock (d.words a) i
    d.width_nonempty hi d.clock_length s hscratch (hs 7 (by decide)) hz
    hst.width hindex (hst.bases a) hst.clock (hst.arrays a)
  have frame : Frame l.changed s.val t.val := by
    refine ⟨hm, hf.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
    · intro j hj hn
      apply hf.2.2.2.1 j hj
      intro heq
      exact hn (heq ▸ Finset.mem_image.mpr ⟨⟨a.val, by omega⟩, Finset.mem_univ _, rfl⟩)
    · intro j hj
      exact hf.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
  refine ⟨cost, t, hc.trans (CalibrationMatrix.Affine.read_cost_le _ _ _ _ B
    hd.1 hd.2.1 hil (hd.2.2.1 a) d.clock_length), he, ?_,
    hst.of_frame hl frame, hw, frame, hf.2.2.2.1⟩
  intro j hj
  rcases ht with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
  have htarget := hl.2.1 ⟨a.val, by omega⟩
  interval_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact blank_of_eq (hf.2.2.2.1 4 (by omega) (by omega)) (hs 4 (by decide))
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

def code (l : Layout) : Code :=
  .seq (channelCode l 0) (.seq (channelCode l 1)
    (.call (WordTransfer.clone l.denominator (l.output 2))))

theorem executes {n : ℕ} (l : Layout) (hl : l.Valid) (d : Data n) (i : Fin n)
    (B : ℕ) (hd : d.Sized B) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hs : Ready s.val) (hst : Stored l d s.val)
    (hindex : BankArray.Word s.val l.index index) (hz : ∀ a, Blank s.val (l.output a)) :
    ∃ cost t, cost ≤ 41000 * (B+2)^2 ∧ Executes input tape (code l) cost s t ∧
      Ready t.val ∧ Stored l d t.val ∧
      Word t.val (l.output 0) (d.value i 0) ∧
      Word t.val (l.output 1) (d.value i 1) ∧
      Word t.val (l.output 2) d.denominator ∧ Frame l.changed s.val t.val := by
  have out_ne (a b : Fin 3) (h : a ≠ b) : l.output a ≠ l.output b := fun he => h (hl.2.2.1 he)
  have hden : l.denominator ∈ l.inputs := by simp [Layout.inputs]
  have hidx : l.index ∈ l.inputs := by simp [Layout.inputs]
  obtain ⟨c0, t0, hc0, e0, r0, st0, w0, f0, same0⟩ :=
    channel l hl d i 0 B hd input tape index hi hil s hs hst hindex (hz 0)
  obtain ⟨c1, t1, hc1, e1, r1, st1, w1, f1, same1⟩ :=
    channel l hl d i 1 B hd input tape index hi hil t0 r0 st0
      (BankArray.word_of_eq (same0 _ (Or.inr (hl.1 _ hidx))
        (l.input_ne_output hl hidx 0)) hindex)
      (blank_of_eq (same0 _ (Or.inr (hl.2.1 1)) (out_ne 1 0 (by decide))) (hz 1))
  have hz2 : Word t1.val (l.output 2) 0 := (zero_word_iff_blank _ _).mpr
    (blank_of_eq (same1 _ (Or.inr (hl.2.1 2)) (out_ne 2 1 (by decide)))
      (blank_of_eq (same0 _ (Or.inr (hl.2.1 2)) (out_ne 2 0 (by decide))) (hz 2)))
  obtain ⟨origin, hw⟩ := st1.denominator
  obtain ⟨origin2, hz2⟩ := (zero_word_iff_blank _ _).mp hz2
  obtain ⟨t, ec, tapes, fc⟩ := WordCall.clone l.denominator (l.output 2)
    (l.input_ne_output hl hden 2) input tape d.denominator.bits origin origin2 t1 hw hz2
  have wd : Word t.val (l.output 2) d.denominator := ⟨origin2, by simp [tapes]⟩
  have sameDen : t.val.tapes l.denominator = t1.val.tapes l.denominator := by
    simp only [tapes, Function.update_of_ne (l.input_ne_output hl hden 2)]
  have fc' : Frame l.changed t1.val t.val := by
    refine ⟨fc.2.2.1, fc.2.1, fc.2.2.2.1, fc.2.2.2.2.1, ?_, ?_⟩
    · intro j _ hn
      by_cases hj : j = l.denominator
      · simpa only [hj] using sameDen
      · apply fc.2.2.2.2.2.1 j hj
        intro heq
        exact hn (heq ▸ Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    · intro j hj
      exact fc.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)
  have frame := f0.trans (f1.trans fc')
  refine ⟨c0+(c1+(15*d.denominator.bits.length+17)), t, ?_,
    e0.seq (e1.seq ec), ?_, hst.of_frame hl frame, ?_, ?_, wd, frame⟩
  · have hdlen := hd.2.2.2
    nlinarith [sq_nonneg (B : ℤ)]
  · intro j hj
    exact blank_of_eq (fc.2.2.2.2.2.1 j (by have := hl.1 _ hden; omega)
      (by have := hl.2.1 2; omega)) (r1 j hj)
  · apply word_of_eq (fc.2.2.2.2.2.1 _
      (Ne.symm (l.input_ne_output hl hden 0)) (out_ne 0 2 (by decide)))
    exact word_of_eq (same1 _ (Or.inr (hl.2.1 0)) (out_ne 0 1 (by decide))) w0
  · exact word_of_eq (fc.2.2.2.2.2.1 _
      (Ne.symm (l.input_ne_output hl hden 1)) (out_ne 1 2 (by decide))) w1

/-- The single retained weighted/rounded mode shared by source and decoder. -/
def retained (index : ℕ) (output : Fin 3 → ℕ) : Layout :=
  ⟨514, 515, 510, 511, 512, index, output⟩

theorem retained_valid (index : ℕ) (output : Fin 3 → ℕ) (hi : 10 ≤ index)
    (ho : ∀ a, 10 ≤ output a ∧ output a < 510)
    (hinj : Function.Injective output) (hne : ∀ a, index ≠ output a) :
    (retained index output).Valid := by
  refine ⟨?_, fun a => (ho a).1, hinj, ?_⟩
  · intro j hj
    simp only [Layout.inputs, retained, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h | h | h | h | h <;> omega
  · intro a
    have ha := ho a
    have hn := hne a
    simp only [Layout.inputs, retained, Finset.mem_insert, Finset.mem_singleton]
    omega

end Maxwell.Cost.ModeRead
