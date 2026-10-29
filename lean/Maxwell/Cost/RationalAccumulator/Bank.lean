import Maxwell.Cost.StoredProduct
import Maxwell.Cost.WordTransfer
import Maxwell.Cost.Structured.Correctness
import Maxwell.Codec.SplitRational

namespace Maxwell.Cost.RationalAccumulator

open Structured

def Word (s : BitRAMState) (i n : ℕ) : Prop :=
  ∃ origin, s.tapes i = BitTape.shifted n.bits origin

def Blank (s : BitRAMState) (i : ℕ) : Prop :=
  ∃ origin, s.tapes i = {BitTape.blank with head := origin}

def Scratch (s : BitRAMState) (scalar : ℕ) : Prop :=
  Blank s 0 ∧ Word s 1 scalar ∧ Blank s 2 ∧ Blank s 3

def Bank (s : BitRAMState) (v : ℕ → ℕ) : Prop :=
  ∀ i, 30 ≤ i → i ≤ 36 → Word s i (v i)

/-- Input/output/random channels and the caller's persistent tapes/registers
are preserved by each arithmetic update. The seven accumulator tapes and
four arithmetic scratch tapes are the only permitted tape changes. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 hb => (kt i h4 hb).trans (ht i h4 hb),
    fun i h15 h24 h25 h26 h27 =>
      (kg i h15 h24 h25 h26 h27).trans (hg i h15 h24 h25 h26 h27)⟩

@[simp] theorem address_bits (n : ℕ) : addressValue n.bits = n := by
  have he : ∀ bs, addressValue bs = Codec.bitsValue bs := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [addressValue, Codec.bitsValue, ih]
  rw [he]
  exact Codec.bitsValue_bits n

theorem bits_nonempty {n : ℕ} (hn : 0 < n) : 0 < n.bits.length := by
  by_contra h
  have he : n.bits = [] := List.length_eq_zero_iff.mp (by omega)
  have hv := address_bits n
  simp [he, addressValue] at hv
  omega

theorem zero_word_iff_blank (s : BitRAMState) (i : ℕ) : Word s i 0 ↔ Blank s i := by
  simp [Word, Blank, BitTape.shifted, BitTape.blank]

theorem word_of_eq {s t : BitRAMState} {i n : ℕ} (h : t.tapes i = s.tapes i)
    (hw : Word s i n) : Word t i n := by
  obtain ⟨origin, ho⟩ := hw
  exact ⟨origin, h.trans ho⟩

theorem blank_of_eq {s t : BitRAMState} {i : ℕ} (h : t.tapes i = s.tapes i)
    (hw : Blank s i) : Blank t i := by
  obtain ⟨origin, ho⟩ := hw
  exact ⟨origin, h.trans ho⟩

theorem clone_frame {source target : ℕ} {s t : BitRAMState}
    (hsource : source < 4 ∨ (30 ≤ source ∧ source ≤ 36))
    (htarget : target < 4 ∨ (30 ≤ target ∧ target ≤ 36))
    (h : WordTransfer.Frame source target s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 hi => ht i (by omega) (by omega),
    fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

theorem clone_to_one (source : ℕ) (hs : 30 ≤ source) (hs' : source ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source 1))
      (15 * (v source).bits.length + 17) s t ∧
      Bank t.val v ∧ Scratch t.val (v source) ∧ Frame s.val t.val := by
  obtain ⟨so, hsource⟩ := hbank source hs hs'
  obtain ⟨xo, hone⟩ := (zero_word_iff_blank s.val 1).mp hready.2.1
  obtain ⟨t, ht, hp, hts, htt, hf⟩ := WordTransfer.clone_steps source 1 (by omega)
    input tape (v source).bits so xo s.val s.property hsource hone
  refine ⟨Store.ofState t, ?_, ?_, ?_, clone_frame (Or.inr ⟨hs, hs'⟩) (Or.inl (by omega)) hf⟩
  · exact Executes.call _ _ _ _ ht (by
      simp [WordTransfer.clone, hp, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  · intro i hi hi'
    by_cases he : i = source
    · subst i; exact ⟨so, hts⟩
    · exact word_of_eq (hf.2.2.2.2.2.1 i he (by omega)) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      ⟨xo, htt⟩, blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩

theorem clone_bank (source target : ℕ) (hs : 30 ≤ source) (hs' : source ≤ 36)
    (ht : 30 ≤ target) (ht' : target ≤ 36) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (scalar : ℕ) (s : Store)
    (hbank : Bank s.val v) (hzero : v target = 0) (hready : Scratch s.val scalar) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source target))
      (15 * (v source).bits.length + 17) s t ∧
      Bank t.val (Function.update v target (v source)) ∧ Scratch t.val scalar ∧ Frame s.val t.val := by
  obtain ⟨so, hsource⟩ := hbank source hs hs'
  have htarget := hbank target ht ht'
  rw [hzero, zero_word_iff_blank] at htarget
  obtain ⟨xo, htarget⟩ := htarget
  obtain ⟨t, he, hp, hts, htt, hf⟩ := WordTransfer.clone_steps source target hne
    input tape (v source).bits so xo s.val s.property hsource htarget
  refine ⟨Store.ofState t, ?_, ?_, ?_, clone_frame (Or.inr ⟨hs, hs'⟩) (Or.inr ⟨ht, ht'⟩) hf⟩
  · exact Executes.call _ _ _ _ he (by
      simp [WordTransfer.clone, hp, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  · intro i hi hi'
    by_cases hit : i = target
    · subst i; exact ⟨xo, by simpa only [Function.update_self, Store.ofState] using htt⟩
    · simp only [Function.update_of_ne hit]
      by_cases his : i = source
      · subst i; exact ⟨so, hts⟩
      · exact word_of_eq (hf.2.2.2.2.2.1 i his hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      word_of_eq (hf.2.2.2.2.2.1 1 (by omega) (by omega)) hready.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩

theorem clear_one (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (scalar : ℕ) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val scalar) :
    ∃ t : Store, Executes input tape (.call (TapeOps.clear 1))
      (6 * scalar.bits.length + 4) s t ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨origin, hone⟩ := hready.2.1
  obtain ⟨t, he, hp, hclear, hf⟩ := TapeOps.clear_steps 1 input tape scalar.bits origin
    s.val s.property hone
  refine ⟨Store.ofState t, ?_, ?_, ?_,
    clone_frame (Or.inl (by omega)) (Or.inl (by omega)) (WordTransfer.frame_of_copy hf)⟩
  · exact Executes.call _ _ _ _ he (by simp [TapeOps.clear, hp])
  · intro i hi hi'
    exact word_of_eq (hf.2.2.2.2.2.1 i (by omega) (by omega)) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      (zero_word_iff_blank _ _).mpr ⟨origin + scalar.bits.length, hclear⟩,
      blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩

theorem multiply_bank (target : ℕ) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (scalar : ℕ) (hscalar : 0 < scalar)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val scalar) :
    ∃ cost, ∃ t : Store, cost ≤ 500 * (scalar.bits.length + (v target).bits.length + 2)^2 + 1 ∧
      Executes input tape (.call (StoredProduct.program target)) cost s t ∧
      Bank t.val (Function.update v target (scalar * v target)) ∧
      Scratch t.val scalar ∧ Frame s.val t.val := by
  obtain ⟨ao, ha⟩ := hready.1
  obtain ⟨xo, hx⟩ := hready.2.1
  obtain ⟨zo, hz⟩ := hready.2.2.1
  obtain ⟨yo, hy⟩ := hready.2.2.2
  obtain ⟨origin, hw⟩ := hbank target ht ht'
  obtain ⟨cost, t, ro, so, hc, he, hp, hout, h0, h1, h2, h3, hf⟩ :=
    StoredProduct.simulation target (by omega) input tape scalar.bits (v target).bits
      ao xo zo yo origin (bits_nonempty hscalar) s.val s.property ha hx hz hy hw
  refine ⟨cost + 1, Store.ofState t, by omega, ?_, ?_,
    ⟨⟨ro, h0⟩, ⟨xo, h1⟩, ⟨so, h2⟩, ⟨yo + (v target).bits.length, h3⟩⟩, ?_⟩
  · exact Executes.call _ _ _ _ he (by
      simp [StoredProduct.program, hp, TapeOps.copyClear, HornerMultiply.program,
        NormalizeWord.program, ScanForward.program, TapeOps.trim, Rewind.program,
        TapeOps.clear, BitRAMInstruction.relocate, RewindOvershoot.program,
        RewindOvershoot.preamble, BitRAM.link, rippleAdder])
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨origin + (v target).bits.length, by simpa [Store.ofState] using hout⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hf.2.2.2.2.2.1 i (by omega) hit) (hbank i hi hi')
  · rcases hf with ⟨haddress, hinput, hmemory, hrandom, houtput, htapes, hregisters⟩
    exact ⟨haddress, hinput, hmemory, hrandom, houtput,
      fun i hi hi' => htapes i hi (by omega), hregisters⟩

end Maxwell.Cost.RationalAccumulator
