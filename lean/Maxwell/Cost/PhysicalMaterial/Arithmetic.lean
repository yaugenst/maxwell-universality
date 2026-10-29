import Maxwell.Cost.PhysicalMaterial.ArithmeticBank

/-! Material arithmetic is a fixed charged program over stored canonical
natural-number words. Fractions are nonnegative and need not be reduced:
the caller's RationalCanonical serializer performs reduction afterwards. -/
namespace Maxwell.Cost.PhysicalMaterial.Arithmetic
open Structured RationalAccumulator

structure Data where
  baseNum : ℕ
  baseDen : ℕ
  sigmaNum : ℕ
  sigmaDen : ℕ
  strengthNum : ℕ
  strengthDen : ℕ
  deriving DecidableEq, Repr

def work : Finset ℕ := ArithmeticBank.work ∪ {228, 229}
abbrev Frame := BinaryPrecision.Frame work

def Valid (x : Data) : Prop := 0 < x.baseDen ∧ 0 < x.sigmaDen ∧ 0 < x.strengthDen

def Bounded (x : Data) (B : ℕ) : Prop :=
  x.baseNum.bits.length ≤ B ∧ x.baseDen.bits.length ≤ B ∧
  x.sigmaNum.bits.length ≤ B ∧ x.sigmaDen.bits.length ≤ B ∧
  x.strengthNum.bits.length ≤ B ∧ x.strengthDen.bits.length ≤ B

structure Ready (x : Data) (s : Store) : Prop where
  baseNum : Word s.val 270 x.baseNum
  baseDen : Word s.val 271 x.baseDen
  sigmaNum : Word s.val 260 x.sigmaNum
  sigmaDen : Word s.val 261 x.sigmaDen
  strengthNum : Word s.val 272 x.strengthNum
  strengthDen : Word s.val 273 x.strengthDen
  blank : ∀ i ∈ work ∪ {4}, Blank s.val i

def firstNum (x : Data) : ℕ := x.baseDen*(64*x.sigmaNum)+x.sigmaDen*x.baseNum
def firstDen (x : Data) : ℕ := x.sigmaDen*x.baseDen

def numerator (x : Data) : ℕ := firstDen x*(64*x.strengthNum)+x.strengthDen*firstNum x
def denominator (x : Data) : ℕ := x.strengthDen*firstDen x

def value (x : Data) : ℚ :=
  (x.baseNum:ℚ)/x.baseDen + 64*((x.sigmaNum:ℚ)/x.sigmaDen) +
    64*((x.strengthNum:ℚ)/x.strengthDen)

theorem denominator_pos (x : Data) (h : Valid x) : 0 < denominator x :=
  Nat.mul_pos h.2.2 (Nat.mul_pos h.2.1 h.1)

theorem fraction_value (x : Data) (h : Valid x) :
    (numerator x:ℚ)/denominator x = value x := by
  have hfirst : (firstNum x:ℚ)/firstDen x =
      (x.baseNum:ℚ)/x.baseDen+64*((x.sigmaNum:ℚ)/x.sigmaDen) := by
    simpa only [firstNum, firstDen, Nat.cast_mul] using
      ArithmeticBank.value x.baseNum x.baseDen x.sigmaNum x.sigmaDen h.1 h.2.1
  calc
    (numerator x:ℚ)/denominator x =
        (firstNum x:ℚ)/firstDen x+64*((x.strengthNum:ℚ)/x.strengthDen) := by
      simpa only [numerator, denominator, Nat.cast_mul] using
        ArithmeticBank.value (firstNum x) (firstDen x) x.strengthNum x.strengthDen
          (Nat.mul_pos h.2.1 h.1) h.2.2
    _ = value x := by rw [hfirst]; rfl

/-- Cross multiplication has linear output bit growth. -/
theorem numerator_bits (x : Data) (B : ℕ) (h : Bounded x B) :
    (numerator x).bits.length ≤ 4*B+24 := by
  have hn : (firstNum x).bits.length ≤ 2*B+8 :=
    ArithmeticBank.numerator_bits _ _ _ _ B h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hd : (firstDen x).bits.length ≤ 2*B :=
    ArithmeticBank.denominator_bits _ _ B h.2.1 h.2.2.2.1
  have hfinal := ArithmeticBank.numerator_bits (firstNum x) (firstDen x)
    x.strengthNum x.strengthDen (2*B+8) hn (by omega)
    (by have := h.2.2.2.2.1; omega) (by have := h.2.2.2.2.2; omega)
  change (numerator x).bits.length ≤ _ at hfinal
  omega

theorem denominator_bits (x : Data) (B : ℕ) (h : Bounded x B) :
    (denominator x).bits.length ≤ 3*B := by
  have hd : (firstDen x).bits.length ≤ 2*B :=
    ArithmeticBank.denominator_bits _ _ B h.2.1 h.2.2.2.1
  have hs := h.2.2.2.2.2
  exact (bits_mul_le x.strengthDen (firstDen x)).trans (by omega)

private theorem bank_subset : ArithmeticBank.work ⊆ work := Finset.subset_union_left

private theorem frame_bank {s t : BitRAMState} (h : ArithmeticBank.Frame s t) : Frame s t :=
  h.mono bank_subset

private theorem clone_out (source target : ℕ) (hs : 30 ≤ source) (hs' : source ≤ 36)
    (ht : target = 228 ∨ target = 229) (input : List Bool) (randomTape : ℕ → Bool)
    (v : ℕ → ℕ) (s : Store) (hb : Bank s.val v) (hr : Scratch s.val 0)
    (htarget : Blank s.val target) :
    ∃ t, Executes input randomTape (.call (WordTransfer.clone source target))
      (15*(v source).bits.length+17) s t ∧ Word t.val target (v source) ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so, hso⟩ := hb source hs hs'
  obtain ⟨targetOrigin, hto⟩ := htarget
  obtain ⟨t, he, htapes, hf⟩ := WordCall.clone source target (by omega)
    input randomTape (v source).bits so targetOrigin s hso hto
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by simp [htapes, hi]
  refine ⟨t, he, ⟨targetOrigin, by simp [htapes]⟩,
    (fun i hi hi' => word_of_eq (keep i (by omega)) (hb i hi hi')),
    ⟨blank_of_eq (keep 0 (by omega)) hr.1, word_of_eq (keep 1 (by omega)) hr.2.1,
      blank_of_eq (keep 2 (by omega)) hr.2.2.1, blank_of_eq (keep 3 (by omega)) hr.2.2.2⟩,
    ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
      fun i hi => keep i (by simpa using hi)⟩⟩

def exportCode : Code :=
  .seq (.call (WordTransfer.clone 30 228))
    (.seq (.call (WordTransfer.clone 32 229))
      (.seq resetCode (.atom (.literal 23 false))))

private theorem export_executes (input : List Bool) (randomTape : ℕ → Bool) (a b : ℕ)
    (s : Store) (hb : Bank s.val (ArithmeticBank.pair a b)) (hr : Scratch s.val 0)
    (h228 : Blank s.val 228) (h229 : Blank s.val 229) :
    ∃ t, Executes input randomTape exportCode (21*(a.bits.length+b.bits.length)+48) s t ∧
      Word t.val 228 a ∧ Word t.val 229 b ∧ t.val.registers 23 = false ∧
      (∀ i ∈ ArithmeticBank.work, Blank t.val i) ∧ Frame s.val t.val := by
  obtain ⟨s1, e1, h1, b1, r1, f1⟩ := clone_out 30 228 (by decide) (by decide) (Or.inl rfl)
    input randomTape _ s hb hr h228
  obtain ⟨s2, e2, h2, b2, r2, f2⟩ := clone_out 32 229 (by decide) (by decide) (Or.inr rfl)
    input randomTape _ s1 b1 r1 (blank_of_eq (f1.tapes 229 (by simp)) h229)
  obtain ⟨s3, e3, b3, r3, f3⟩ := reset input randomTape _ s2 b2 r2
  have reset_eq : resetBank (ArithmeticBank.pair a b) = (fun _ => 0) := by
    ext i
    simp [resetBank, ArithmeticBank.pair, Function.update_apply]
    split_ifs <;> omega
  have b3zero : Bank s3.val (fun _ => 0) := reset_eq ▸ b3
  let t := Store.ofState (s3.val.setRegister 23 false)
  have ft : Frame s3.val t.val := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have f3' := frame_bank (ArithmeticBank.frame_bank f3)
  have fall : Frame s.val t.val :=
    (((f1.mono (by simp [work])).trans (f2.mono (by simp [work]))).trans f3').trans ft
  refine ⟨t, ?_, ?_, ?_, by simp [t, Store.ofState, BitRAMState.setRegister], ?_, fall⟩
  · convert e1.seq (e2.seq (e3.seq (Executes.literal input randomTape s3 23 false))) using 1 <;>
      first | rfl | (simp [ArithmeticBank.pair]; ring)
  · exact word_of_eq (show t.val.tapes 228 = s1.val.tapes 228 from
      (f3.2.2.2.2.2.1 228 (by decide) (by omega)).trans (f2.tapes 228 (by simp))) h1
  · exact word_of_eq (show t.val.tapes 229 = s2.val.tapes 229 from
      (f3.2.2.2.2.2.1 229 (by decide) (by omega))) h2
  · intro i hi
    simp only [ArithmeticBank.work, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h
    · subst i; exact r3.1
    · subst i; exact (zero_word_iff_blank _ _).mp r3.2.1
    · subst i; exact r3.2.2.1
    · subst i; exact r3.2.2.2
    all_goals subst i; apply (zero_word_iff_blank _ _).mp
    all_goals exact b3zero _ (by decide) (by decide)

def code : Code :=
  .seq (.call (WordTransfer.clone 270 30))
    (.seq (.call (WordTransfer.clone 271 32))
      (.seq (ArithmeticBank.addCode 260 261)
        (.seq (ArithmeticBank.addCode 272 273) exportCode)))

def costBound (B : ℕ) : ℕ := 100000*(B+20)^2

/-- Actual finite material arithmetic, with all temporary words erased and
all input/descriptor tapes retained exactly. The six numbers occur only in
the specification, never in the executable program. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool) (x : Data) (B : ℕ)
    (hx : Valid x) (hB : Bounded x B) (s : Store) (hs : Ready x s) :
    ∃ cost t, Executes input randomTape code cost s t ∧ cost ≤ costBound B ∧
      Word t.val 228 (numerator x) ∧ Word t.val 229 (denominator x) ∧
      t.val.registers 23 = false ∧
      (∀ i ∈ ArithmeticBank.work ∪ {4}, Blank t.val i) ∧ Frame s.val t.val := by
  have blank (i : ℕ) (hi : i ∈ ArithmeticBank.work) : Blank s.val i :=
    hs.blank i (Finset.mem_union_left _ (bank_subset hi))
  have bank0 : Bank s.val (fun _ => 0) := by
    intro i hi hi'
    apply (zero_word_iff_blank _ _).mpr
    apply blank
    interval_cases i <;> simp [ArithmeticBank.work]
  have scratch0 : Scratch s.val 0 := ⟨blank 0 (by simp [ArithmeticBank.work]),
    (zero_word_iff_blank _ _).mpr (blank 1 (by simp [ArithmeticBank.work])),
    blank 2 (by simp [ArithmeticBank.work]), blank 3 (by simp [ArithmeticBank.work])⟩
  obtain ⟨s1, e1, b1, r1, f1⟩ := ArithmeticBank.load 270 30 (by decide) (by decide) (by decide)
    input randomTape x.baseNum _ s hs.baseNum bank0 rfl scratch0
  obtain ⟨s2, e2, b2, r2, f2⟩ := ArithmeticBank.load 271 32 (by decide) (by decide) (by decide)
    input randomTape x.baseDen _ s1
    (word_of_eq (f1.tapes 271 (by simp [ArithmeticBank.work])) hs.baseDen)
    b1 (by simp) r1
  have firstFrame := f1.trans f2
  obtain ⟨c3, s3, e3, hc3, b3, r3, f3⟩ := ArithmeticBank.add 260 261 (by decide) (by decide)
    input randomTape x.baseNum x.baseDen x.sigmaNum x.sigmaDen B
    hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hx.1 hx.2.1 s2 b2 r2
    (word_of_eq (firstFrame.tapes 260 (by simp [ArithmeticBank.work])) hs.sigmaNum)
    (word_of_eq (firstFrame.tapes 261 (by simp [ArithmeticBank.work])) hs.sigmaDen)
  have secondFrame := firstFrame.trans f3
  have hn1 : (firstNum x).bits.length ≤ 2*B+8 :=
    ArithmeticBank.numerator_bits _ _ _ _ B hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1
  have hd1 : (firstDen x).bits.length ≤ 2*B :=
    ArithmeticBank.denominator_bits _ _ B hB.2.1 hB.2.2.2.1
  obtain ⟨c4, s4, e4, hc4, b4, r4, f4⟩ := ArithmeticBank.add 272 273 (by decide) (by decide)
    input randomTape (firstNum x) (firstDen x) x.strengthNum x.strengthDen (2*B+8)
    hn1 (by omega) (by have := hB.2.2.2.2.1; omega) (by have := hB.2.2.2.2.2; omega)
    (Nat.mul_pos hx.2.1 hx.1) hx.2.2 s3 b3 r3
    (word_of_eq (secondFrame.tapes 272 (by simp [ArithmeticBank.work])) hs.strengthNum)
    (word_of_eq (secondFrame.tapes 273 (by simp [ArithmeticBank.work])) hs.strengthDen)
  have beforeExport := secondFrame.trans f4
  obtain ⟨t, et, ht228, ht229, hsign, hblank, ft⟩ := export_executes input randomTape
    (numerator x) (denominator x) s4 b4 r4
    (blank_of_eq (beforeExport.tapes 228 (by simp [ArithmeticBank.work]))
      (hs.blank 228 (by simp [work])))
    (blank_of_eq (beforeExport.tapes 229 (by simp [ArithmeticBank.work]))
      (hs.blank 229 (by simp [work])))
  have fall : Frame s.val t.val := (frame_bank beforeExport).trans ft
  refine ⟨_, t, e1.seq (e2.seq (e3.seq (e4.seq et))), ?_, ht228, ht229, hsign, ?_, fall⟩
  · have hn : (numerator x).bits.length ≤ 2*(2*B+8)+8 :=
      ArithmeticBank.numerator_bits _ _ _ _ (2*B+8) hn1 (by omega)
        (by have := hB.2.2.2.2.1; omega) (by have := hB.2.2.2.2.2; omega)
    have hd : (denominator x).bits.length ≤ 2*(2*B+8) :=
      ArithmeticBank.denominator_bits _ _ (2*B+8) (by omega)
        (by have := hB.2.2.2.2.2; omega)
    have hbN := hB.1
    have hbD := hB.2.1
    dsimp [costBound]
    nlinarith
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hblank i hi
    · have hi4 : i = 4 := by simpa using hi
      subst i
      exact blank_of_eq (fall.tapes 4 (by simp [work, ArithmeticBank.work]))
        (hs.blank 4 (by simp))

end Maxwell.Cost.PhysicalMaterial.Arithmetic
