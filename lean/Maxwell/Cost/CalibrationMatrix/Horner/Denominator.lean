import Maxwell.Cost.CalibrationMatrix.NatPower
import Maxwell.Cost.NormalizeCoefficient.Load
import Maxwell.Cost.RationalAccumulator.Reset
import Maxwell.Cost.RationalCanonical.Transfer

namespace Maxwell.Cost.CalibrationMatrix.Horner.Denominator
open Structured RationalAccumulator
set_option maxHeartbeats 1200000

/-- Persistent operands may share tapes when their values agree. -/
structure Layout where
  denominator : ℕ
  numeratorScale : ℕ
  denominatorScale : ℕ
  count : ℕ
  denominator_ge : 150 ≤ denominator
  numeratorScale_ge : 150 ≤ numeratorScale
  denominatorScale_ge : 150 ≤ denominatorScale
  count_ge : 150 ≤ count

def value (D U V N : ℕ) : ℕ := U * V * (D^2)^(3*N+2)

theorem value_identity (D U V N : ℕ) :
    ((D^2)^3)^N * (U*V*(D^2)^2) = value D U V N := by
  simp only [value, pow_mul, pow_add]
  ring

theorem value_pos {D U V N : ℕ} (hD : 0 < D) (hU : 0 < U) (hV : 0 < V) :
    0 < value D U V N := Nat.mul_pos (Nat.mul_pos hU hV) (pow_pos (pow_pos hD _) _)

structure Widths (D U V N B : ℕ) : Prop where
  initial : ∀ a ∈ [D, U, V, D^2, (D^2)^2, (D^2)^3,
    U*V, U*V*(D^2), U*V*(D^2)^2], a.bits.length ≤ B
  count : N.bits.length ≤ B
  power : ∀ k, k ≤ N → (((D^2)^3)^k * (U*V*(D^2)^2)).bits.length ≤ B

def unitCost (B : ℕ) : ℕ := 4000*(2*B+3)^2

private theorem small_cost (B n : ℕ) (hn : n ≤ B) :
    15*n+17 ≤ unitCost B ∧ 6*n+4 ≤ unitCost B ∧ 12*n+11 ≤ unitCost B := by
  dsimp [unitCost]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- Copy a bank operand to the scalar tape, multiply, then clear that tape. -/
def multiplyCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 1))
    (.seq (productCode target) (.call (TapeOps.clear 1)))

theorem multiply (source target B : ℕ) (hs : 30 ≤ source) (hs' : source ≤ 36)
    (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hsource : (v source).bits.length ≤ B) (htarget : (v target).bits.length ≤ B) :
    ∃ cost, ∃ t : Store, cost ≤ unitCost B ∧
      Executes input tape (multiplyCode source target) cost s t ∧
      Bank t.val (Function.update v target (v source*v target)) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ea, ba, sa, fa⟩ := clone_to_one source hs hs' input tape v s hbank hready
  obtain ⟨cost, b, cb, eb, bb, sb, fb⟩ := product target ht ht' input tape v (v source) a ba sa
  obtain ⟨t, et, bt, st, ft⟩ := clear_one input tape _ (v source) b bb sb
  refine ⟨_, t, ?_, ea.seq (eb.seq et), bt, st, (fa.trans fb).trans ft⟩
  have hc : cost ≤ 1000*(2*B+3)^2 := cb.trans (by gcongr; omega)
  dsimp [unitCost]
  nlinarith

def bankValues (a b c d : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (fun _ => 0)
    30 a) 31 b) 32 c) 36 d

@[simp] theorem bankValues30 (a b c d : ℕ) : bankValues a b c d 30 = a := by simp [bankValues]
@[simp] theorem bankValues31 (a b c d : ℕ) : bankValues a b c d 31 = b := by simp [bankValues]
@[simp] theorem bankValues32 (a b c d : ℕ) : bankValues a b c d 32 = c := by simp [bankValues]
@[simp] theorem bankValues36 (a b c d : ℕ) : bankValues a b c d 36 = d := by simp [bankValues]

private theorem bankValues_zero : bankValues 0 0 0 0 = fun _ => 0 := by
  funext i
  simp [bankValues]

private theorem update30 (a b c d x : ℕ) :
    Function.update (bankValues a b c d) 30 x = bankValues x b c d := by
  funext i; by_cases hi : i = 30 <;> simp [bankValues, Function.update_apply, hi]
private theorem update31 (a b c d x : ℕ) :
    Function.update (bankValues a b c d) 31 x = bankValues a x c d := by
  funext i; by_cases hi : i = 31 <;> simp [bankValues, Function.update_apply, hi]
private theorem update32 (a b c d x : ℕ) :
    Function.update (bankValues a b c d) 32 x = bankValues a b x d := by
  funext i; by_cases hi : i = 32 <;> simp [bankValues, Function.update_apply, hi]
private theorem update36 (a b c d x : ℕ) :
    Function.update (bankValues a b c d) 36 x = bankValues a b c x := by
  funext i; by_cases hi : i = 36 <;> simp [bankValues, Function.update_apply, hi]

private theorem frame_word {s t : BitRAMState} (hf : RationalAccumulator.Frame s t)
    (i n : ℕ) (hi : 150 ≤ i) (hw : Word s i n) : Word t i n :=
  word_of_eq (hf.2.2.2.2.2.1 i (by omega) (Or.inr (by omega))) hw

def prepareCode (l : Layout) : Code :=
  .seq (.call (WordTransfer.clone l.denominator 30))
  (.seq (multiplyCode 30 30)
  (.seq (.call (WordTransfer.clone 30 31))
  (.seq (multiplyCode 30 31)
  (.seq (multiplyCode 30 31)
  (.seq (.call (WordTransfer.clone l.numeratorScale 36))
  (.seq (.call (WordTransfer.clone l.denominatorScale 32))
  (.seq (multiplyCode 32 36)
  (.seq (.call (TapeOps.clear 32))
  (.seq (multiplyCode 30 36) (multiplyCode 30 36))))))))))

theorem prepare (l : Layout) (D U V N B : ℕ) (hw : Widths D U V N B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) :
    ∃ cost, ∃ t : Store, cost ≤ 11*unitCost B ∧
      Executes input tape (prepareCode l) cost s t ∧
      Bank t.val (bankValues (D^2) ((D^2)^3) 0 (U*V*(D^2)^2)) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  have wD := hw.initial D (by simp)
  have wU := hw.initial U (by simp)
  have wV := hw.initial V (by simp)
  have wD2 := hw.initial (D^2) (by simp)
  have wD4 := hw.initial ((D^2)^2) (by simp)
  have wUV := hw.initial (U*V) (by simp)
  have wUVD2 := hw.initial (U*V*(D^2)) (by simp)
  rw [← bankValues_zero] at hbank
  obtain ⟨s1, e1, b1, r1, f1⟩ := NormalizeCoefficient.clone_external l.denominator 30
    (by have := l.denominator_ge; omega) (by omega) (by omega)
    input tape _ D s hbank hready (by simp [bankValues]) hD
  rw [update30] at b1
  obtain ⟨c2, s2, hc2, e2, b2, r2, f2⟩ := multiply 30 30 B (by omega) (by omega)
    (by omega) (by omega) input tape _ s1 b1 r1 (by simpa [bankValues] using wD)
    (by simpa [bankValues] using wD)
  have b2' : Bank s2.val (bankValues (D^2) 0 0 0) := by
    simpa only [bankValues30, update30, pow_two] using b2
  obtain ⟨s3, e3, b3, r3, f3⟩ := clone_bank 30 31 (by omega) (by omega) (by omega) (by omega)
    (by omega) input tape _ 0 s2 b2' (by simp [bankValues]) r2
  have b3' : Bank s3.val (bankValues (D^2) (D^2) 0 0) := by
    simpa only [show bankValues (D^2) 0 0 0 30 = D^2 by simp [bankValues], update31] using b3
  obtain ⟨c4, s4, hc4, e4, b4, r4, f4⟩ := multiply 30 31 B (by omega) (by omega)
    (by omega) (by omega) input tape _ s3 b3' r3 (by simpa [bankValues] using wD2)
    (by simpa [bankValues] using wD2)
  have b4' : Bank s4.val (bankValues (D^2) ((D^2)^2) 0 0) := by
    simpa [show bankValues (D^2) (D^2) 0 0 30 = D^2 by simp [bankValues],
      show bankValues (D^2) (D^2) 0 0 31 = D^2 by simp [bankValues], update31, pow_two] using b4
  obtain ⟨c5, s5, hc5, e5, b5, r5, f5⟩ := multiply 30 31 B (by omega) (by omega)
    (by omega) (by omega) input tape _ s4 b4' r4 (by simpa [bankValues] using wD2)
    (by simpa [bankValues] using wD4)
  have b5' : Bank s5.val (bankValues (D^2) ((D^2)^3) 0 0) := by
    simpa [show bankValues (D^2) ((D^2)^2) 0 0 30 = D^2 by simp [bankValues],
      show bankValues (D^2) ((D^2)^2) 0 0 31 = (D^2)^2 by simp [bankValues],
      update31, pow_succ, Nat.mul_comm] using b5
  have fs5 := (((f1.trans f2).trans f3).trans f4).trans f5
  obtain ⟨s6, e6, b6, r6, f6⟩ := NormalizeCoefficient.clone_external l.numeratorScale 36
    (by have := l.numeratorScale_ge; omega) (by omega) (by omega)
    input tape _ U s5 b5' r5 (by simp [bankValues])
    (frame_word fs5 _ _ l.numeratorScale_ge hU)
  rw [update36] at b6
  obtain ⟨s7, e7, b7, r7, f7⟩ := NormalizeCoefficient.clone_external l.denominatorScale 32
    (by have := l.denominatorScale_ge; omega) (by omega) (by omega)
    input tape _ V s6 b6 r6 (by simp [bankValues])
    (frame_word (fs5.trans f6) _ _ l.denominatorScale_ge hV)
  rw [update32] at b7
  obtain ⟨c8, s8, hc8, e8, b8, r8, f8⟩ := multiply 32 36 B (by omega) (by omega)
    (by omega) (by omega) input tape _ s7 b7 r7 (by simpa [bankValues] using wV)
    (by simpa [bankValues] using wU)
  have b8' : Bank s8.val (bankValues (D^2) ((D^2)^3) V (U*V)) := by
    simpa [show bankValues (D^2) ((D^2)^3) V U 32 = V by simp [bankValues],
      show bankValues (D^2) ((D^2)^3) V U 36 = U by simp [bankValues], update36, Nat.mul_comm] using b8
  obtain ⟨s9, e9, b9, r9, f9⟩ := clear_bank 32 (by omega) (by omega) input tape _ 0 s8 b8' r8
  rw [update32] at b9
  obtain ⟨c10, s10, hc10, e10, b10, r10, f10⟩ := multiply 30 36 B (by omega) (by omega)
    (by omega) (by omega) input tape _ s9 b9 r9 (by simpa [bankValues] using wD2)
    (by simpa [bankValues] using wUV)
  have b10' : Bank s10.val (bankValues (D^2) ((D^2)^3) 0 (U*V*(D^2))) := by
    simpa [show bankValues (D^2) ((D^2)^3) 0 (U*V) 30 = D^2 by simp [bankValues],
      show bankValues (D^2) ((D^2)^3) 0 (U*V) 36 = U*V by simp [bankValues], update36, Nat.mul_comm] using b10
  obtain ⟨c11, t, hc11, e11, b11, r11, f11⟩ := multiply 30 36 B (by omega) (by omega)
    (by omega) (by omega) input tape _ s10 b10' r10 (by simpa [bankValues] using wD2)
    (by simpa [bankValues] using wUVD2)
  have b11' : Bank t.val (bankValues (D^2) ((D^2)^3) 0 (U*V*(D^2)^2)) := by
    simpa [show bankValues (D^2) ((D^2)^3) 0 (U*V*(D^2)) 30 = D^2 by simp [bankValues],
      show bankValues (D^2) ((D^2)^3) 0 (U*V*(D^2)) 36 = U*V*(D^2) by simp [bankValues],
      update36, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using b11
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq
    (e8.seq (e9.seq (e10.seq e11)))))))))
  simp only [show bankValues (D^2) 0 0 0 30 = D^2 by simp [bankValues],
    show bankValues (D^2) ((D^2)^3) V (U*V) 32 = V by simp [bankValues]] at he
  refine ⟨_, t, ?_, he, b11', r11, (((((fs5.trans f6).trans f7).trans f8).trans f9).trans f10).trans f11⟩
  have hd := (small_cost B _ wD).1
  have hd2 := (small_cost B _ wD2).1
  have hu := (small_cost B _ wU).1
  have hv := (small_cost B _ wV).1
  have hv' := (small_cost B _ wV).2.1
  omega

/-- Only the arithmetic workspace, countdown, and destination may change. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → i ≠ 141 → i ≠ 142 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, k.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i hi hj hk hl => (k.2.2.2.2.2.1 i hi hj hk hl).trans (h.2.2.2.2.2.1 i hi hj hk hl),
    fun i hi a b c d e f => (k.2.2.2.2.2.2 i hi a b c d e f).trans (h.2.2.2.2.2.2 i hi a b c d e f)⟩

theorem Frame.of_power {s t : BitRAMState} (h : NatPower.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi hj hk _ => h.2.2.2.2.2.1 i hi hj hk, h.2.2.2.2.2.2⟩

theorem Frame.of_product {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t :=
  Frame.of_power (NatPower.Frame.of_product h)

theorem Frame.word {s t : BitRAMState} (h : Frame s t) (i n : ℕ) (hi : 150 ≤ i)
    (hw : Word s i n) : Word t i n :=
  word_of_eq (h.2.2.2.2.2.1 i (by omega) (Or.inr (by omega)) (by omega) (by omega)) hw

private theorem clone_count (source N : ℕ) (hs : 150 ≤ source)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (base : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val base)
    (hsource : Word s.val source N) (hblank : Blank s.val 141) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source 141))
      (15*N.bits.length+17) s t ∧
      Bank t.val v ∧ Scratch t.val base ∧ Word t.val 141 N ∧ NatPower.Frame s.val t.val := by
  obtain ⟨origin, ho⟩ := hsource
  obtain ⟨targetOrigin, ht⟩ := hblank
  obtain ⟨t, he, heq, hf⟩ := WordCall.clone source 141 (by omega) input tape N.bits
    origin targetOrigin s ho ht
  have keep (i : ℕ) (hi : i ≠ 141) : t.val.tapes i = s.val.tapes i := by simp [heq, hi]
  refine ⟨t, he, fun i hi hi' => word_of_eq (keep i (by omega)) (hbank i hi hi'),
    ⟨blank_of_eq (keep 0 (by omega)) hready.1, word_of_eq (keep 1 (by omega)) hready.2.1,
      blank_of_eq (keep 2 (by omega)) hready.2.2.1,
      blank_of_eq (keep 3 (by omega)) hready.2.2.2⟩,
    ⟨targetOrigin, by simp [heq]⟩, ?_⟩
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i _ _ hi => keep i hi,
    fun i _ h24 h25 h26 h27 _ _ => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

private theorem export_value (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) (hblank : Blank s.val 142) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.move 36 142))
      (12*(v 36).bits.length+11) s t ∧
      Bank t.val (Function.update v 36 0) ∧ Scratch t.val 0 ∧
      Word t.val 142 (v 36) ∧ (t.val.tapes 141 = s.val.tapes 141) ∧ Frame s.val t.val := by
  obtain ⟨t, he, hzero, hvalue, hf⟩ := RationalCanonical.move_word 36 142 (v 36) (by omega)
    input tape s (hbank 36 (by omega) (by omega)) ((zero_word_iff_blank _ _).mpr hblank)
  have keep (i : ℕ) (hi : i ≠ 36) (hj : i ≠ 142) := hf.2.2.2.2.2.1 i hi hj
  refine ⟨t, he, ?_,
    ⟨blank_of_eq (keep 0 (by omega) (by omega)) hready.1,
      word_of_eq (keep 1 (by omega) (by omega)) hready.2.1,
      blank_of_eq (keep 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (keep 3 (by omega) (by omega)) hready.2.2.2⟩,
    hvalue, keep 141 (by omega) (by omega), ?_⟩
  · intro i hi hi'
    by_cases he : i = 36
    · subst i; simpa using hzero
    · simpa only [Function.update_of_ne he] using word_of_eq (keep i he (by omega)) (hbank i hi hi')
  · exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
      fun i _ hi _ hj => keep i (by omega) hj,
      fun i _ h24 h25 h26 h27 _ _ => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

def code (l : Layout) : Code :=
  .seq (prepareCode l)
  (.seq (.call (WordTransfer.clone 31 1))
  (.seq (.call (WordTransfer.clone l.count 141))
  (.seq NatPower.code
  (.seq (.call (TapeOps.clear 1))
  (.seq (.call (TapeOps.clear 30))
  (.seq (.call (TapeOps.clear 31)) (.call (WordTransfer.move 36 142))))))))

def costCap (N B : ℕ) : ℕ := 17*unitCost B + NatPower.costCap N B

theorem costCap_le (N B : ℕ) : costCap N B ≤ 400000*(N+1)*(B+2)^2 := by
  dsimp [costCap, unitCost, NatPower.costCap]
  nlinarith [Nat.zero_le (N*B*B), Nat.zero_le (N*B), Nat.zero_le (B*B)]

/-- The fixed instruction program constructs the physical denominator, exports a
canonical natural word, and clears its countdown and arithmetic workspace. -/
theorem executes (l : Layout) (D U V N B : ℕ) (hw : Widths D U V N B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (hcount : Blank s.val 141) (hout : Blank s.val 142) :
    ∃ cost, ∃ t : Store, cost ≤ costCap N B ∧ Executes input tape (code l) cost s t ∧
      Word t.val 142 (value D U V N) ∧ Bank t.val (fun _ => 0) ∧
      Scratch t.val 0 ∧ Blank t.val 141 ∧ Frame s.val t.val := by
  let v := bankValues (D^2) ((D^2)^3) 0 (U*V*(D^2)^2)
  obtain ⟨c1, s1, hc1, e1, b1, r1, f1⟩ := prepare l D U V N B hw input tape s hbank hready hD hU hV
  obtain ⟨s2, e2, b2, r2, f2⟩ := clone_to_one 31 (by omega) (by omega) input tape v s1 b1 r1
  have fs2 := f1.trans f2
  obtain ⟨s3, e3, b3, r3, hc3, f3⟩ := clone_count l.count N l.count_ge input tape v (v 31) s2 b2 r2
    (frame_word fs2 _ _ l.count_ge hN)
    (blank_of_eq (fs2.2.2.2.2.2.1 141 (by omega) (Or.inr (by omega))) hcount)
  obtain ⟨origin, hcounter⟩ := hc3
  have wbase : (v 31).bits.length ≤ B := by simpa [v] using hw.initial ((D^2)^3) (by simp)
  have wpow : ∀ k, k ≤ N → ((v 31)^k*v 36).bits.length ≤ B := by simpa [v] using hw.power
  obtain ⟨c4, s4, hc4, e4, b4, r4, hcount4, f4⟩ := NatPower.executes input tape v (v 31) N B
    wbase wpow N.bits (address_bits N) hw.count origin s3 hcounter b3 r3
  have b4' : Bank s4.val (bankValues (D^2) ((D^2)^3) 0 (value D U V N)) := by
    simpa [NatPower.values, v, update36, value_identity] using b4
  have r4' : Scratch s4.val ((D^2)^3) := by simpa [v] using r4
  obtain ⟨s5, e5, b5, r5, f5⟩ := clear_one input tape _ ((D^2)^3) s4 b4' r4'
  obtain ⟨s6, e6, b6, r6, f6⟩ := clear_bank 30 (by omega) (by omega) input tape _ 0 s5 b5 r5
  rw [update30] at b6
  obtain ⟨s7, e7, b7, r7, f7⟩ := clear_bank 31 (by omega) (by omega) input tape _ 0 s6 b6 r6
  rw [update31] at b7
  have fs7 : NatPower.Frame s.val s7.val :=
    ((((NatPower.Frame.of_product fs2).trans f3).trans f4).trans (NatPower.Frame.of_product f5)).trans
      ((NatPower.Frame.of_product f6).trans (NatPower.Frame.of_product f7))
  obtain ⟨t, e8, b8, r8, hv8, hcount8, f8⟩ := export_value input tape _ s7 b7 r7
    (blank_of_eq (fs7.2.2.2.2.2.1 142 (by omega) (Or.inr (by omega)) (by omega)) hout)
  have hc7 : Blank s7.val 141 := blank_of_eq
    (((f5.trans f6).trans f7).2.2.2.2.2.1 141 (by omega) (Or.inr (by omega))) hcount4
  have he := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  simp only [bankValues30, bankValues31, bankValues36] at he hv8
  refine ⟨_, t, ?_, he, hv8, ?_, r8, blank_of_eq hcount8 hc7, (Frame.of_power fs7).trans f8⟩
  · have wb : ((D^2)^3).bits.length ≤ B := hw.initial _ (by simp)
    have wd : (D^2).bits.length ≤ B := hw.initial _ (by simp)
    have wval : (value D U V N).bits.length ≤ B := by simpa [value_identity] using hw.power N le_rfl
    have hbclone : 15*(v 31).bits.length+17 ≤ unitCost B := (small_cost B _ wbase).1
    have hnclone := (small_cost B _ hw.count).1
    have hbclear := (small_cost B _ wb).2.1
    have hdclear := (small_cost B _ wd).2.1
    have hvexport := (small_cost B _ wval).2.2
    dsimp [costCap]
    omega
  · simpa only [update36, bankValues_zero] using b8

theorem compiled_run (l : Layout) (D U V N B : ℕ) (hw : Widths D U V N B)
    (hDpos : 0 < D) (hUpos : 0 < U) (hVpos : 0 < V)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (hcount : Blank s.val 141) (hout : Blank s.val 142) :
    ∃ t : Store,
      (runPriced ((code l).compile.next input tape) (costCap N B+1) s.val).finished =
        some (t.place (code l).size) ∧
      (runPriced ((code l).compile.next input tape) (costCap N B+1) s.val).instructions ≤ costCap N B ∧
      Word t.val 142 (value D U V N) ∧ Bank t.val (fun _ => 0) ∧
      Scratch t.val 0 ∧ Blank t.val 141 ∧ Frame s.val t.val ∧
      0 < value D U V N ∧ (value D U V N).bits.length ≤ B := by
  obtain ⟨cost, t, hcost, he, hv, hb, hs, hc, hf⟩ :=
    executes l D U V N B hw input tape s hbank hready hD hU hV hN hcount hout
  have hr := he.compiled_run (costCap N B+1) (by omega)
  refine ⟨t, hr.1, hr.2 ▸ hcost, hv, hb, hs, hc, hf, value_pos hDpos hUpos hVpos, ?_⟩
  simpa [value_identity] using hw.power N le_rfl

end Maxwell.Cost.CalibrationMatrix.Horner.Denominator
