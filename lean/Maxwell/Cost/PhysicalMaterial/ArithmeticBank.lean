import Maxwell.Cost.RationalAccumulator.Push
import Maxwell.Cost.RationalAccumulator.Reset
import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.WordCall

/-! A fixed positive rational update, using actual canonical-word arithmetic. -/
namespace Maxwell.Cost.PhysicalMaterial.ArithmeticBank
open Structured RationalAccumulator

/-- Arithmetic workspace; caller descriptors are outside this set. -/
def work : Finset ℕ := {0, 1, 2, 3, 30, 31, 32, 33, 34, 35, 36}
abbrev Frame := BinaryPrecision.Frame work

@[simp] private theorem bits64 : (64:ℕ).bits.length = 7 := by decide

def pair (numerator denominator : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (fun _ => 0) 30 numerator) 32 denominator

@[simp] theorem pair_num (a b : ℕ) : pair a b 30 = a := by simp [pair]
@[simp] theorem pair_den (a b : ℕ) : pair a b 32 = b := by simp [pair]

theorem frame_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro i hi
  simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact h.2.2.2.2.2.1 i (by omega) (by omega)

/-- Load a caller word into an empty arithmetic-bank slot, preserving the
source tape including its head. -/
theorem load (source target : ℕ) (hs : 240 ≤ source) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ) (v : ℕ → ℕ) (s : Store)
    (hword : Word s.val source n) (hbank : Bank s.val v) (hzero : v target = 0)
    (hready : Scratch s.val 0) :
    ∃ t, Executes input randomTape (.call (WordTransfer.clone source target))
        (15*n.bits.length+17) s t ∧ Bank t.val (Function.update v target n) ∧
      Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨so, hso⟩ := hword
  have hb := hbank target ht ht'
  rw [hzero, zero_word_iff_blank] at hb
  obtain ⟨targetOrigin, htarget⟩ := hb
  obtain ⟨t, he, hts, hf⟩ := WordCall.clone source target (by omega)
    input randomTape n.bits so targetOrigin s hso htarget
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by simp [hts, hi]
  refine ⟨t, he, ?_, ?_, ?_⟩
  · intro i hi hi'
    by_cases hit : i = target
    · subst i; exact ⟨targetOrigin, by simp [hts]⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (keep i hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (keep 0 (by omega)) hready.1,
      word_of_eq (keep 1 (by omega)) hready.2.1,
      blank_of_eq (keep 2 (by omega)) hready.2.2.1,
      blank_of_eq (keep 3 (by omega)) hready.2.2.2⟩
  · refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
    intro i hi
    exact keep i (by
      intro heq
      subst i
      interval_cases target <;> simp [work] at hi)

/-- Compile-time constant 64 is written, multiplied, and cleared physically. -/
def scaleCode : Code :=
  .seq (BinaryPrecision.literalCode 1 64)
    (.seq (.call (StoredProduct.program 33)) (.call (TapeOps.clear 1)))

theorem scale (input : List Bool) (randomTape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost t, Executes input randomTape scaleCode cost s t ∧
      cost ≤ 500*((v 33).bits.length+9)^2+124 ∧
      Bank t.val (Function.update v 33 (64*v 33)) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨a, ea, ha, fa⟩ := BinaryPrecision.literal 1 64 input randomTape s
    ((zero_word_iff_blank _ _).mp hready.2.1)
  have ba : Bank a.val v := fun i hi _ => word_of_eq (fa.tapes i (by simp; omega)) (hbank i hi ‹_›)
  have ra : Scratch a.val 64 := ⟨blank_of_eq (fa.tapes 0 (by simp)) hready.1, ha,
    blank_of_eq (fa.tapes 2 (by simp)) hready.2.2.1,
    blank_of_eq (fa.tapes 3 (by simp)) hready.2.2.2⟩
  obtain ⟨cost, b, hc, eb, bb, rb, fb⟩ := multiply_bank 33 (by decide) (by decide)
    input randomTape v 64 (by decide) a ba ra
  obtain ⟨t, et, bt, rt, ft⟩ := clear_one input randomTape _ 64 b bb rb
  refine ⟨_, t, ea.seq (eb.seq et), ?_, bt, rt,
    ((fa.mono (by simp [work])).trans (frame_bank fb)).trans (frame_bank ft)⟩
  norm_num at hc ⊢
  nlinarith

def addCode (numSource denSource : ℕ) : Code :=
  .seq (.call (WordTransfer.clone numSource 33))
    (.seq (.call (WordTransfer.clone denSource 34))
      (.seq scaleCode (.seq (.atom (.literal 35 false))
        (.seq pushCode (.seq (.call (TapeOps.clear 33)) (.call (TapeOps.clear 34)))))))

/-- Add 64 times a nonnegative caller rational to a nonnegative bank value. -/
theorem add (numSource denSource : ℕ) (hns : 240 ≤ numSource) (hds : 240 ≤ denSource)
    (input : List Bool) (randomTape : ℕ → Bool) (a b c d B : ℕ)
    (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (hc : c.bits.length ≤ B) (hd : d.bits.length ≤ B) (hbpos : 0 < b) (hdpos : 0 < d)
    (s : Store) (hbank : Bank s.val (pair a b)) (hready : Scratch s.val 0)
    (hnum : Word s.val numSource c) (hden : Word s.val denSource d) :
    ∃ cost t, Executes input randomTape (addCode numSource denSource) cost s t ∧
      cost ≤ 15000*(B+10)^2 ∧ Bank t.val (pair (b*(64*c)+d*a) (d*b)) ∧
      Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨s1, e1, b1, r1, f1⟩ := load numSource 33 hns (by decide) (by decide)
    input randomTape c (pair a b) s hnum hbank (by simp [pair]) hready
  have hden1 : Word s1.val denSource d := word_of_eq (f1.tapes denSource (by simp [work]; omega)) hden
  let v1 := Function.update (pair a b) 33 c
  obtain ⟨s2, e2, b2, r2, f2⟩ := load denSource 34 hds (by decide) (by decide)
    input randomTape d v1 s1 hden1 b1 (by simp [v1, pair]) r1
  let v2 := Function.update v1 34 d
  obtain ⟨sc, s3, e3, hc3, b3, r3, f3⟩ := scale input randomTape v2 s2 b2 r2
  let v3 := Function.update v2 33 (64*c)
  have b3' : Bank s3.val v3 := by simpa [v3, v2, v1] using b3
  let s4 := Store.ofState (s3.val.setRegister 35 false)
  have b4 : Bank s4.val v3 := b3'
  have r4 : Scratch s4.val 0 := r3
  have f4 : Frame s3.val s4.val := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hbits : ∀ i, 30 ≤ i → i ≤ 36 → (v3 i).bits.length ≤ B+7 := by
    have hmul : (64*c).bits.length ≤ B+7 := (bits_mul_le 64 c).trans (by norm_num; omega)
    intro i hi hi'
    interval_cases i <;> simp [v3, v2, v1, pair] <;> omega
  obtain ⟨pc, s5, hpc, e5, b5, r5, f5⟩ := push input randomTape v3 (B+7) false hbits
    (by simpa [v3, v2, v1, pair] using hbpos)
    (by simpa [v3, v2, v1] using hdpos) (by simp [v3, v2, v1, pair]) s4 b4 r4
    (by simp [s4, Store.ofState, BitRAMState.setRegister])
  obtain ⟨s6, e6, b6, r6, f6⟩ := clear_bank 33 (by decide) (by decide)
    input randomTape (pushed v3 false) 0 s5 b5 r5
  obtain ⟨t, e7, b7, r7, f7⟩ := clear_bank 34 (by decide) (by decide)
    input randomTape (Function.update (pushed v3 false) 33 0) 0 s6 b6 r6
  have heq : Function.update (Function.update (pushed v3 false) 33 0) 34 0 =
      pair (b*(64*c)+d*a) (d*b) := by
    ext i
    simp [pushed, prepared, selected, v3, v2, v1, pair, Function.update_apply]
    split_ifs <;> omega
  refine ⟨_, t, e1.seq (e2.seq (e3.seq ((Executes.literal input randomTape s3 35 false).seq
      (e5.seq (e6.seq e7))))), ?_, heq ▸ b7, r7,
    (((((f1.trans f2).trans f3).trans f4).trans (frame_bank f5)).trans
      (frame_bank f6)).trans (frame_bank f7)⟩
  have hmul : (64*c).bits.length ≤ B+7 := (bits_mul_le 64 c).trans (by norm_num; omega)
  simp only [v2, v1, Function.update_apply] at hc3
  norm_num at hc3
  simp only [pushed, prepared, selected, v3, v2, v1, Function.update_apply]
  norm_num
  have hsc : sc ≤ 500*(B+9)^2+124 := hc3.trans (by gcongr)
  nlinarith

theorem numerator_bits (a b c d B : ℕ) (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (hc : c.bits.length ≤ B) (hd : d.bits.length ≤ B) :
    (b*(64*c)+d*a).bits.length ≤ 2*B+8 := by
  have h64 : (64*c).bits.length ≤ B+7 := (bits_mul_le 64 c).trans (by norm_num; omega)
  have hleft := bits_mul_le b (64*c)
  have hright := bits_mul_le d a
  have hsum := bits_add_le (b*(64*c)) (d*a)
  omega

theorem denominator_bits (b d B : ℕ) (hb : b.bits.length ≤ B) (hd : d.bits.length ≤ B) :
    (d*b).bits.length ≤ 2*B := (bits_mul_le d b).trans (by omega)

theorem value (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    ((b*(64*c)+d*a : ℕ) : ℚ) / (d*b) = (a:ℚ)/b+64*((c:ℚ)/d) := by
  have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp
  ring

end Maxwell.Cost.PhysicalMaterial.ArithmeticBank
