import Maxwell.Cost.RationalNormalize.Export
import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.Structured.RegisterFootprint

namespace Maxwell.Cost.WeightedSource.Weight
open Structured RationalAccumulator
set_option maxHeartbeats 1200000

private theorem write_protects (target register : ℕ) (hr : 36≤register) (bits : List Bool) :
    (BinaryPrecision.writeCode target bits).protectsRegister register = true := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [BinaryPrecision.writeCode,PowerOfTwo.appendBit,Code.atom,Code.protectsRegister,
      BitRAM.protectsRegister,List.all_cons,List.all_nil,BitRAMInstruction.protectsRegister,
      Bool.and_true,ih]
    simp only [decide_eq_true_eq]
    omega

private theorem literal_protects (target value register : ℕ) (hr : 36≤register) :
    (BinaryPrecision.literalCode target value).protectsRegister register=true := by
  simp only [BinaryPrecision.literalCode,Code.protectsRegister,write_protects target register hr,Bool.true_and]
  simp [BitRAM.protectsRegister,Rewind.program,BitRAMInstruction.protectsRegister]
  omega

private theorem literal_bank (target value : ℕ) (ht : 30≤target) (ht' : target≤36)
    (input : List Bool) (tape : ℕ→Bool) (v : ℕ→ℕ) (hzero : v target=0)
    (s : Store) (hb : Bank s.val v) (hr : Scratch s.val 0) :
    ∃ t, Executes input tape (BinaryPrecision.literalCode target value) (10*value.bits.length+7) s t ∧
      Bank t.val (Function.update v target value) ∧ Scratch t.val 0 ∧ RationalNormalize.Frame s.val t.val := by
  obtain ⟨t,he,hw,hf⟩ := BinaryPrecision.literal target value input tape s
    ((zero_word_iff_blank _ _).mp (by simpa only [hzero] using hb target ht ht'))
  refine ⟨t,he,?_,?_,?_⟩
  · intro i hi hi'
    by_cases hit : i=target
    · subst i; simpa only [Function.update_self] using hw
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hf.tapes i (by simpa using hit)) (hb i hi hi')
  · exact ⟨blank_of_eq (hf.tapes 0 (by simp;omega)) hr.1,
      word_of_eq (hf.tapes 1 (by simp;omega)) hr.2.1,
      blank_of_eq (hf.tapes 2 (by simp;omega)) hr.2.2.1,
      blank_of_eq (hf.tapes 3 (by simp;omega)) hr.2.2.2⟩
  · exact ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,
      fun i hi => hf.tapes i (by simp only [Finset.mem_singleton];omega),
      fun i hi => he.protectsRegister i (literal_protects target value i hi)⟩

def setupCode (A B : ℕ) : Code := .seq (BinaryPrecision.literalCode 30 A)
  (.seq (BinaryPrecision.literalCode 31 B)
    (.seq (RationalNormalize.oneCode 33) (RationalNormalize.oneCode 34)))

theorem setup (A B : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Bank s.val (fun _=>0)) (hr : Scratch s.val 0) :
    ∃ t, Executes input tape (setupCode A B) (10*(A.bits.length+B.bits.length)+30) s t ∧
      Bank t.val (DyadicSqrt.bank A B 0 1) ∧ Scratch t.val 0 ∧ RationalNormalize.Frame s.val t.val := by
  obtain ⟨a,ea,ba,ra,fa⟩ := literal_bank 30 A (by decide) (by decide) input tape (fun _=>0) rfl s hb hr
  obtain ⟨b,eb,bb,rb,fb⟩ := literal_bank 31 B (by decide) (by decide) input tape
    (Function.update (fun _=>0) 30 A) (by simp) a ba ra
  obtain ⟨c,ec,bc,rc,fc⟩ := RationalNormalize.one 33 (by decide) (by decide) input tape
    (Function.update (Function.update (fun _=>0) 30 A) 31 B) b bb rb
  obtain ⟨t,et,bt,rt,ft⟩ := RationalNormalize.one 34 (by decide) (by decide) input tape
    (Function.update (Function.update (Function.update (fun _=>0) 30 A) 31 B) 33 1) c bc rc
  refine ⟨t,?_,?_,rt,((fa.trans fb).trans fc).trans ft⟩
  · convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | simp; omega
  · intro i hi hi'
    have h := bt i hi hi'
    interval_cases i <;> simpa [DyadicSqrt.bank] using h

end Maxwell.Cost.WeightedSource.Weight
