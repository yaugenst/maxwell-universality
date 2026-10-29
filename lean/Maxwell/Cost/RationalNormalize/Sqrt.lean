import Maxwell.Cost.RationalNormalize.Prepare
import Maxwell.Defect.IntegerNormalization

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator
open Maxwell.Defect.DyadicSqrt.Integer

def sqrtCode : Code := .seq prepareCode
  (.seq (.call (WordTransfer.clone 152 40)) DyadicSqrt.upperCode)

def sqrtBudget (W p : ℕ) : ℕ := 30000*(W+4)^2 + 15*p + 17 +
  (p+1)*(14000000000*(5*W+2*p+5)^2 + 250*(p+5))

def upperNumerator (A C D p : ℕ) : ℕ := lowerNum (A*D^2) (C^2) p + 1

theorem upperNumerator_binding (A C D p : ℕ) (hC : 0 < C) :
    ((upperNumerator A C D p : ℕ) : ℚ) / (2^p : ℕ) =
      Maxwell.Defect.DyadicSqrt.upper (((A*D^2 : ℕ) : ℚ) / (C^2 : ℕ)) p :=
  by simpa only [upperNumerator, Nat.cast_pow, Nat.cast_ofNat] using
    upper_binding (A*D^2) (C^2) p (pow_pos hC 2)

/-- The norm-square and rational upper bound are turned into a dyadic
square root by a fixed finite program. Precision is read from tape 152. -/
theorem sqrt_executes (input : List Bool) (tape : ℕ → Bool)
    (positive negative A C D W p : ℕ)
    (hp : positive.bits.length ≤ W) (hn : negative.bits.length ≤ W)
    (hA : A.bits.length ≤ W) (hC : C.bits.length ≤ W) (hD : D.bits.length ≤ W)
    (s : Store) (hbank : Bank s.val (inputBank positive negative A))
    (hready : Scratch s.val 0) (h40 : Blank s.val 40)
    (hCword : Word s.val 150 C) (hDword : Word s.val 151 D) (hpword : Word s.val 152 p) :
    ∃ cost, ∃ t : Store, cost ≤ sqrtBudget W p ∧
      Executes input tape sqrtCode cost s t ∧
      Bank t.val (DyadicSqrt.bank ((A*D^2)*4^p) (C^2) (upperNumerator A C D p) (2^p)) ∧
      Scratch t.val 0 ∧ Blank t.val 40 ∧ DyadicSqrt.LoopFrame s.val t.val := by
  obtain ⟨c1, a, hc1, e1, b1, r1, f1⟩ :=
    prepare input tape positive negative A C D W hp hn hA hC hD s hbank hready hCword hDword
  obtain ⟨origin, ho⟩ := blank_of_eq (f1.2.2.2.2.2.1 40 (by decide)) h40
  obtain ⟨po, hpw⟩ := word_of_eq (f1.2.2.2.2.2.1 152 (by decide)) hpword
  obtain ⟨b, e2, htapes, f2⟩ := WordCall.clone 152 40 (by decide)
    input tape p.bits po origin a hpw ho
  have keep (i : ℕ) (hi : i ≠ 40) : b.val.tapes i = a.val.tapes i := by
    simp [htapes, hi]
  have bb : Bank b.val (DyadicSqrt.bank (A*D^2) (C^2) 0 1) := by
    intro i hi hi'
    exact word_of_eq (keep i (by omega)) (b1 i hi hi')
  have rb : Scratch b.val 0 :=
    ⟨blank_of_eq (keep 0 (by decide)) r1.1, word_of_eq (keep 1 (by decide)) r1.2.1,
      blank_of_eq (keep 2 (by decide)) r1.2.2.1, blank_of_eq (keep 3 (by decide)) r1.2.2.2⟩
  have fb : DyadicSqrt.LoopFrame a.val b.val :=
    ⟨f2.1, f2.2.1, f2.2.2.1, f2.2.2.2.1, f2.2.2.2.2.1,
      fun i hi => keep i (by omega), fun i hi =>
        f2.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩
  obtain ⟨c3, t, hc3, e3, b3, r3, h3, f3⟩ :=
    DyadicSqrt.upper_executes input tape (A*D^2) (C^2) p origin b bb rb (by simp [htapes])
  refine ⟨c1 + (15*p.bits.length+17+c3), t, ?_,
    e1.seq (e2.seq e3), b3, r3, h3, (f1.toLoop.trans fb).trans f3⟩
  have hDD := bits_mul_le D D
  have hADD := bits_mul_le A (D*D)
  have hCC := bits_mul_le C C
  have hpbits : p.bits.length ≤ p := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have hpoly := DyadicSqrt.upperBudget_le_polynomial (A*D^2) (C^2) p
  have hbase : (A*D^2).bits.length + (C^2).bits.length + 2*p+5 ≤ 5*W+2*p+5 := by
    simpa only [pow_two] using (show (A*(D*D)).bits.length + (C*C).bits.length + 2*p+5 ≤
      5*W+2*p+5 by omega)
  have hpow := Nat.pow_le_pow_left hbase 2
  have hmul := Nat.mul_le_mul_left (p+1) (show
      14000000000*((A*D^2).bits.length+(C^2).bits.length+2*p+5)^2+250*(p+5) ≤
      14000000000*(5*W+2*p+5)^2+250*(p+5) by omega)
  unfold sqrtBudget
  omega

end Maxwell.Cost.RationalNormalize
