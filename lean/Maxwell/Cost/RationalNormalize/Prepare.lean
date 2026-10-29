import Maxwell.Cost.RationalNormalize.Bank

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator

def inputBank (positive negative A : ℕ) (i : ℕ) : ℕ :=
  if i = 30 then positive else if i = 31 then negative else if i = 34 then A else 0

def prepareCode : Code :=
  .seq (DyadicSqrt.Operation.copy 4 0 (by decide)).code
    (.seq (loadCode 151 34)
      (.seq (DyadicSqrt.multiplyCode 34 34)
        (.seq (DyadicSqrt.multiplyCode 34 30)
          (.seq (loadCode 150 31)
            (.seq (DyadicSqrt.multiplyCode 31 31)
              (.seq (oneCode 33) (oneCode 34)))))))

theorem prepare (input : List Bool) (tape : ℕ → Bool)
    (positive negative A C D W : ℕ)
    (hp : positive.bits.length ≤ W) (hn : negative.bits.length ≤ W)
    (hA : A.bits.length ≤ W) (hC : C.bits.length ≤ W) (hD : D.bits.length ≤ W)
    (s : Store) (hbank : Bank s.val (inputBank positive negative A)) (hready : Scratch s.val 0)
    (hCword : Word s.val 150 C) (hDword : Word s.val 151 D) :
    ∃ cost, ∃ t : Store, cost ≤ 30000 * (W + 4)^2 ∧
      Executes input tape prepareCode cost s t ∧
      Bank t.val (DyadicSqrt.bank (A * D^2) (C^2) 0 1) ∧
      Scratch t.val 0 ∧ Frame s.val t.val := by
  have hwidth : DyadicSqrt.Width (inputBank positive negative A) W := by
    intro i hi hi'
    interval_cases i <;> simp [inputBank] <;> assumption
  obtain ⟨c1, a, hc1, e1, b1, r1, f1⟩ :=
    (DyadicSqrt.Operation.copy 4 0 (by decide)).executes input tape
      (inputBank positive negative A) W hwidth s hbank hready
  let v1 := Function.update (inputBank positive negative A) 30 A
  change Bank a.val v1 at b1
  have haD : Word a.val 151 D := word_of_eq
    (f1.2.2.2.2.2.1 151 (by decide) (by decide)) hDword
  obtain ⟨b, e2, b2, r2, f2⟩ := load 151 34 (by decide) (by decide) (by decide)
    input tape v1 D a b1 r1 haD
  let v2 := Function.update v1 34 D
  obtain ⟨c3, c, hc3, e3, b3, r3, f3⟩ := DyadicSqrt.multiply 34 34 (by decide) (by decide)
    (by decide) (by decide) input tape v2 b b2 r2
  let v3 := Function.update v2 34 (D * D)
  change Bank c.val v3 at b3
  obtain ⟨c4, d, hc4, e4, b4, r4, f4⟩ := DyadicSqrt.multiply 34 30 (by decide) (by decide)
    (by decide) (by decide) input tape v3 c b3 r3
  let v4 := Function.update v3 30 ((D * D) * A)
  change Bank d.val v4 at b4
  have fstart : Frame s.val d.val :=
    (((frame_of_bank f1).trans f2).trans (frame_of_bank f3)).trans (frame_of_bank f4)
  have hdC : Word d.val 150 C := word_of_eq (fstart.2.2.2.2.2.1 150 (by decide)) hCword
  obtain ⟨e, e5, b5, r5, f5⟩ := load 150 31 (by decide) (by decide) (by decide)
    input tape v4 C d b4 r4 hdC
  let v5 := Function.update v4 31 C
  obtain ⟨c6, f, hc6, e6, b6, r6, f6⟩ := DyadicSqrt.multiply 31 31 (by decide) (by decide)
    (by decide) (by decide) input tape v5 e b5 r5
  let v6 := Function.update v5 31 (C * C)
  change Bank f.val v6 at b6
  obtain ⟨g, e7, b7, r7, f7⟩ := one 33 (by decide) (by decide) input tape v6 f b6 r6
  let v7 := Function.update v6 33 1
  obtain ⟨t, e8, b8, r8, f8⟩ := one 34 (by decide) (by decide) input tape v7 g b7 r7
  let v8 := Function.update v7 34 1
  have hvalues : v8 = DyadicSqrt.bank (A * D^2) (C^2) 0 1 := by
    funext i
    by_cases h30 : i = 30
    · subst i; simp [v8, v7, v6, v5, v4, v3, v2, v1, DyadicSqrt.bank]; ring
    by_cases h31 : i = 31
    · subst i; simp [v8, v7, v6, v5, v4, v3, v2, v1, DyadicSqrt.bank, pow_two]
    by_cases h32 : i = 32
    · subst i; simp [v8, v7, v6, v5, v4, v3, v2, v1, inputBank, DyadicSqrt.bank]
    by_cases h33 : i = 33
    · subst i; simp [v8, v7, v6, v5, v4, v3, v2, v1, DyadicSqrt.bank]
    by_cases h34 : i = 34
    · subst i; simp [v8, v7, v6, v5, v4, v3, v2, v1, DyadicSqrt.bank]
    simp [v8, v7, v6, v5, v4, v3, v2, v1, inputBank, DyadicSqrt.bank,
      h30, h31, h32, h33, h34]
  refine ⟨c1 + ((6 * (v1 34).bits.length + 15 * D.bits.length + 21) +
    (c3 + (c4 + ((6 * (v4 31).bits.length + 15 * C.bits.length + 21) +
    (c6 + ((6 * (v6 33).bits.length + 8) + (6 * (v7 34).bits.length + 8))))))), t, ?_,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8)))))),
    hvalues ▸ b8, r8,
    (((fstart.trans f5).trans (frame_of_bank f6)).trans f7).trans f8⟩
  change c3 ≤ 1200 * (D.bits.length + D.bits.length + 3)^2 at hc3
  change c4 ≤ 1200 * ((D * D).bits.length + A.bits.length + 3)^2 at hc4
  change c6 ≤ 1200 * (C.bits.length + C.bits.length + 3)^2 at hc6
  have hDD := bits_mul_le D D
  have h3 : c3 ≤ 4800 * (W+4)^2 := by
    have hh := Nat.pow_le_pow_left (show D.bits.length + D.bits.length + 3 ≤ 2*(W+4) by omega) 2
    nlinarith only [hc3, hh]
  have h4 : c4 ≤ 10800 * (W+4)^2 := by
    have hh := Nat.pow_le_pow_left (show (D*D).bits.length + A.bits.length + 3 ≤ 3*(W+4) by omega) 2
    nlinarith only [hc4, hh]
  have h6 : c6 ≤ 4800 * (W+4)^2 := by
    have hh := Nat.pow_le_pow_left (show C.bits.length + C.bits.length + 3 ≤ 2*(W+4) by omega) 2
    nlinarith only [hc6, hh]
  change c1 + ((6*A.bits.length + 15*D.bits.length+21) +
    (c3 + (c4 + ((6*negative.bits.length+15*C.bits.length+21) +
      (c6 + ((6*(0:ℕ).bits.length+8)+(6*(D*D).bits.length+8))))))) ≤ _
  rw [show (0:ℕ).bits.length = 0 from rfl]
  have hsq : W+4 ≤ (W+4)^2 := Nat.le_self_pow (by decide) _
  omega

end Maxwell.Cost.RationalNormalize
