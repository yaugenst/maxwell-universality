import Maxwell.Cost.IntegerNormSquare.Magnitude

namespace Maxwell.Cost.IntegerNormSquare

open Structured RationalAccumulator

/-- One finite Boolean program computes the square of the signed integer
stored as positive and negative natural channels in bank tapes 30 and 31. -/
def code : Code := .seq magnitudeCode (DyadicSqrt.multiplyCode 34 34)

def costBound (a b : ℕ) : ℕ := 6000 * (a.bits.length + b.bits.length + 4)^2

/-- The inputs and every other bank word survive the computation. Register
and external-channel preservation use the signed-arithmetic frame. -/
theorem execute (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) (hzero : v 34 = 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ costBound (v 30) (v 31) ∧
      Executes input tape code cost s t ∧
      Bank t.val (Function.update v 34 ((magnitude (v 30) (v 31))^2)) ∧
      Scratch t.val 0 ∧ DyadicSqrt.Frame s.val t.val := by
  obtain ⟨mcost, m, hmcost, hem, hmb, hmr, hmf⟩ :=
    store_magnitude input tape v s hbank hready hzero
  obtain ⟨pcost, t, hpcost, hep, htb, htr, htf⟩ := DyadicSqrt.multiply 34 34
    (by omega) (by omega) (by omega) (by omega) input tape
    (Function.update v 34 (magnitude (v 30) (v 31))) m hmb hmr
  simp only [Function.update_self] at hpcost htb
  refine ⟨mcost + pcost, t, ?_, hem.seq hep, ?_, htr,
    hmf.trans (DyadicSqrt.frame_of_bank htf)⟩
  · let N := (v 30).bits.length + (v 31).bits.length + 4
    have hlen := magnitude_bits_length_le (v 30) (v 31)
    have hbase : (magnitude (v 30) (v 31)).bits.length +
        (magnitude (v 30) (v 31)).bits.length + 3 ≤ 2 * N := by dsimp [N]; omega
    have hp := hpcost.trans (Nat.mul_le_mul_left 1200 (Nat.pow_le_pow_left hbase 2))
    have hN : N ≤ N^2 := Nat.le_self_pow (by decide) N
    have hscale : 1200 * (2 * N)^2 = 4800 * N^2 := by ring
    rw [hscale] at hp
    change mcost + pcost ≤ 6000 * N^2
    change mcost ≤ 300 * N at hmcost
    omega
  · simpa only [Function.update_idem, ← pow_two] using htb

def inputBank (a b : ℕ) : ℕ → ℕ := fun i => if i = 30 then a else if i = 31 then b else 0

def outputBank (a b : ℕ) : ℕ → ℕ := Function.update (inputBank a b) 34 ((magnitude a b)^2)

/-- The canonical calling convention has the two input channels in tapes
30 and 31, a blank remaining bank, and blank arithmetic scratch. -/
theorem execute_canonical (input : List Bool) (tape : ℕ → Bool) (a b : ℕ)
    (s : Store) (hbank : Bank s.val (inputBank a b)) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ costBound a b ∧
      Executes input tape code cost s t ∧ Bank t.val (outputBank a b) ∧
      Scratch t.val 0 ∧ DyadicSqrt.Frame s.val t.val := by
  simpa only [outputBank, inputBank, show (34 : ℕ) ≠ 30 by omega,
    show (34 : ℕ) ≠ 31 by omega, show (31 : ℕ) ≠ 30 by omega,
    ite_false, ite_true] using execute input tape (inputBank a b) s hbank hready (by
      simp [inputBank])

/-- The finite compiled BitRAM program terminates within the proved
polynomial bound and returns the exact canonical bank state. -/
theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (a b : ℕ)
    (s : Store) (hbank : Bank s.val (inputBank a b)) (hready : Scratch s.val 0) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costBound a b + 1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound a b + 1) s.val).instructions ≤
        costBound a b ∧
      Bank t.val (outputBank a b) ∧ Scratch t.val 0 ∧ DyadicSqrt.Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, hb, hr, hf⟩ := execute_canonical input tape a b s hbank hready
  obtain ⟨hfinish, hcost⟩ := he.compiled_run (costBound a b + 1) (by omega)
  exact ⟨t, hfinish, hcost.le.trans hc, hb, hr, hf⟩

end Maxwell.Cost.IntegerNormSquare
