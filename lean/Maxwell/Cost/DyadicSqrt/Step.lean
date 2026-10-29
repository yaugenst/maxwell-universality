import Maxwell.Cost.DyadicSqrt.Operations
import Maxwell.Defect.DyadicSqrtInteger

namespace Maxwell.Cost.DyadicSqrt

open Structured RationalAccumulator

def bank (A B L P : ℕ) (i : ℕ) : ℕ :=
  if i = 30 then A else if i = 31 then B else if i = 32 then L else
    if i = 33 then P else if i = 34 then 1 else 0

def prepare : List Operation := [
  .add 0 0, .add 0 0, .add 2 2, .add 3 3,
  .copy 2 5 (by decide), .add 4 5, .multiply 5 5, .multiply 1 5,
  .copy 0 6 (by decide)]

def prepared (A B L P : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (bank (4 * A) B (2 * L) (2 * P))
    35 (B * (2 * L + 1)^2)) 36 (4 * A)

theorem prepare_value (A B L P : ℕ) :
    operationsValue prepare (bank A B L P) = prepared A B L P := by
  funext i
  by_cases h30 : i = 30
  · subst i; norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]; ring
  by_cases h31 : i = 31
  · subst i; norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]
  by_cases h32 : i = 32
  · subst i; norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]; omega
  by_cases h33 : i = 33
  · subst i; norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]; omega
  by_cases h34 : i = 34
  · subst i; norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]
  by_cases h35 : i = 35
  · subst i
    norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]
    left
    change (1 + (L + L)) * (1 + (L + L)) = (2 * L + 1)^2
    ring
  by_cases h36 : i = 36
  · subst i
    norm_num [operationsValue, prepare, Operation.value, bankIndex, bank, prepared]
    change A + A + (A + A) = 4 * A
    omega
  simp [operationsValue, prepare, Operation.value, bankIndex, bank, prepared,
    h30, h31, h32, h33, h34, h35, h36]

theorem cleared_prepared (A B L P : ℕ) :
    RationalCompare.cleared (prepared A B L P) = bank (4 * A) B (2 * L) (2 * P) := by
  funext i
  by_cases h35 : i = 35 <;> by_cases h36 : i = 36 <;>
    simp_all [RationalCompare.cleared, prepared, bank, Function.update_apply]

theorem add_accept (A B L P : ℕ) :
    Function.update (bank (4 * A) B (2 * L) (2 * P)) 32
      ((bank (4 * A) B (2 * L) (2 * P)) 34 +
        (bank (4 * A) B (2 * L) (2 * P)) 32) =
      bank (4 * A) B (2 * L + 1) (2 * P) := by
  funext i
  by_cases h : i = 32
  · subst i; simp [bank, Nat.add_comm]
  · simp only [Function.update_of_ne h]
    simp [bank, h]

def nextLower (A B L : ℕ) : ℕ :=
  if B * (2 * L + 1)^2 ≤ 4 * A then 2 * L + 1 else 2 * L

def cycle : Code := .seq (operationsCode prepare)
  (.seq RationalCompare.temporaryCode (.branch 35 .skip (addCode 34 32)))

def cycleBudget (W : ℕ) : ℕ :=
  10 * 5000 * (2^9 * (W + 4))^2 + 300 * (4 * W + 10) + 230 * (W + 6) + 2

theorem bank_width (A B L P W : ℕ)
    (hA : A.bits.length ≤ W) (hB : B.bits.length ≤ W)
    (hL : L.bits.length ≤ W) (hP : P.bits.length ≤ W) (hW : 1 ≤ W) :
    Width (bank A B L P) W := by
  intro i hi hi'
  interval_cases i <;> simp [bank] <;> assumption

theorem cycle_executes (input : List Bool) (tape : ℕ → Bool) (A B L P W : ℕ)
    (hA : A.bits.length ≤ W) (hB : B.bits.length ≤ W)
    (hL : L.bits.length ≤ W) (hP : P.bits.length ≤ W) (hW : 1 ≤ W)
    (s : Store) (hbank : Bank s.val (bank A B L P)) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ cycleBudget W ∧ Executes input tape cycle cost s t ∧
      Bank t.val (bank (4 * A) B (nextLower A B L) (2 * P)) ∧
      Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨pcost, p, hpc, ep, bp, rp, fp⟩ := operations_executes prepare input tape
    (bank A B L P) W (bank_width A B L P W hA hB hL hP hW) s hbank hready
  rw [prepare_value] at bp
  have hpCost : pcost ≤ 10 * 5000 * (2^9 * (W + 4))^2 := by simpa [prepare] using hpc
  obtain ⟨ccost, c, hcc, ec, hcSign, bc, rc, fc⟩ :=
    RationalCompare.compare_temporaries input tape (prepared A B L P) p bp rp
  rw [cleared_prepared] at bc
  have hsign : c.val.registers 35 = decide (4 * A < B * (2 * L + 1)^2) := by
    simpa [prepared] using hcSign
  have htwo : (2 * L).bits.length ≤ W + 1 := by
    have h := bits_add_le L L
    have he : L + L = 2 * L := by omega
    rw [he] at h
    omega
  have htrial : (2 * L + 1).bits.length ≤ W + 2 := by
    have h := bits_add_le (2 * L) 1
    rw [show (1 : ℕ).bits.length = 1 from rfl] at h
    omega
  have hcomparison : (B * (2 * L + 1)^2).bits.length ≤ 3 * W + 4 := by
    have hs := bits_mul_le (2 * L + 1) (2 * L + 1)
    have hm := bits_mul_le B ((2 * L + 1)^2)
    rw [← pow_two] at hs
    omega
  have hfour : (4 * A).bits.length ≤ W + 2 := by
    have htwoA := bits_add_le A A
    have hfourA := bits_add_le (A + A) (A + A)
    have he : (A + A) + (A + A) = 4 * A := by omega
    rw [he] at hfourA
    omega
  have hcCost : ccost ≤ 300 * (4 * W + 10) := by
    simp only [prepared, Function.update_self,
      Function.update_of_ne (show 35 ≠ 36 by decide)] at hcc
    omega
  by_cases htest : B * (2 * L + 1)^2 ≤ 4 * A
  · obtain ⟨acost, t, hac, ea, ba, ra, fa⟩ := add 34 32 (by decide) (by decide)
      (by decide) (by decide) input tape (bank (4 * A) B (2 * L) (2 * P)) c bc rc
    have haCost : acost ≤ 230 * (W + 6) := by
      simp only [bank, ↓reduceIte] at hac
      norm_num at hac
      omega
    refine ⟨pcost + (ccost + (1 + acost)), t, by unfold cycleBudget; omega,
      ep.seq (ec.seq (Executes.no (by simp [hsign, Nat.not_lt.mpr htest]) ea)), ?_, ra,
      ((frame_of_bank fp).trans fc).trans (frame_of_bank fa)⟩
    rw [add_accept] at ba
    simpa [nextLower, htest] using ba
  · refine ⟨pcost + (ccost + (1 + 1)), c, by unfold cycleBudget; omega,
      ep.seq (ec.seq (Executes.yes (by simp [hsign, Nat.lt_of_not_ge htest]) (Executes.skip c))),
      ?_, rc, (frame_of_bank fp).trans fc⟩
    simpa [nextLower, htest] using bc

end Maxwell.Cost.DyadicSqrt
