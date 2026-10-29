import Maxwell.Cost.RationalCompare.Products
import Maxwell.Cost.RationalCompare.Temporary

/-! An executable comparison of nonnegative rational magnitudes. Tapes
30/31 hold a/A and tapes 32/33 hold b/B. The positive denominators are
copied into arithmetic tape 1; both cross-products are computed by fixed
Boolean programs and compared by an actual signed subtraction. Temporary
tapes 35/36 and arithmetic tapes 0 through 3 are cleared on return. -/

namespace Maxwell.Cost.RationalCompare

open Structured RationalAccumulator

def code : Code := .seq productCode temporaryCode

theorem cleared_products (v : ℕ → ℕ) (h35 : v 35 = 0) (h36 : v 36 = 0) :
    cleared (products v) = v := by
  funext i
  by_cases hi35 : i = 35 <;> by_cases hi36 : i = 36 <;>
    simp_all [cleared, products, Function.update_apply]

theorem rational_lt_iff (v : ℕ → ℕ) (hA : 0 < v 31) (hB : 0 < v 33) :
    (v 30 : ℚ) / v 31 < (v 32 : ℚ) / v 33 ↔ v 33 * v 30 < v 31 * v 32 := by
  have hAq : (0 : ℚ) < v 31 := by exact_mod_cast hA
  have hBq : (0 : ℚ) < v 33 := by exact_mod_cast hB
  rw [div_lt_div_iff₀ hAq hBq]
  norm_cast
  simp only [Nat.mul_comm]

/-- One fixed finite machine compares both rational magnitudes and restores
the same bank and scratch invariant required by the next comparison. -/
theorem compare (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 33 → (v i).bits.length ≤ B)
    (hA : 0 < v 31) (hB : 0 < v 33) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 8000 * (B + 2)^2 ∧
      Executes input tape code cost s t ∧
      t.val.registers 35 = decide ((v 30 : ℚ) / v 31 < (v 32 : ℚ) / v 33) ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨pcost, p, hpCost, hp, hpb, hpr, hpf⟩ :=
    cross_products input tape v B hbits hA hB h35 h36 s hbank hready
  obtain ⟨ccost, t, hcCost, hc, hsign, htb, htr, htf⟩ :=
    compare_temporaries input tape (products v) p hpb hpr
  have hprod35 : (products v 35).bits.length ≤ 2 * B := by
    have h31 := hbits 31 (by omega) (by omega)
    have h32 := hbits 32 (by omega) (by omega)
    simpa [products] using (bits_mul_le (v 31) (v 32)).trans
      (show (v 31).bits.length + (v 32).bits.length ≤ 2 * B by omega)
  have hprod36 : (products v 36).bits.length ≤ 2 * B := by
    have h33 := hbits 33 (by omega) (by omega)
    have h30 := hbits 30 (by omega) (by omega)
    simpa [products] using (bits_mul_le (v 33) (v 30)).trans
      (show (v 33).bits.length + (v 30).bits.length ≤ 2 * B by omega)
  refine ⟨pcost + ccost, t, by nlinarith, hp.seq hc, ?_, ?_, htr, (frame_of_bank hpf).trans htf⟩
  · simpa [products, rational_lt_iff v hA hB] using hsign
  · simpa only [cleared_products v h35 h36] using htb

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 33 → (v i).bits.length ≤ B)
    (hA : 0 < v 31) (hB : 0 < v 33) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (8000 * (B + 2)^2 + 1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (8000 * (B + 2)^2 + 1) s.val).instructions ≤
        8000 * (B + 2)^2 ∧
      t.val.registers 35 = decide ((v 30 : ℚ) / v 31 < (v 32 : ℚ) / v 33) ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, hsign, hb, hr, hf⟩ :=
    compare input tape v B hbits hA hB h35 h36 s hbank hready
  have hrun := he.compiled_run (8000 * (B + 2)^2 + 1) (by omega)
  exact ⟨t, hrun.1, hrun.2 ▸ hc, hsign, hb, hr, hf⟩

end Maxwell.Cost.RationalCompare
