import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.RationalAccumulator

open Structured

/-- The actual positive-denominator cross products for one rational update.
The term magnitude and denominator remain on tapes 33 and 34. -/
def prepareCode : Code :=
  .seq (.call (WordTransfer.clone 32 1))
    (.seq (.call (WordTransfer.clone 33 36))
      (.seq (.call (StoredProduct.program 36))
        (.seq (.call (TapeOps.clear 1))
          (.seq (.call (WordTransfer.clone 34 1))
            (.seq (.call (StoredProduct.program 30))
              (.seq (.call (StoredProduct.program 31))
                (.seq (.call (StoredProduct.program 32)) (.call (TapeOps.clear 1)))))))))

def prepared (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update v 36 (v 32 * v 33))
    30 (v 34 * v 30)) 31 (v 34 * v 31)) 32 (v 34 * v 32)

theorem prepare (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 36 → (v i).bits.length ≤ B)
    (hd : 0 < v 32) (htermD : 0 < v 34) (hzero : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 10000 * (B + 2)^2 ∧
      Executes input tape prepareCode cost s t ∧
      Bank t.val (prepared v) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨s1, h1, hb1, hr1, hf1⟩ := clone_to_one 32 (by decide) (by decide)
    input tape v s hbank hready
  obtain ⟨s2, h2, hb2, hr2, hf2⟩ := clone_bank 33 36 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v (v 32) s1 hb1 hzero hr1
  let v1 := Function.update v 36 (v 33)
  obtain ⟨c3, s3, hc3, h3, hb3, hr3, hf3⟩ := multiply_bank 36 (by decide) (by decide)
    input tape v1 (v 32) hd s2 hb2 hr2
  let v2 := Function.update v1 36 (v 32 * v1 36)
  obtain ⟨s4, h4, hb4, hr4, hf4⟩ := clear_one input tape v2 (v 32) s3 hb3 hr3
  have hv234 : v2 34 = v 34 := by simp [v2, v1]
  obtain ⟨s5, h5, hb5, hr5, hf5⟩ := clone_to_one 34 (by decide) (by decide)
    input tape v2 s4 hb4 hr4
  rw [hv234] at hr5
  obtain ⟨c6, s6, hc6, h6, hb6, hr6, hf6⟩ := multiply_bank 30 (by decide) (by decide)
    input tape v2 (v 34) htermD s5 hb5 hr5
  let v3 := Function.update v2 30 (v 34 * v2 30)
  obtain ⟨c7, s7, hc7, h7, hb7, hr7, hf7⟩ := multiply_bank 31 (by decide) (by decide)
    input tape v3 (v 34) htermD s6 hb6 hr6
  let v4 := Function.update v3 31 (v 34 * v3 31)
  obtain ⟨c8, s8, hc8, h8, hb8, hr8, hf8⟩ := multiply_bank 32 (by decide) (by decide)
    input tape v4 (v 34) htermD s7 hb7 hr7
  let v5 := Function.update v4 32 (v 34 * v4 32)
  obtain ⟨s9, h9, hb9, hr9, hf9⟩ := clear_one input tape v5 (v 34) s8 hb8 hr8
  have hv5 : v5 = prepared v := by
    ext i
    simp [v5, v4, v3, v2, v1, prepared, Function.update_apply]
  refine ⟨(15 * (v 32).bits.length + 17) + ((15 * (v 33).bits.length + 17) +
      (c3 + ((6 * (v 32).bits.length + 4) + ((15 * (v2 34).bits.length + 17) +
      (c6 + (c7 + (c8 + (6 * (v 34).bits.length + 4)))))))),
    s9, ?_, Executes.seq h1 (Executes.seq h2 (Executes.seq h3 (Executes.seq h4
      (Executes.seq h5 (Executes.seq h6 (Executes.seq h7 (Executes.seq h8 h9))))))),
    hv5 ▸ hb9, hr9,
    (((((((hf1.trans hf2).trans hf3).trans hf4).trans hf5).trans hf6).trans hf7).trans hf8).trans hf9⟩
  have h30 := hbits 30 (by decide) (by decide)
  have h31 := hbits 31 (by decide) (by decide)
  have h32 := hbits 32 (by decide) (by decide)
  have h33 := hbits 33 (by decide) (by decide)
  have h34 := hbits 34 (by decide) (by decide)
  simp only [v1, v2, v3, v4, Function.update_self, Function.update_of_ne (show 30 ≠ 36 by decide),
    Function.update_of_ne (show 31 ≠ 30 by decide), Function.update_of_ne (show 31 ≠ 36 by decide),
    Function.update_of_ne (show 32 ≠ 31 by decide), Function.update_of_ne (show 32 ≠ 30 by decide),
    Function.update_of_ne (show 32 ≠ 36 by decide)] at hc3 hc6 hc7 hc8
  rw [hv234]
  have h3bound : c3 ≤ 500 * (2 * B + 2)^2 + 1 := hc3.trans (by gcongr; omega)
  have h6bound : c6 ≤ 500 * (2 * B + 2)^2 + 1 := hc6.trans (by gcongr; omega)
  have h7bound : c7 ≤ 500 * (2 * B + 2)^2 + 1 := hc7.trans (by gcongr; omega)
  have h8bound : c8 ≤ 500 * (2 * B + 2)^2 + 1 := hc8.trans (by gcongr; omega)
  nlinarith

end Maxwell.Cost.RationalAccumulator
