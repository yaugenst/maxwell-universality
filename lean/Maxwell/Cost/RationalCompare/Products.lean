import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.RationalCompare

open Structured RationalAccumulator

def productCode : Code :=
  .seq (.call (WordTransfer.clone 31 1))
    (.seq (.call (WordTransfer.clone 32 35))
      (.seq (.call (StoredProduct.program 35))
        (.seq (.call (TapeOps.clear 1))
          (.seq (.call (WordTransfer.clone 33 1))
            (.seq (.call (WordTransfer.clone 30 36))
              (.seq (.call (StoredProduct.program 36)) (.call (TapeOps.clear 1))))))))

def products (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 35 (v 31 * v 32)) 36 (v 33 * v 30)

theorem cross_products (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 33 → (v i).bits.length ≤ B)
    (hA : 0 < v 31) (hB : 0 < v 33) (h35 : v 35 = 0) (h36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 6000 * (B + 2)^2 ∧
      Executes input tape productCode cost s t ∧
      Bank t.val (products v) ∧ Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, hea, hba, hra, hfa⟩ := clone_to_one 31 (by decide) (by decide)
    input tape v s hbank hready
  obtain ⟨b, heb, hbb, hrb, hfb⟩ := clone_bank 32 35 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v (v 31) a hba h35 hra
  let v1 := Function.update v 35 (v 32)
  obtain ⟨cCost, c, hcCost, hec, hbc, hrc, hfc⟩ := multiply_bank 35 (by decide) (by decide)
    input tape v1 (v 31) hA b hbb hrb
  let v2 := Function.update v1 35 (v 31 * v1 35)
  obtain ⟨d, hed, hbd, hrd, hfd⟩ := clear_one input tape v2 (v 31) c hbc hrc
  obtain ⟨e, hee, hbe, hre, hfe⟩ := clone_to_one 33 (by decide) (by decide)
    input tape v2 d hbd hrd
  have hv233 : v2 33 = v 33 := by simp [v2, v1]
  rw [hv233] at hre
  obtain ⟨f, hef, hbf, hrf, hff⟩ := clone_bank 30 36 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v2 (v 33) e hbe
    (by simpa [v2, v1] using h36) hre
  let v3 := Function.update v2 36 (v2 30)
  obtain ⟨gCost, g, hgCost, heg, hbg, hrg, hfg⟩ := multiply_bank 36 (by decide) (by decide)
    input tape v3 (v 33) hB f hbf hrf
  let v4 := Function.update v3 36 (v 33 * v3 36)
  obtain ⟨t, het, hbt, hrt, hft⟩ := clear_one input tape v4 (v 33) g hbg hrg
  have hv4 : v4 = products v := by
    ext i
    simp [v4, v3, v2, v1, products, Function.update_apply]
  refine ⟨(15*(v 31).bits.length+17) + ((15*(v 32).bits.length+17) +
      (cCost + ((6*(v 31).bits.length+4) + ((15*(v2 33).bits.length+17) +
      ((15*(v2 30).bits.length+17) + (gCost + (6*(v 33).bits.length+4))))))), t, ?_,
    hea.seq (heb.seq (hec.seq (hed.seq (hee.seq (hef.seq (heg.seq het)))))),
    hv4 ▸ hbt, hrt, ((((((hfa.trans hfb).trans hfc).trans hfd).trans hfe).trans hff).trans hfg).trans hft⟩
  have h30 := hbits 30 (by decide) (by decide)
  have h31 := hbits 31 (by decide) (by decide)
  have h32 := hbits 32 (by decide) (by decide)
  have h33 := hbits 33 (by decide) (by decide)
  simp only [v1, v2, v3, Function.update_self,
    Function.update_of_ne (show 30 ≠ 35 by decide),
    Function.update_of_ne (show 33 ≠ 35 by decide)] at hcCost hgCost ⊢
  have hleft : ((v 31).bits.length + (v 32).bits.length + 2)^2 ≤ (2*B+2)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hright : ((v 33).bits.length + (v 30).bits.length + 2)^2 ≤ (2*B+2)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  nlinarith

end Maxwell.Cost.RationalCompare
