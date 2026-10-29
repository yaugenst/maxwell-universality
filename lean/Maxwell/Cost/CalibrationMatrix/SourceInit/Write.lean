import Maxwell.Cost.CalibrationMatrix.SourceInit.Data

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)

def writtenWords {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (row : Fin n) (positive negative : ℕ) : Fin 4 → Vector (List Bool) n :=
  let p := FixedWidth.bits (addressValue d.width) positive.bits
  let q := FixedWidth.bits (addressValue d.width) negative.bits
  setPair (setPair words 0 1 row p q) 2 3 row p q

def writeCode : Code := .seq (Affine.writePairCode 120 121)
  (.seq (Affine.writePairCode 122 123) clearDotCode)

/-- Write the same accumulated signed pair to the two independent Horner
source/state array pairs, then reclaim the arithmetic bank. -/
theorem write_four {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (hd : d.Sized B) (row : Fin n) (positive negative : ℕ)
    (hpfit : positive.bits.length ≤ addressValue d.width)
    (hnfit : negative.bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hindex : addressValue index = row.val) (hilen : index.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues positive negative))
    (hdata : Stored d words s.val) (h104 : BankArray.Word s.val 104 index) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 170000*(B+2)^2 ∧ Executes input tape writeCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧
      Stored d (writtenWords d words row positive negative) t.val ∧
      RowFrame s.val t.val ∧ Outside d s.val t.val := by
  let p := FixedWidth.bits (addressValue d.width) positive.bits
  let q := FixedWidth.bits (addressValue d.width) negative.bits
  obtain ⟨c1, a, hc1, e1, r1, h137, hm1, hp1, hn1, f1⟩ := Affine.write_pair 120 121
    (by omega) (by omega) input tape d.width index (d.outputBases 0) (d.outputBases 1) d.clock
    (words 0) (words 1) row positive negative d.width_nonempty hindex d.clock_length d.width_positive
    hpfit hnfit (d.output_separated 0 1 (by decide)) s hready h37 hdata.width h104
    (hdata.outputBases 0) (hdata.outputBases 1) hdata.clock (hdata.outputs 0) (hdata.outputs 1)
  have data1 := hdata.after_pair 0 1 (by decide) row p q (FixedWidth.bits_length _ _)
    (FixedWidth.bits_length _ _) f1 hm1 hp1 hn1
  have index1 := BankArray.word_of_eq
    (f1.2.2.2.1 104 (Or.inr (by omega)) (by omega) (by omega) (by omega)) h104
  let words1 := setPair words 0 1 row p q
  obtain ⟨c2, b, hc2, e2, r2, h237, hm2, hp2, hn2, f2⟩ := Affine.write_pair 122 123
    (by omega) (by omega) input tape d.width index (d.outputBases 2) (d.outputBases 3) d.clock
    (words1 2) (words1 3) row positive negative d.width_nonempty hindex d.clock_length d.width_positive
    hpfit hnfit (d.output_separated 2 3 (by decide)) a r1 h137 data1.width index1
    (data1.outputBases 2) (data1.outputBases 3) data1.clock (data1.outputs 2) (data1.outputs 3)
  have data2 := data1.after_pair 2 3 (by decide) row p q (FixedWidth.bits_length _ _)
    (FixedWidth.bits_length _ _) f2 hm2 hp2 hn2
  obtain ⟨t, e3, r3, h337, hm3, f3⟩ := clear_dot input tape positive negative b r2 h237
  have data3 := data2.of_tapes_memory hm3 (fun i hi =>
    f3.2.2.2.1 i (Or.inr (by omega)) (by omega) (by omega) (by omega))
  have outside1 := Outside.of_pair (d := d) 0 1 row p q (FixedWidth.bits_length _ _)
    (FixedWidth.bits_length _ _) hm1
  have outside2 := Outside.of_pair (d := d) 2 3 row p q (FixedWidth.bits_length _ _)
    (FixedWidth.bits_length _ _) hm2
  refine ⟨c1+(c2+(6*(positive.bits.length+negative.bits.length)+8)), t, ?_,
    e1.seq (e2.seq e3), r3, h337, data3, (f1.trans f2).trans f3,
    (outside1.trans outside2).trans (Outside.of_memory hm3)⟩
  have h1 := hc1.trans (writeRow_cost_le d.width index (d.outputBases 0) (d.outputBases 1)
    positive negative B hd.1 hilen (hd.2.2.2.2.2 0) (hd.2.2.2.2.2 1) hd.2.1)
  have h2 := hc2.trans (writeRow_cost_le d.width index (d.outputBases 2) (d.outputBases 3)
    positive negative B hd.1 hilen (hd.2.2.2.2.2 2) (hd.2.2.2.2.2 3) hd.2.1)
  have hp := hpfit.trans hd.2.1
  have hn := hnfit.trans hd.2.1
  have hsq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
  clear * - h1 h2 hp hn hsq
  omega

end Maxwell.Cost.CalibrationMatrix.SourceInit
