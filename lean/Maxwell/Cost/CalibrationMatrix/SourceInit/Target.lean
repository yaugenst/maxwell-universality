import Maxwell.Cost.CalibrationMatrix.SourceInit.AddPair
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)

def targetCode : Code := .seq (.call (TapeOps.clear 104))
  (BankArray.readCanonicalCode 100 102 160 101 104)

/-- Read the sparse record's target from memory into the actual dense cursor. -/
theorem load_target {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (hd : d.Sized B) (j : Fin m) (input : List Bool) (tape : ℕ → Bool)
    (index old : List Bool) (hindex : addressValue index = j.val)
    (hilen : index.length ≤ B) (holen : old.length ≤ B)
    (s : Store) (v : ℕ → ℕ) (hready : Ready s.val v) (hdata : Stored d words s.val)
    (h102 : BankArray.Word s.val 102 index) (h104 : BankArray.Word s.val 104 old) :
    ∃ cost t, cost ≤ 21000*(B+2)^2 ∧ Executes input tape targetCode cost s t ∧
      Ready t.val v ∧ Stored d words t.val ∧
      BankArray.Word t.val 104 (d.records.index j).val.bits ∧
      (d.records.index j).val.bits.length ≤ B ∧ t.val.memory = s.val.memory ∧
      BankArray.FrameExcept 104 s.val t.val := by
  obtain ⟨origin, ho⟩ := h104
  obtain ⟨a, e1, ha, f1⟩ := WordCall.clear 104 input tape old origin s ho
  have keep1 (i : ℕ) (hi : i ≠ 104) : a.val.tapes i = s.val.tapes i := by simp [ha, hi]
  have r1 := hready.of_tapes (fun i hi => keep1 i (by omega))
  have data1 := hdata.of_tapes_memory f1.2.2.1 (fun i hi => keep1 i (by omega))
  have i1 := BankArray.word_of_eq (keep1 102 (by omega)) h102
  have b1 : Blank a.val 104 := ⟨origin+old.length, by simp [ha]⟩
  obtain ⟨c2, t, hc2, e2, ht, hs, h7, hm, _, f2⟩ := BankArray.read_canonical
    100 102 160 101 104 (by omega) (by omega) (by omega) (by omega) (by omega)
    input tape d.width index (d.inputBases 0) d.clock (d.inputWords 0) j
    d.width_nonempty hindex d.clock_length a r1.2.1 r1.2.2 b1 data1.width i1
    (data1.inputBases 0) data1.clock (data1.inputs 0)
  have hf : BankArray.FrameExcept 104 s.val t.val :=
    ⟨f2.1.trans f1.2.1, f2.2.1.trans f1.2.2.2.1,
      f2.2.2.1.trans f1.2.2.2.2.1,
      fun i hi hn => (f2.2.2.2.1 i hi hn).trans (keep1 i hn),
      fun i hi h24 h25 h26 h27 h28 h29 =>
        (f2.2.2.2.2 i hi h24 h25 h26 h27 h28 h29).trans
          (f1.2.2.2.2.2.2 i h26 h27)⟩
  refine ⟨6*old.length+4+c2, t, ?_, e1.seq e2, ⟨?_, hs, h7⟩,
    hdata.of_tapes_memory (hm.trans f1.2.2.1)
      (fun i hi => hf.2.2.2.1 i (Or.inr (by omega)) (by omega)),
    ht, ?_, hm.trans f1.2.2.1, hf⟩
  · have hc := hc2.trans (Affine.read_cost_le d.width index (d.inputBases 0) d.clock B
      hd.1 hd.2.1 hilen (hd.2.2.2.2.1 0) d.clock_length)
    have hsq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
    clear * - hc holen hsq
    omega
  · intro i hi hi'
    exact RationalAccumulator.word_of_eq (hf.2.2.2.1 i (Or.inr (by omega)) (by omega))
      (hready.1 i hi hi')
  · exact ((canonical_length_le ((d.inputWords 0).get j)).trans
      ((hdata.inputs 0).length j).le).trans hd.2.1

end Maxwell.Cost.CalibrationMatrix.SourceInit
