import Maxwell.Cost.CalibrationMatrix.Product
import Maxwell.Cost.RationalAccumulator.Add
import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.CalibrationMatrix

open Structured RationalAccumulator

def macCode (source scalar target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 36))
    (.seq (.call (WordTransfer.clone scalar 1))
      (.seq (productCode 36) (.seq (.call (TapeOps.clear 1))
        (.seq (.call (WordTransfer.move 36 1))
          (.seq (addCode target) (.call (TapeOps.clear 1)))))))

def accumulated (v : ℕ → ℕ) (source scalar target : ℕ) : ℕ → ℕ :=
  Function.update v target (v scalar*v source+v target)

/-- One unsigned product is accumulated into either signed channel. All
four operand tapes survive, and temporary tape36 and scalar tape1 are empty. -/
theorem mac (source scalar target : ℕ) (hs : 32 ≤ source) (hs' : source ≤ 33)
    (hx : 34 ≤ scalar) (hx' : scalar ≤ 35) (ht : 30 ≤ target) (ht' : target ≤ 31)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) (hz : v 36 = 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 5000*((v source).bits.length+(v scalar).bits.length+(v target).bits.length+3)^2 ∧
      Executes input tape (macCode source scalar target) cost s t ∧
      Bank t.val (accumulated v source scalar target) ∧ Scratch t.val 0 ∧
      RationalAccumulator.Frame s.val t.val := by
  let v1 := Function.update v 36 (v source)
  let v2 := Function.update v1 36 (v scalar*v source)
  let v3 := Function.update v2 36 0
  have hsourceNe : source ≠ 36 := by omega
  have hscalarNe : scalar ≠ 36 := by omega
  have htargetNe : target ≠ 36 := by omega
  obtain ⟨a, ha, hab, har, haf⟩ := clone_bank source 36 (by omega) (by omega)
    (by omega) (by omega) hsourceNe input tape v 0 s hbank hz hready
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clone_to_one scalar (by omega) (by omega)
    input tape v1 a hab har
  have hv1s : v1 scalar = v scalar := by simp [v1, hscalarNe]
  have hv136 : v1 36 = v source := by simp [v1]
  rw [hv1s] at hbr
  obtain ⟨pcost, c, hpCost, hc, hcb, hcr, hcf⟩ := product 36 (by omega) (by omega)
    input tape v1 (v scalar) b hbb hbr
  have hcb' : Bank c.val v2 := by simpa only [v2, hv136] using hcb
  obtain ⟨d, hd, hdb, hdr, hdf⟩ := clear_one input tape v2 (v scalar) c hcb' hcr
  obtain ⟨e, he, heb, her, hef⟩ := move_to_one 36 (by omega) (by omega)
    input tape v2 d hdb hdr
  have hv236 : v2 36 = v scalar*v source := by simp [v2]
  have hv3 : v3 = v := by
    funext i
    by_cases hi : i = 36
    · subst i; simp [v3, hz]
    · simp [v3, v2, v1, hi]
  have heb' : Bank e.val v := by simpa only [← hv3] using heb
  rw [hv236] at her
  obtain ⟨acost, f, haCost, hf, hfb, hfr, hff⟩ := add_bank target (by omega) (by omega)
    input tape v (v scalar*v source) e heb' her
  obtain ⟨t, hg, htb, htr, htf⟩ := clear_one input tape (accumulated v source scalar target)
    (v scalar*v source) f hfb hfr
  refine ⟨(15*(v source).bits.length+17) + ((15*(v scalar).bits.length+17) +
      (pcost + ((6*(v scalar).bits.length+4) + ((12*(v scalar*v source).bits.length+11) +
        (acost+(6*(v scalar*v source).bits.length+4)))))), t, ?_, ?_, htb, htr,
    (((((haf.trans hbf).trans hcf).trans hdf).trans hef).trans hff).trans htf⟩
  · rw [hv136] at hpCost
    have hlen := bits_mul_le (v scalar) (v source)
    have hbase : (v scalar).bits.length+(v source).bits.length+3 ≤
        (v source).bits.length+(v scalar).bits.length+(v target).bits.length+3 := by omega
    have hprod := hpCost.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hbase 2))
    nlinarith
  · have hr := ha.seq (hb.seq (hc.seq (hd.seq (he.seq (hf.seq hg)))))
    simpa only [macCode, hv1s, hv236] using hr

end Maxwell.Cost.CalibrationMatrix
