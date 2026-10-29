import Maxwell.Cost.RationalAccumulator.Bank
import Maxwell.Cost.PadWord

namespace Maxwell.Cost.CalibrationMatrix

open Structured RationalAccumulator

def productCode (target : ℕ) : Code := .seq (.call (PadWord.program 1))
  (.seq (.call (StoredProduct.program target)) (.call (NormalizeWord.program 1)))

/-- A canonical bank product, including a zero scalar, with all scratch
tapes restored. The scalar is physically padded and normalized. -/
theorem product (target : ℕ) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (scalar : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val scalar) :
    ∃ cost, ∃ t : Store, cost ≤ 1000*(scalar.bits.length+(v target).bits.length+3)^2 ∧
      Executes input tape (productCode target) cost s t ∧
      Bank t.val (Function.update v target (scalar*v target)) ∧
      Scratch t.val scalar ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨ao, h0⟩ := hready.1
  obtain ⟨xo, h1⟩ := hready.2.1
  obtain ⟨zo, h2⟩ := hready.2.2.1
  obtain ⟨yo, h3⟩ := hready.2.2.2
  obtain ⟨origin, hw⟩ := hbank target ht ht'
  obtain ⟨pcost, hpcost, hp, hpword, hpf⟩ :=
    PadWord.simulation 1 xo input tape scalar.bits s.val s.property h1
  let p : Store := Store.ofState (PadWord.finish 1 s.val scalar.bits)
  have hep : Executes input tape (.call (PadWord.program 1)) (pcost+1) s p :=
    Executes.call _ _ _ _ hp (by simp [PadWord.program, PadWord.finish])
  have hp0 := (hpf.2.2.2.2.2.1 0 (by omega) (by omega)).trans h0
  have hp2 := (hpf.2.2.2.2.2.1 2 (by omega) (by omega)).trans h2
  have hp3 := (hpf.2.2.2.2.2.1 3 (by omega) (by omega)).trans h3
  have hpt := (hpf.2.2.2.2.2.1 target (by omega) (by omega)).trans hw
  obtain ⟨mcost, m, ro, so, hmcost, hm, hmp, hmword, hm0, hm1, hm2, hm3, hmf⟩ :=
    StoredProduct.simulation target (by omega) input tape (PadWord.bits scalar.bits) (v target).bits
      ao xo zo yo origin (PadWord.nonempty _) p.val p.property hp0 hpword hp2 hp3 hpt
  let r : Store := Store.ofState m
  have hem : Executes input tape (.call (StoredProduct.program target)) (mcost+1) p r :=
    Executes.call _ _ _ _ hm (by
      simp [StoredProduct.program, hmp, TapeOps.copyClear, HornerMultiply.program,
        NormalizeWord.program, ScanForward.program, TapeOps.trim, Rewind.program,
        TapeOps.clear, BitRAMInstruction.relocate, RewindOvershoot.program,
        RewindOvershoot.preamble, BitRAM.link, rippleAdder])
  obtain ⟨ncost, normalized, hncost, hn, hnp, hnword, _, hnf⟩ :=
    NormalizeWord.simulation 1 xo input tape (PadWord.bits scalar.bits) r.val r.property hm1
  let t : Store := Store.ofState normalized
  have hen : Executes input tape (.call (NormalizeWord.program 1)) (ncost+1) r t :=
    Executes.call _ _ _ _ hn (by
      simp [NormalizeWord.program, hnp, ScanForward.program, TapeOps.trim,
        Rewind.program, BitRAMInstruction.relocate])
  refine ⟨pcost+1+(mcost+1+(ncost+1)), t, ?_, hep.seq (hem.seq hen), ?_, ?_, ?_⟩
  · have hlen := PadWord.length_le scalar.bits
    have hbase : (PadWord.bits scalar.bits).length+(v target).bits.length+2 ≤
        scalar.bits.length+(v target).bits.length+3 := by omega
    have hmul := hmcost.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hbase 2))
    have hnorm : ncost ≤ 16*(scalar.bits.length+1)+17 := by omega
    nlinarith
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨origin+(v target).bits.length, by simpa [t, Store.ofState] using
        (hnf.2.2.2.2.2.1 target (by omega)).trans hmword⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq ((hnf.2.2.2.2.2.1 i (by omega)).trans
        ((hmf.2.2.2.2.2.1 i (by omega) hit).trans
          (hpf.2.2.2.2.2.1 i (by omega) (by omega)))) (hbank i hi hi')
  · exact ⟨⟨ro, (hnf.2.2.2.2.2.1 0 (by omega)).trans hm0⟩,
      ⟨xo, by simpa [t, Store.ofState] using hnword⟩,
      ⟨so, (hnf.2.2.2.2.2.1 2 (by omega)).trans hm2⟩,
      ⟨yo+(v target).bits.length, (hnf.2.2.2.2.2.1 3 (by omega)).trans hm3⟩⟩
  · rcases hpf with ⟨pa, pi, pm, pr, po, pt, pg⟩
    rcases hmf with ⟨ma, mi, mm, mr, mo, mt, mg⟩
    rcases hnf with ⟨na, ni, nm, nr, no, nt, ng⟩
    exact ⟨na.trans (ma.trans pa), ni.trans (mi.trans pi), nm.trans (mm.trans pm),
      nr.trans (mr.trans pr), no.trans (mo.trans po),
      fun i hi hib => (nt i (by omega)).trans
        ((mt i hi (by omega)).trans (pt i (by omega) (by omega))),
      fun i hi h24 h25 h26 h27 => (ng i h24 h25 h26 h27).trans
        ((mg i hi h24 h25 h26 h27).trans (pg i h26 h27))⟩

end Maxwell.Cost.CalibrationMatrix
