import Maxwell.Cost.IndexedAddress.Prepare

namespace Maxwell.Cost.IndexedAddress
open Structured

def finishCode : Code := .seq (.seq (.seq
  (.call (StoredAdd.program 5)) (.call (TapeOps.clear 1)))
  (.call (WordTransfer.move 9 1))) (.call (ScanForward.program 5))

/-- Finish the address sum, restore the reusable width word and place the
computed canonical address at its end for the indexed memory primitive. -/
theorem finish (input : List Bool) (tape : ℕ → Bool)
    (base offset width : List Bool) (ao xo zo io savedOrigin : ℤ)
    (hbase : 0 < base.length) (hoffset : 0 < offset.length) (s : Store)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted base xo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h5 : s.val.tapes 5 = BitTape.shifted offset io)
    (h9 : s.val.tapes 9 = BitTape.shifted width savedOrigin) :
    ∃ cost t,
      cost ≤ 100 * (base.length + offset.length + 2) + 6 * base.length +
        12 * width.length + 5 * (addressValue base + addressValue offset).bits.length + 20 ∧
      Executes input tape finishCode cost s t ∧
      t.val.tapes 0 = {BitTape.blank with head := ao + offset.length} ∧
      t.val.tapes 1 = BitTape.shifted width (xo + base.length) ∧
      t.val.tapes 2 = {BitTape.blank with head := zo + (addressValue base + addressValue offset).bits.length} ∧
      t.val.tapes 3 = s.val.tapes 3 ∧
      t.val.tapes 5 = BitTape.shiftedEnd (addressValue base + addressValue offset).bits (io + offset.length) ∧
      t.val.tapes 9 = {BitTape.blank with head := savedOrigin + width.length} ∧ Frame s.val t.val := by
  let result := (addressValue base + addressValue offset).bits
  obtain ⟨acost, a, hacost, ha, hapc, ha5, ha0, ha1, ha2, haf⟩ :=
    StoredAdd.simulation 5 (by omega) input tape base offset ao xo zo io
      hbase hoffset s.val s.property h0 h1 h2 h5
  let aS := Store.ofState a
  have aexec : Executes input tape (.call (StoredAdd.program 5)) (acost + 1) s aS :=
    .call _ s a acost ha (by rw [hapc]; rfl)
  have ha3 : aS.val.tapes 3 = s.val.tapes 3 := haf.2.2.2.2.2.1 3 (by omega) (by omega)
  have ha9 : aS.val.tapes 9 = BitTape.shifted width savedOrigin :=
    (haf.2.2.2.2.2.1 9 (by omega) (by omega)).trans h9
  obtain ⟨c, hc, hcpc, hc1, hcf⟩ := TapeOps.clear_steps 1 input tape base xo aS.val aS.property ha1
  let cS := Store.ofState c
  have cexec : Executes input tape (.call (TapeOps.clear 1)) (6 * base.length + 3 + 1) aS cS :=
    .call _ aS c _ hc (by rw [hcpc]; rfl)
  have hc9 : cS.val.tapes 9 = BitTape.shifted width savedOrigin :=
    (hcf.2.2.2.2.2.1 9 (by omega) (by omega)).trans ha9
  obtain ⟨m, hm, hmpc, hm9, hm1, hmf⟩ := WordTransfer.move_steps 9 1 (by omega)
    input tape width savedOrigin (xo + base.length) cS.val cS.property hc9 hc1
  let mS := Store.ofState m
  have mexec : Executes input tape (.call (WordTransfer.move 9 1)) (12 * width.length + 10 + 1) cS mS :=
    .call _ cS m _ hm (by rw [hmpc]; rfl)
  have hm5 : mS.val.tapes 5 = BitTape.shifted result (io + offset.length) :=
    (hmf.2.2.2.2.2.1 5 (by omega) (by omega)).trans
      ((hcf.2.2.2.2.2.1 5 (by omega) (by omega)).trans ha5)
  obtain ⟨hs, hs5, hsf⟩ := ScanForward.shifted_steps 5 (io + offset.length) input tape result
    mS.val mS.property hm5
  let scanned := ScanForward.finish 5 result.length mS.val
  let t := Store.ofState scanned
  have sexec : Executes input tape (.call (ScanForward.program 5)) (5 * result.length + 3 + 1) mS t :=
    .call _ mS scanned _ hs rfl
  have hkeep (j : ℕ) (hj1 : j ≠ 1) (hj5 : j ≠ 5) (hj9 : j ≠ 9) :
      t.val.tapes j = aS.val.tapes j :=
    (hsf.2.2.2.2.2.1 j hj5 hj5).trans
      ((hmf.2.2.2.2.2.1 j hj9 hj1).trans (hcf.2.2.2.2.2.1 j hj1 hj1))
  refine ⟨_, t, by dsimp [result] at *; omega, ((aexec.seq cexec).seq mexec).seq sexec,
    (hkeep 0 (by omega) (by omega) (by omega)).trans ha0,
    (hsf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hm1,
    (hkeep 2 (by omega) (by omega) (by omega)).trans ha2,
    (hkeep 3 (by omega) (by omega) (by omega)).trans ha3, hs5,
    (hsf.2.2.2.2.2.1 9 (by omega) (by omega)).trans hm9, ?_⟩
  exact (((Frame.of_add haf).trans (Frame.of_tapeOps hcf (by omega) (by omega))).trans
    (Frame.of_transfer hmf (by intro i h4 _ h9'; exact hmf.2.2.2.2.2.1 i h9' (by omega)))).trans
    (Frame.of_tapeOps hsf (by omega) (by omega))

end Maxwell.Cost.IndexedAddress
