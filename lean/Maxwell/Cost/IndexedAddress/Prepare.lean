import Maxwell.Cost.StoredProduct
import Maxwell.Cost.StoredAdd
import Maxwell.Cost.PadWord
import Maxwell.Cost.Structured.Correctness
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.IndexedAddress
open Structured

/-- Index arithmetic preserves ambient channels, metadata and payload tapes,
including the retained base address on tape 8 and the sign register 23. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 5 → i ≠ 9 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 h5 h9 => (kt i h4 h5 h9).trans (ht i h4 h5 h9),
    fun i h15 h24 h25 h26 h27 => (kg i h15 h24 h25 h26 h27).trans (hg i h15 h24 h25 h26 h27)⟩

theorem Frame.of_product {s t : BitRAMState} (h : StoredProduct.Frame 5 s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 h5 _ => ht i h4 h5, hg⟩

theorem Frame.of_add {s t : BitRAMState} (h : StoredAdd.Frame 5 s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 h5 _ => ht i (by omega) h5,
    fun i h15 h24 h25 h26 h27 => hg i (by omega) h24 h25 h26 h27⟩

theorem Frame.of_transfer {a b : ℕ} {s t : BitRAMState} (h : WordTransfer.Frame a b s t)
    (ht : ∀ i, 4 ≤ i → i ≠ 5 → i ≠ 9 → t.tapes i = s.tapes i) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, _, hg⟩
  exact ⟨ha, hi, hm, hr, ho, ht, fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

theorem Frame.of_tapeOps {a b : ℕ} {s t : BitRAMState} (h : TapeOps.Frame a b s t)
    (ha' : a < 4 ∨ a = 5 ∨ a = 9) (hb' : b < 4 ∨ b = 5 ∨ b = 9) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 h5 h9 => ht i (by omega) (by omega),
    fun i _ _ _ h26 h27 => hg i h26 h27⟩

def prepareCode : Code :=
  .seq (.seq (.seq (.seq
    (.call (StoredProduct.program 5)) (.call (WordTransfer.move 1 9)))
    (.call (WordTransfer.clone 8 1))) (.call (PadWord.program 1))) (.call (PadWord.program 5))

/-- Save the reusable width, fetch the retained base, and prepare nonempty
addition operands after an actual multiplication. Empty index/base are allowed. -/
theorem prepare (input : List Bool) (tape : ℕ → Bool)
    (width index base : List Bool) (ao wo zo yo io bo savedOrigin : ℤ)
    (hwidth : 0 < width.length) (s : Store)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted width wo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = {BitTape.blank with head := yo})
    (h5 : s.val.tapes 5 = BitTape.shifted index io)
    (h8 : s.val.tapes 8 = BitTape.shifted base bo)
    (h9 : s.val.tapes 9 = {BitTape.blank with head := savedOrigin}) :
    ∃ cost t resultOrigin scratchOrigin,
      cost ≤ 500 * (width.length + index.length + 2)^2 + 12 * width.length + 15 * base.length + 41 ∧
      Executes input tape prepareCode cost s t ∧
      t.val.tapes 0 = {BitTape.blank with head := resultOrigin} ∧
      t.val.tapes 1 = BitTape.shifted (PadWord.bits base) (wo + width.length) ∧
      t.val.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.val.tapes 3 = {BitTape.blank with head := yo + index.length} ∧
      t.val.tapes 5 = BitTape.shifted
        (PadWord.bits (addressValue width * addressValue index).bits) (io + index.length) ∧
      t.val.tapes 9 = BitTape.shifted width savedOrigin ∧ Frame s.val t.val := by
  obtain ⟨pcost, p, ro, so, hpcost, hp, hppc, hp5, hp0, hp1, hp2, hp3, hpf⟩ :=
    StoredProduct.simulation 5 (by omega) input tape width index ao wo zo yo io
      hwidth s.val s.property h0 h1 h2 h3 h5
  let pS := Store.ofState p
  have pexec : Executes input tape (.call (StoredProduct.program 5)) (pcost + 1) s pS :=
    .call _ s p pcost hp (by rw [hppc]; rfl)
  have hp8 : pS.val.tapes 8 = BitTape.shifted base bo :=
    (hpf.2.2.2.2.2.1 8 (by omega) (by omega)).trans h8
  have hp9 : pS.val.tapes 9 = {BitTape.blank with head := savedOrigin} :=
    (hpf.2.2.2.2.2.1 9 (by omega) (by omega)).trans h9
  obtain ⟨m, hm, hmpc, hm1, hm9, hmf⟩ := WordTransfer.move_steps 1 9 (by omega)
    input tape width wo savedOrigin pS.val pS.property hp1 hp9
  let mS := Store.ofState m
  have mexec : Executes input tape (.call (WordTransfer.move 1 9)) (12 * width.length + 10 + 1) pS mS :=
    .call _ pS m _ hm (by rw [hmpc]; rfl)
  have mf : Frame pS.val mS.val := Frame.of_transfer hmf (by
    intro i h4 _ h9'; exact hmf.2.2.2.2.2.1 i (by omega) h9')
  have hm8 : mS.val.tapes 8 = BitTape.shifted base bo :=
    (hmf.2.2.2.2.2.1 8 (by omega) (by omega)).trans hp8
  obtain ⟨c, hc, hcpc, hc8, hc1, hcf⟩ := WordTransfer.clone_steps 8 1 (by omega)
    input tape base bo (wo + width.length) mS.val mS.property hm8 hm1
  let cS := Store.ofState c
  have cexec : Executes input tape (.call (WordTransfer.clone 8 1)) (15 * base.length + 16 + 1) mS cS :=
    .call _ mS c _ hc (by rw [hcpc]; rfl)
  have cf : Frame mS.val cS.val := Frame.of_transfer hcf (by
    intro i h4 _ _
    by_cases hi : i = 8
    · subst i; exact hc8.trans hm8.symm
    · exact hcf.2.2.2.2.2.1 i hi (by omega))
  obtain ⟨bcost, hbcost, hb, hb1, hbf⟩ := PadWord.simulation 1 (wo + width.length)
    input tape base cS.val cS.property hc1
  let b := PadWord.finish 1 cS.val base
  let bS := Store.ofState b
  have bexec : Executes input tape (.call (PadWord.program 1)) (bcost + 1) cS bS :=
    .call _ cS b _ hb rfl
  have hm5 : mS.val.tapes 5 = BitTape.shifted (addressValue width * addressValue index).bits (io + index.length) :=
    (hmf.2.2.2.2.2.1 5 (by omega) (by omega)).trans hp5
  have hc5 : cS.val.tapes 5 = BitTape.shifted (addressValue width * addressValue index).bits (io + index.length) :=
    (hcf.2.2.2.2.2.1 5 (by omega) (by omega)).trans hm5
  have hb5 : bS.val.tapes 5 = BitTape.shifted (addressValue width * addressValue index).bits (io + index.length) :=
    (hbf.2.2.2.2.2.1 5 (by omega) (by omega)).trans hc5
  obtain ⟨icost, hicost, hi, hi5, hif⟩ := PadWord.simulation 5 (io + index.length)
    input tape (addressValue width * addressValue index).bits bS.val bS.property hb5
  let i := PadWord.finish 5 bS.val (addressValue width * addressValue index).bits
  let iS := Store.ofState i
  have iexec : Executes input tape (.call (PadWord.program 5)) (icost + 1) bS iS :=
    .call _ bS i _ hi rfl
  have hkeep (j : ℕ) (hj1 : j ≠ 1) (hj5 : j ≠ 5) (hj8 : j ≠ 8) (hj9 : j ≠ 9) :
      iS.val.tapes j = pS.val.tapes j :=
    (hif.2.2.2.2.2.1 j hj5 hj5).trans
      ((hbf.2.2.2.2.2.1 j hj1 hj1).trans
        ((hcf.2.2.2.2.2.1 j hj8 hj1).trans (hmf.2.2.2.2.2.1 j hj1 hj9)))
  refine ⟨_, iS, ro, so, by omega, (((pexec.seq mexec).seq cexec).seq bexec).seq iexec,
    (hkeep 0 (by omega) (by omega) (by omega) (by omega)).trans hp0,
    (hif.2.2.2.2.2.1 1 (by omega) (by omega)).trans hb1,
    (hkeep 2 (by omega) (by omega) (by omega) (by omega)).trans hp2,
    (hkeep 3 (by omega) (by omega) (by omega) (by omega)).trans hp3, hi5, ?_,
    ((((Frame.of_product hpf).trans mf).trans cf).trans
      (Frame.of_tapeOps hbf (by omega) (by omega))).trans
      (Frame.of_tapeOps hif (by omega) (by omega))⟩
  exact (hif.2.2.2.2.2.1 9 (by omega) (by omega)).trans
    ((hbf.2.2.2.2.2.1 9 (by omega) (by omega)).trans
      ((hcf.2.2.2.2.2.1 9 (by omega) (by omega)).trans hm9))

end Maxwell.Cost.IndexedAddress
