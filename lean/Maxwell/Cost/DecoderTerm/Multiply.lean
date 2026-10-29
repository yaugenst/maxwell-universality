import Maxwell.Cost.RationalAccumulator.Bank
import Maxwell.Cost.PadWord

namespace Maxwell.Cost.DecoderTerm

open Structured
open RationalAccumulator (Word Blank)

/-- Multiply a stored unsigned word by another stored word, including zero.
Only the destination and the four arithmetic scratch tapes may change. -/
def multiplyCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 1))
    (.seq (.call (PadWord.program 1))
      (.seq (.call (StoredProduct.program target)) (.call (TapeOps.clear 1))))

theorem multiply (source target : ℕ) (hs : 4 ≤ source) (ht : 4 ≤ target)
    (hne : source ≠ target) (input : List Bool) (tape : ℕ → Bool)
    (x y : ℕ) (s : Store) (hsource : Word s.val source x) (htarget : Word s.val target y)
    (hblank : ∀ i, i < 4 → Blank s.val i) :
    ∃ cost, ∃ t : Store, cost ≤ 600 * (x.bits.length + y.bits.length + 3)^2 ∧
      Executes input tape (multiplyCode source target) cost s t ∧
      Word t.val target (x * y) ∧ (∀ i, i < 4 → Blank t.val i) ∧
      StoredProduct.Frame target s.val t.val := by
  obtain ⟨so, hso⟩ := hsource
  obtain ⟨yo, hyo⟩ := htarget
  obtain ⟨ao, ha⟩ := hblank 0 (by omega)
  obtain ⟨xo, hx⟩ := hblank 1 (by omega)
  obtain ⟨zo, hz⟩ := hblank 2 (by omega)
  obtain ⟨wo, hw⟩ := hblank 3 (by omega)
  obtain ⟨c, hc, hcp, hcs, hc1, hcf⟩ := WordTransfer.clone_steps source 1 (by omega)
    input tape x.bits so xo s.val s.property hso hx
  let cS := Store.ofState c
  have ec : Executes input tape (.call (WordTransfer.clone source 1))
      (15*x.bits.length+17) s cS := by
    simpa using Executes.call _ s c _ hc (by rw [hcp]; rfl)
  have cf : StoredProduct.Frame target s.val cS.val := by
    rcases hcf with ⟨a,b,d,e,f,g,h⟩
    refine ⟨a,b,d,e,f,?_,fun i _ h24 h25 h26 h27 => h i h24 h25 h26 h27⟩
    intro i hi _
    by_cases his : i = source
    · subst i; exact hcs.trans hso.symm
    · exact g i his (by omega)
  obtain ⟨pcost, hpcost, hp, hp1, hpf⟩ := PadWord.simulation 1 xo input tape x.bits
    cS.val cS.property hc1
  let p := PadWord.finish 1 cS.val x.bits
  let pS := Store.ofState p
  have ep : Executes input tape (.call (PadWord.program 1)) (pcost+1) cS pS :=
    .call _ cS p pcost hp rfl
  have pf : StoredProduct.Frame target cS.val pS.val :=
    StoredProduct.frame_of_copy (Or.inr (by omega)) (Or.inr (by omega)) hpf
  have pkeep (i : ℕ) (hi : i ≠ 1) : pS.val.tapes i = cS.val.tapes i :=
    hpf.2.2.2.2.2.1 i hi hi
  have ckeep (i : ℕ) (hi : i ≠ 1) (his : i ≠ source) : cS.val.tapes i = s.val.tapes i :=
    hcf.2.2.2.2.2.1 i his hi
  obtain ⟨mcost,m,mo,mz,hmcost,hm,hmp,hmout,hm0,hm1,hm2,hm3,hmf⟩ :=
    StoredProduct.simulation target ht input tape (PadWord.bits x.bits) y.bits ao xo zo wo yo
      (PadWord.nonempty _) pS.val pS.property
      ((pkeep 0 (by omega)).trans ((ckeep 0 (by omega) (by omega)).trans ha)) hp1
      ((pkeep 2 (by omega)).trans ((ckeep 2 (by omega) (by omega)).trans hz))
      ((pkeep 3 (by omega)).trans ((ckeep 3 (by omega) (by omega)).trans hw))
      ((pkeep target (by omega)).trans ((ckeep target (by omega) (Ne.symm hne)).trans hyo))
  let mS := Store.ofState m
  have em : Executes input tape (.call (StoredProduct.program target)) (mcost+1) pS mS :=
    .call _ pS m mcost hm (by rw [hmp]; rfl)
  obtain ⟨f,hf,hfp,hf1,hff⟩ := TapeOps.clear_steps 1 input tape (PadWord.bits x.bits) xo
    mS.val mS.property hm1
  let fS := Store.ofState f
  have ef : Executes input tape (.call (TapeOps.clear 1))
      (6*(PadWord.bits x.bits).length+4) mS fS := by
    simpa using Executes.call _ mS f _ hf (by rw [hfp]; rfl)
  have hfinal : StoredProduct.Frame target mS.val fS.val :=
    StoredProduct.frame_of_copy (Or.inr (by omega)) (Or.inr (by omega)) hff
  have fkeep (i : ℕ) (hi : i ≠ 1) : fS.val.tapes i = mS.val.tapes i :=
    hff.2.2.2.2.2.1 i hi hi
  refine ⟨_,fS,?_,ec.seq (ep.seq (em.seq ef)),?_,?_,((cf.trans pf).trans hmf).trans hfinal⟩
  · have hlen := PadWord.length_le x.bits
    have hmcap : mcost ≤ 500*(x.bits.length+y.bits.length+3)^2 := hmcost.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
    have hsq : x.bits.length+y.bits.length+3 ≤ (x.bits.length+y.bits.length+3)^2 := by nlinarith
    nlinarith
  · refine ⟨yo+y.bits.length, ?_⟩
    simpa only [PadWord.value, RationalAccumulator.address_bits] using
      (fkeep target (by omega)).trans hmout
  · intro i hi
    interval_cases i
    · exact ⟨mo, (fkeep 0 (by omega)).trans hm0⟩
    · exact ⟨xo+(PadWord.bits x.bits).length,hf1⟩
    · exact ⟨mz, (fkeep 2 (by omega)).trans hm2⟩
    · exact ⟨wo+y.bits.length,(fkeep 3 (by omega)).trans hm3⟩

end Maxwell.Cost.DecoderTerm
