import Maxwell.Cost.DecoderConstants.Add
import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.PositiveGraph
open Structured
open RationalAccumulator (Word Blank)

/-- Actual addition accepts padded identifier words from the source archive. -/
theorem add_words (source target : ℕ) (hs : 4 ≤ source) (ht : 4 ≤ target)
    (hne : source ≠ target) (input : List Bool) (tape : ℕ → Bool)
    (xs ys : List Bool) (s : Store) (hsource : BankArray.Word s.val source xs) (htarget : BankArray.Word s.val target ys)
    (hblank : ∀ i, i < 4 → Blank s.val i) :
    ∃ cost, ∃ t : Store, cost ≤ 200 * (xs.length+ys.length+4) ∧
      Executes input tape (DecoderConstants.addCode source target) cost s t ∧
      Word t.val target (addressValue xs+addressValue ys) ∧ (∀ i, i < 4 → Blank t.val i) ∧
      StoredProduct.Frame target s.val t.val := by
  obtain ⟨so,hso⟩ := hsource
  obtain ⟨yo,hyo⟩ := htarget
  obtain ⟨ao,ha⟩ := hblank 0 (by omega)
  obtain ⟨xo,hx⟩ := hblank 1 (by omega)
  obtain ⟨zo,hz⟩ := hblank 2 (by omega)
  obtain ⟨c,hc,hcp,hcs,hc1,hcf⟩ := WordTransfer.clone_steps source 1 (by omega)
    input tape xs so xo s.val s.property hso hx
  let cS := Store.ofState c
  have ec : Executes input tape (.call (WordTransfer.clone source 1)) (15*xs.length+17) s cS := by
    simpa using Executes.call _ s c _ hc (by rw [hcp]; rfl)
  have cf : StoredProduct.Frame target s.val cS.val := by
    rcases hcf with ⟨a,b,d,e,f,g,h⟩
    refine ⟨a,b,d,e,f,?_,fun i _ h24 h25 h26 h27 => h i h24 h25 h26 h27⟩
    intro i hi _
    by_cases his : i = source
    · subst i; exact hcs.trans hso.symm
    · exact g i his (by omega)
  obtain ⟨pcost,hpcost,hp,hp1,hpf⟩ := PadWord.simulation 1 xo input tape xs cS.val cS.property hc1
  let p := PadWord.finish 1 cS.val xs
  let pS := Store.ofState p
  have ep : Executes input tape (.call (PadWord.program 1)) (pcost+1) cS pS := .call _ _ _ _ hp rfl
  have pf : StoredProduct.Frame target cS.val pS.val :=
    StoredProduct.frame_of_copy (Or.inr (by omega)) (Or.inr (by omega)) hpf
  have pkeep (i : ℕ) (hi : i ≠ 1) : pS.val.tapes i = cS.val.tapes i := hpf.2.2.2.2.2.1 i hi hi
  have ckeep (i : ℕ) (hi : i ≠ 1) (his : i ≠ source) : cS.val.tapes i = s.val.tapes i :=
    hcf.2.2.2.2.2.1 i his hi
  obtain ⟨qcost,hqcost,hq,hqy,hqf⟩ := PadWord.simulation target yo input tape ys pS.val pS.property
    ((pkeep target (by omega)).trans ((ckeep target (by omega) (Ne.symm hne)).trans hyo))
  let q := PadWord.finish target pS.val ys
  let qS := Store.ofState q
  have eq' : Executes input tape (.call (PadWord.program target)) (qcost+1) pS qS := .call _ _ _ _ hq rfl
  have qf : StoredProduct.Frame target pS.val qS.val :=
    StoredProduct.frame_of_copy (Or.inl rfl) (Or.inl rfl) hqf
  have qkeep (i : ℕ) (hi : i ≠ target) : qS.val.tapes i = pS.val.tapes i := hqf.2.2.2.2.2.1 i hi hi
  obtain ⟨acost,a,hacost,ha',hap,haout,ha0,ha1,ha2,haf⟩ :=
    StoredAdd.simulation target (by omega) input tape (PadWord.bits xs) (PadWord.bits ys)
      ao xo zo yo (PadWord.nonempty _) (PadWord.nonempty _) qS.val qS.property
      ((qkeep 0 (by omega)).trans ((pkeep 0 (by omega)).trans ((ckeep 0 (by omega) (by omega)).trans ha)))
      ((qkeep 1 (by omega)).trans hp1)
      ((qkeep 2 (by omega)).trans ((pkeep 2 (by omega)).trans ((ckeep 2 (by omega) (by omega)).trans hz))) hqy
  let aS := Store.ofState a
  have ea : Executes input tape (.call (StoredAdd.program target)) (acost+1) qS aS :=
    .call _ _ _ _ ha' (by rw [hap]; rfl)
  have af : StoredProduct.Frame target qS.val aS.val := by
    rcases haf with ⟨a,b,c,d,e,f,g⟩
    exact ⟨a,b,c,d,e,fun i hi hn => f i (by omega) hn,fun i hi => g i (by omega)⟩
  obtain ⟨f,hf,hfp,hf1,hff⟩ := TapeOps.clear_steps 1 input tape (PadWord.bits xs) xo aS.val aS.property ha1
  let fS := Store.ofState f
  have ef : Executes input tape (.call (TapeOps.clear 1)) (6*(PadWord.bits xs).length+4) aS fS := by
    simpa using Executes.call _ _ _ _ hf (by rw [hfp]; rfl)
  have ff : StoredProduct.Frame target aS.val fS.val :=
    StoredProduct.frame_of_copy (Or.inr (by omega)) (Or.inr (by omega)) hff
  have fkeep (i : ℕ) (hi : i ≠ 1) : fS.val.tapes i = aS.val.tapes i := hff.2.2.2.2.2.1 i hi hi
  refine ⟨_,fS,?_,ec.seq (ep.seq (eq'.seq (ea.seq ef))),?_,?_,(((cf.trans pf).trans qf).trans af).trans ff⟩
  · have hx := PadWord.length_le xs
    have hy := PadWord.length_le ys
    omega
  · refine ⟨yo+(PadWord.bits ys).length,?_⟩
    simpa only [PadWord.value,RationalAccumulator.address_bits] using (fkeep target (by omega)).trans haout
  · intro i hi
    interval_cases i
    · exact ⟨ao+(PadWord.bits ys).length,(fkeep 0 (by omega)).trans ha0⟩
    · exact ⟨xo+(PadWord.bits xs).length,hf1⟩
    · refine ⟨zo+(addressValue (PadWord.bits xs)+addressValue (PadWord.bits ys)).bits.length,
        (fkeep 2 (by omega)).trans ha2⟩
    · exact RationalAccumulator.blank_of_eq ((fkeep 3 (by omega)).trans
        ((haf.2.2.2.2.2.1 3 (by omega) (by omega)).trans ((qkeep 3 (by omega)).trans
        ((pkeep 3 (by omega)).trans (ckeep 3 (by omega) (by omega)))))) (hblank 3 (by omega))

end Maxwell.Cost.PositiveGraph
