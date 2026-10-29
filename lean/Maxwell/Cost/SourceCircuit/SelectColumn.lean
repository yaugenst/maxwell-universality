import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.SourceCircuit.BankReplace

namespace Maxwell.Cost.SourceCircuit.SelectColumn
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (.call (Rewind.program 16))
  (.seq (BankArray.packCanonicalCode 16 93) (replaceCode 37 91))

def work : Finset ℕ := {16,37,91}

theorem executes (input : List Bool) (tape : ℕ → Bool)
    (column : ℕ) (clock old : List Bool) (s : Store)
    (hclock : 0 < clock.length) (hfit : column.bits.length ≤ clock.length)
    (hold : old.length = clock.length) (hs : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h16 : s.val.tapes 16 = BitTape.atEnd column.bits)
    (hc : BankArray.Word s.val 93 clock) (hi : BankArray.Word s.val 91 old) :
    ∃ cost t, cost ≤ 4*column.bits.length+98*clock.length+111 ∧
      Executes input tape code cost s t ∧
      BankArray.Word t.val 91 (FixedWidth.bits clock.length column.bits) ∧
      t.val.tapes 16 = BitTape.ofList column.bits ∧ Blank t.val 37 ∧ Blank t.val 7 ∧
      BankArray.Scratch t.val ∧ t.val.memory = s.val.memory ∧ Frame work s.val t.val := by
  have er := Rewind.atEnd_steps 16 input tape column.bits s.val s.property h16
  let r := Store.ofState (Rewind.finish 16 s.val)
  have eR : Executes input tape (.call (Rewind.program 16)) (4*column.bits.length+6) s r :=
    .call _ s _ _ er (by simp [Rewind.program,Rewind.finish])
  have r16 : r.val.tapes 16 = BitTape.ofList column.bits := Rewind.finish_tape 16 _ _ h16
  have keep (j : ℕ) (hj : j ≠ 16) : r.val.tapes j = s.val.tapes j := by
    simp [r,Store.ofState,Rewind.finish,hj]
  obtain ⟨pc,p,hpc,ep,p37,ps,p7,pm,pf⟩ := BankArray.pack_canonical 16 93 (by omega) (by omega)
    input tape column.bits clock hclock hfit r
    (scratch_of_tapes hs (fun j hj => keep j (by omega)))
    (RationalAccumulator.blank_of_eq (keep 7 (by omega)) h7)
    (RationalAccumulator.blank_of_eq (keep 37 (by omega)) h37)
    ⟨0,by simpa [BitTape.shifted,BitTape.ofList] using r16⟩
    (BankArray.word_of_eq (keep 93 (by omega)) hc)
  obtain ⟨t,et,ti,t37,tm,tf,tk⟩ := replace_executes 37 91 (by omega) input tape
    (FixedWidth.bits clock.length column.bits) old p p37
    (BankArray.word_of_eq ((pf.2.2.2.1 91 (by omega) (by omega)).trans (keep 91 (by omega))) hi)
  have rf : Frame work s.val r.val := by
    refine ⟨rfl,rfl,rfl,?_,rfl,?_⟩
    · intro j _ hj
      exact keep j (fun he => hj (by simp [work,he]))
    · intro j hj
      simp [r,Store.ofState,Rewind.finish,show j ≠ 24 by omega,show j ≠ 25 by omega]
  refine ⟨4*column.bits.length+6+(pc+(6*old.length+12*(FixedWidth.bits clock.length column.bits).length+15)),
    t,?_,eR.seq (ep.seq et),ti,
    (tk 16 (by omega) (by omega)).trans ((pf.2.2.2.1 16 (by omega) (by omega)).trans r16),
    t37,RationalAccumulator.blank_of_eq (tk 7 (by omega) (by omega)) p7,
    scratch_of_tapes ps (fun j hj => tk j (by omega) (by omega)),
    tm.trans pm.2.2.2.1,rf.trans (((frame_except pf).mono (by simp [work])).trans
      (tf.mono (by simp [work])))⟩
  simp only [FixedWidth.bits_length,hold]
  omega

end Maxwell.Cost.SourceCircuit.SelectColumn
