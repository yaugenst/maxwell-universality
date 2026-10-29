import Maxwell.Cost.BankStack.Save
import Maxwell.Cost.BankStack.Replace
import Maxwell.Cost.Structured.WordAssign

namespace Maxwell.Cost.BankStack
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- Restoring visits the static bank list in reverse order, as required by
its LIFO wire representation. The recursion constructs finite code only. -/
def restoreCode (clock stack : ℕ) : List ℕ → Code
  | [] => .skip
  | i::rest => .seq (restoreCode clock stack rest) (replaceCode stack clock i)

theorem restore (clockBank stack : ℕ) (ids : List ℕ)
    (hc : 10 ≤ clockBank) (ha : 10 ≤ stack) (hca : clockBank≠stack)
    (valid : Valid clockBank stack ids) (distinct : ids.Nodup)
    (input : List Bool) (tape : ℕ → Bool) (values : ℕ → ℕ) (current : ℕ → List Bool)
    (clock preceding : List Bool)
    (hfit : ∀ i∈ids, (values i).bits.length≤clock.length)
    (hcurrent : ∀ i∈ids, (current i).length≤clock.length)
    (s : Store) (banks : WordAssign.Bank ids s.val current) (scratch : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (hclockBank : Word s.val clockBank clock)
    (hstack : s.val.tapes stack=BitTape.atEnd (preceding++wire clock.length ids values)) :
    ∃ cost t, cost ≤ ids.length*(37*clock.length+32)+1 ∧ Executes input tape (restoreCode clockBank stack ids) cost s t ∧
      t.val.tapes stack=BitTape.atEnd preceding ∧ Banks ids values t.val ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame (insert stack ids.toFinset) s.val t.val := by
  induction ids generalizing s preceding with
  | nil =>
    exact ⟨1,s,by simp,.skip s,by simpa [wire] using hstack,by simp [Banks],scratch,h7,rfl,
      ⟨rfl,rfl,rfl,fun _ _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
  | cons i rest ih =>
    obtain ⟨hi,_,hia,hic⟩ := valid i (by simp)
    have hin : i∉rest := (List.nodup_cons.mp distinct).1
    obtain ⟨rc,p,hrc,er,pstack,pbanks,ps,p7,pm,pframe⟩ := ih
      (fun j hj => valid j (by simp [hj])) (List.nodup_cons.mp distinct).2
      (preceding++FixedWidth.bits clock.length (values i).bits)
      (fun j hj => hfit j (by simp [hj])) (fun j hj => hcurrent j (by simp [hj])) s
      (fun j hj => banks j (by simp [hj])) scratch h7 hclockBank
      (by simpa only [wire,List.flatMap_cons,List.append_assoc] using hstack)
    have pword : Word p.val i (current i) := BankArray.word_of_eq
      (pframe.tapes i (Or.inr hi) (by simp [hia,hin])) (banks i (by simp))
    have pclock : Word p.val clockBank clock := BankArray.word_of_eq
      (pframe.tapes clockBank (Or.inr hc) (by
        simp only [Finset.mem_insert, List.mem_toFinset, not_or]
        exact ⟨hca,fun hm => (valid clockBank (by simp [hm])).2.2.2 rfl⟩)) hclockBank
    obtain ⟨pc,t,hpc,ep,tstack,ti,_,ts,t7,tm,tframe⟩ := replace stack clockBank i ha hi
      (Ne.symm hca) (Ne.symm hia) (Ne.symm hic) input tape (values i) (current i) clock preceding
      (hfit i (by simp)) (hcurrent i (by simp)) p pstack pword pclock ps p7
    have allbanks : Banks (i::rest) values t.val := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ti
      · exact BankArray.word_of_eq (tframe.tapes j (Or.inr (valid j (by simp [hj])).1)
          (by have hv := valid j (by simp [hj]); have hji : j≠i := by intro he; subst j; exact hin hj
              simp [hv.2.2.1,hji])) (pbanks j hj)
    refine ⟨rc+pc,t,?_,er.seq ep,tstack,allbanks,ts,t7,tm.trans pm,
      (pframe.mono ?_).trans (tframe.mono ?_)⟩
    · simp only [List.length_cons]; nlinarith
    · intro j hj; simp_all; tauto
    · intro j hj; simp_all; tauto

end Maxwell.Cost.BankStack
