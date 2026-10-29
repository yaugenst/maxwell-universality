import Maxwell.Cost.BankStack.Push

namespace Maxwell.Cost.BankStack
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def wire (width : ℕ) (banks : List ℕ) (values : ℕ → ℕ) : List Bool :=
  banks.flatMap (fun i => FixedWidth.bits width (values i).bits)

def saveCode (clock stack : ℕ) : List ℕ → Code
  | [] => .skip
  | i::rest => .seq (pushCode i clock stack) (saveCode clock stack rest)

def Banks (ids : List ℕ) (values : ℕ → ℕ) (s : BitRAMState) : Prop :=
  ∀ i∈ids, Word s i (values i).bits

def Valid (clock stack : ℕ) (ids : List ℕ) : Prop :=
  ∀ i∈ids, 10 ≤ i ∧ i≠37 ∧ i≠stack ∧ i≠clock

theorem save (clockBank stack : ℕ) (ids : List ℕ)
    (hc : 10 ≤ clockBank) (ha : 10 ≤ stack) (hc37 : clockBank≠37)
    (ha37 : stack≠37) (hca : clockBank≠stack) (valid : Valid clockBank stack ids)
    (input : List Bool) (tape : ℕ → Bool) (values : ℕ → ℕ)
    (clock preceding : List Bool) (hclock : 0<clock.length)
    (hfit : ∀ i∈ids, (values i).bits.length≤clock.length)
    (s : Store) (banks : Banks ids values s.val) (scratch : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (h37 : Blank s.val 37) (hclockBank : Word s.val clockBank clock)
    (hstack : s.val.tapes stack=BitTape.atEnd preceding) :
    ∃ cost t, cost ≤ ids.length*(100*clock.length+110)+1 ∧ Executes input tape (saveCode clockBank stack ids) cost s t ∧
      t.val.tapes stack=BitTape.atEnd (preceding++wire clock.length ids values) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame {37,stack} s.val t.val := by
  induction ids generalizing s preceding with
  | nil =>
    exact ⟨1,s,by simp,.skip s,by simpa [wire] using hstack,scratch,h7,h37,rfl,
      ⟨rfl,rfl,rfl,fun _ _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
  | cons i rest ih =>
    obtain ⟨hi,hi37,hia,_⟩ := valid i (by simp)
    obtain ⟨pc,p,hpc,ep,pstack,ps,p7,p37,pm,pframe⟩ := push i clockBank stack hi hc ha ha37
      input tape (values i).bits clock preceding hclock (hfit i (by simp)) s scratch h7 h37
      (banks i (by simp)) hclockBank hstack
    obtain ⟨rc,t,hrc,er,tstack,ts,t7,t37,tm,tframe⟩ := ih
      (fun j hj => valid j (by simp [hj]))
      (preceding++FixedWidth.bits clock.length (values i).bits) (fun j hj => hfit j (by simp [hj])) p
      (fun j hj => BankArray.word_of_eq (pframe.tapes j (Or.inr (valid j (by simp [hj])).1)
        (by have hv := valid j (by simp [hj]); simp_all)) (banks j (by simp [hj])))
      ps p7 p37
      (BankArray.word_of_eq (pframe.tapes clockBank (Or.inr hc) (by simp [hc37,hca])) hclockBank) pstack
    refine ⟨pc+rc,t,?_,ep.seq er,?_,ts,t7,t37,tm.trans pm,pframe.trans tframe⟩
    · simp only [List.length_cons]; nlinarith
    · simpa only [wire,List.flatMap_cons,List.append_assoc] using tstack

end Maxwell.Cost.BankStack
