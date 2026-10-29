import Maxwell.Cost.WordGrow
import Maxwell.Cost.HalfPair.ReduceWords
import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.WordLift
open Structured

/-- Add a binary routing level to a padded child label. -/
def code (workTape register : ℕ) : Code :=
  .seq (WordGrow.code workTape false) (.branch register (WordPenultimate.code workTape) .skip)

theorem executes (workTape register : ℕ)
    (h24 : register≠24) (h25 : register≠25) (h26 : register≠26) (h27 : register≠27)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (bit : Bool) (origin : ℤ)
    (s : Store) (hw : s.val.tapes workTape=BitTape.shifted (xs++[false]) origin)
    (hr : s.val.registers register=bit) :
    ∃ cost t, cost≤20*(xs.length+4) ∧ Executes input tape (code workTape register) cost s t ∧
      t.val.tapes workTape=BitTape.shifted (xs++[bit,false]) origin ∧
      WordTransfer.Frame workTape workTape s.val t.val := by
  obtain ⟨a,ea,aw,af⟩ := WordGrow.executes workTape false input tape (xs++[false]) origin s hw
  have ar : a.val.registers register=bit := (af.2.2.2.2.2.2 register h24 h25 h26 h27).trans hr
  have aw' : a.val.tapes workTape=BitTape.shifted (xs++[false,false]) origin := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using aw
  cases bit with
  | false =>
    refine ⟨9*(xs++[false]).length+18+2,a,?_,ea.seq (.no ar (.skip a)),aw',af⟩
    simp only [List.length_append,List.length_singleton]
    omega
  | true =>
    obtain ⟨t,et,tw,tf⟩ := WordPenultimate.executes workTape input tape xs false false origin a aw'
    refine ⟨9*(xs++[false]).length+18+(1+(9*(xs.length+2)+19)),t,?_,ea.seq (.yes ar et),tw,af.trans tf⟩
    simp only [List.length_append,List.length_singleton]
    omega

theorem padded_executes (workTape register : ℕ)
    (h24 : register≠24) (h25 : register≠25) (h26 : register≠26) (h27 : register≠27)
    (input : List Bool) (tape : ℕ → Bool) (k : ℕ) (value : Fin (2^k)) (bit : Bool)
    (s : Store) (hw : BankArray.Word s.val workTape (IncidenceEncoding.word (k+1) value.val))
    (hr : s.val.registers register=bit) :
    ∃ cost t, cost≤20*(k+4) ∧ Executes input tape (code workTape register) cost s t ∧
      BankArray.Word t.val workTape (IncidenceEncoding.word (k+2)
        (value.val+2^k*bit.toNat)) ∧ WordTransfer.Frame workTape workTape s.val t.val := by
  let parent : Fin (2*(2^k)) := ⟨value.val,by have := value.isLt; omega⟩
  obtain ⟨xs,b,hlen,_,hword⟩ := HalfPair.exists_reduce_word k parent
  have hchild : xs++[false]=IncidenceEncoding.word (k+1) value.val := by
    simpa only [parent,Nat.mod_eq_of_lt value.isLt,SourceCircuit.fixedWidth,IncidenceEncoding.word] using hword
  obtain ⟨origin,ho⟩ := hw
  obtain ⟨cost,t,hcost,he,tw,tf⟩ := executes workTape register h24 h25 h26 h27 input tape xs bit origin s
    (by simpa only [hchild] using ho) hr
  have hv : addressValue xs=value.val := by
    have h := congrArg addressValue hchild
    rw [HalfPair.addressValue_append,IncidenceEncoding.word_value] at h
    · simpa [addressValue] using h
    · have := value.isLt; rw [pow_succ]; omega
  have hparent : xs++[bit,false]=IncidenceEncoding.word (k+2) (value.val+2^k*bit.toNat) := by
    apply SourceCircuit.fixedWidth_eq
    · simp [hlen]
    · rw [HalfPair.addressValue_append,hlen,hv]
      simp [addressValue]
  exact ⟨cost,t,by simpa only [hlen] using hcost,he,⟨origin,by simpa only [hparent] using tw⟩,tf⟩

end Maxwell.Cost.WordLift
