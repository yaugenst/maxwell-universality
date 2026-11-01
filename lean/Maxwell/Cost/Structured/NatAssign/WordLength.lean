import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Cost.RoutingPorts.Primitives

/-! Measure an actual binary word while retaining the surrounding natural
operand bank. The scan preserves its source and the arithmetic scratch. -/
namespace Maxwell.Cost.Structured.NatAssign
open RationalAccumulator (Word Blank)

theorem wordLength_executes (ids : Finset ℕ) (source target B : ℕ)
    (hs : source∈ids) (ht : target∈ids) (hne : source≠target) (ht4 : 4≤target)
    (v : ℕ→ℕ) (zero : v target=0) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : Bank ids v s.val) (scratch : Scratch s.val) :
    ∃cost t,Executes input tape (WordLength.code source target) cost s t ∧
      cost≤48*(B+1)^2+1 ∧
      Bank ids (Function.update v target (v source).bits.length) t.val ∧
      Scratch t.val ∧
      (∀i∈ids,((Function.update v target (v source).bits.length) i).bits.length≤B) ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  have blank : Blank s.val target := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [zero] using bank target ht
  obtain ⟨cost,t,execution,bound,word,frame⟩ :=
    RoutingPorts.wordLength source target hne input tape (v source) s (bank source hs) blank
  refine ⟨cost,t,execution,bound.trans (by gcongr;exact hw source hs),?_,?_,?_,frame⟩
  · intro i hi
    by_cases he : i=target
    · subst i;simpa only [Function.update_self] using word
    · simpa only [Function.update_of_ne he] using
        RationalAccumulator.word_of_eq (frame.tapes i (by simpa using he)) (bank i hi)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (frame.tapes i (by simp;omega)) (scratch i hi)
  · intro i hi
    by_cases he : i=target
    · subst i
      have h : ((v source).bits.length).bits.length≤(v source).bits.length := by
        simpa only [WordLength.countBits_eq] using WordLength.countBits_length (v source).bits.length
      simpa only [Function.update_self] using h.trans (hw source hs)
    · simpa only [Function.update_of_ne he] using hw i hi

#print axioms wordLength_executes
end Maxwell.Cost.Structured.NatAssign
