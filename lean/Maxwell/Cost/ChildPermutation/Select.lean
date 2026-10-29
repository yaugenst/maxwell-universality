import Maxwell.Cost.IncidenceEncoding
import Maxwell.Cost.WordReduceHalf
import Maxwell.Cost.HalfPair.ReduceWords
import Maxwell.Cost.WordSwap

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

theorem reduce_executes (workTape : ℕ) (k : ℕ) (i : Fin (2*(2^k)))
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Word s.val workTape (IncidenceEncoding.word (k+2) i.val)) :
    ∃ t, Executes input tape (WordReduceHalf.code workTape) (9*k+31) s t ∧
      Word t.val workTape (IncidenceEncoding.word (k+1) (i.val%2^k)) ∧
      WordTransfer.Frame workTape workTape s.val t.val := by
  obtain ⟨xs,b,hlen,hword,hreduced⟩ := HalfPair.exists_reduce_word k i
  obtain ⟨origin,ho⟩ := hw
  have he : IncidenceEncoding.word (k+2) i.val=xs++[b,false] := hword
  obtain ⟨t,et,tw,tf⟩ := WordReduceHalf.executes workTape input tape xs b false origin s (by simpa only [he] using ho)
  exact ⟨t,by simpa only [hlen] using et,⟨origin,by simpa only [hreduced,SourceCircuit.fixedWidth,IncidenceEncoding.word] using tw⟩,tf⟩

abbrev SelectFrame := WordSwap.Frame 89 91 92

theorem SelectFrame.trans {s t u : BitRAMState} (h : SelectFrame s t) (j : SelectFrame t u) : SelectFrame s u := by
  rcases h with ⟨ha,hi,hm,hr,ho,ht,hg⟩
  rcases j with ⟨ja,ji,jm,jr,jo,jt,jg⟩
  exact ⟨ja.trans ha,ji.trans hi,jm.trans hm,jr.trans hr,jo.trans ho,
    fun i h89 h91 h92 => (jt i h89 h91 h92).trans (ht i h89 h91 h92),
    fun i h24 h25 h26 h27 => (jg i h24 h25 h26 h27).trans (hg i h24 h25 h26 h27)⟩

theorem SelectFrame.of_reduce {workTape : ℕ} {s t : BitRAMState}
    (hw : workTape=89 ∨ workTape=91) (h : WordTransfer.Frame workTape workTape s t) : SelectFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i h89 h91 _ => h.2.2.2.2.2.1 i (by rcases hw with hw | hw <;> omega)
      (by rcases hw with hw | hw <;> omega),h.2.2.2.2.2.2⟩

def selectCode : Code := .seq (.branch 30 (WordSwap.code 89 91 92) .skip)
  (.seq (WordReduceHalf.code 89) (WordReduceHalf.code 91))

/-- One actual color branch selects both children, then removes the common
high coordinate bit from both stored parent labels. -/
theorem select_executes (k : ℕ) (lower upper : Fin (2*(2^k))) (color : Bool)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hcolor : s.val.registers 30=color)
    (hl : Word s.val 89 (IncidenceEncoding.word (k+2) lower.val))
    (hu : Word s.val 91 (IncidenceEncoding.word (k+2) upper.val)) (h92 : Blank s.val 92) :
    ∃ cost t, cost≤100*(k+3) ∧ Executes input tape selectCode cost s t ∧
      Word t.val 89 (IncidenceEncoding.word (k+1) ((if color then upper else lower).val%2^k)) ∧
      Word t.val 91 (IncidenceEncoding.word (k+1) ((if color then lower else upper).val%2^k)) ∧
      Blank t.val 92 ∧ SelectFrame s.val t.val := by
  have branchRun : ∃ cost a, cost≤36*(k+2)+34 ∧
      Executes input tape (.branch 30 (WordSwap.code 89 91 92) .skip) cost s a ∧
      Word a.val 89 (IncidenceEncoding.word (k+2) (if color then upper else lower).val) ∧
      Word a.val 91 (IncidenceEncoding.word (k+2) (if color then lower else upper).val) ∧
      Blank a.val 92 ∧ SelectFrame s.val a.val := by
    cases color with
    | false => exact ⟨2,s,by omega,.no hcolor (.skip s),hl,hu,h92,by simp [SelectFrame,WordSwap.Frame]⟩
    | true =>
      obtain ⟨a,ea,al,au,a92,af⟩ := WordSwap.executes 89 91 92 (by omega) (by omega) (by omega)
        input tape (IncidenceEncoding.word (k+2) lower.val) (IncidenceEncoding.word (k+2) upper.val) s hl hu h92
      refine ⟨1+(12*(2*(IncidenceEncoding.word (k+2) lower.val).length+
        (IncidenceEncoding.word (k+2) upper.val).length)+33),a,?_,.yes hcolor ea,al,au,a92,af⟩
      simp only [IncidenceEncoding.word_length]
      omega
  obtain ⟨bc,b,hbc,eb,bl,bu,b92,bf⟩ := branchRun
  obtain ⟨a,ea,al,af⟩ := reduce_executes 89 k (if color then upper else lower) input tape b bl
  obtain ⟨t,et,tu,tf⟩ := reduce_executes 91 k (if color then lower else upper) input tape a
    (BankArray.word_of_eq (af.2.2.2.2.2.1 91 (by omega) (by omega)) bu)
  refine ⟨bc+((9*k+31)+(9*k+31)),t,by omega,eb.seq (ea.seq et),
    BankArray.word_of_eq (tf.2.2.2.2.2.1 89 (by omega) (by omega)) al,tu,?_,
    bf.trans ((SelectFrame.of_reduce (Or.inl rfl) af).trans (SelectFrame.of_reduce (Or.inr rfl) tf))⟩
  exact RationalAccumulator.blank_of_eq ((tf.2.2.2.2.2.1 92 (by omega) (by omega)).trans
    (af.2.2.2.2.2.1 92 (by omega) (by omega))) b92

end Maxwell.Cost.ChildPermutation
