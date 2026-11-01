import Maxwell.Continuum.WellStrengthGeometrySetupPlan

namespace Maxwell.Continuum.WellStrengthInitialization.Geometry
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def code : Code := .seq (WordCleanup.code clearHeaders)
  (.seq (NatAssign.code instructions) (WordCopyAppend.code 1251 962 []))
def costBound (B H clockLength : ℕ) : ℕ := clearHeaders.length*(6*H+4)+1+
  (3000*8^30*(B+2)^2+(24*clockLength+28))

theorem executes (v : ℕ→ℕ) (B H : ℕ) (hB : 54≤B)
    (width : ∀i∈inputs,(v i).bits.length≤B)
    (clock : List Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : BankArray.Scratch s.val)
    (old : WordCleanup.Bounded clearHeaders H s.val) (clockWord : BankArray.Word s.val 1251 clock) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound B H clock.length ∧
      NatAssign.Bank ids (values v) t.val ∧
      (∀i∈ids,(values v i).bits.length≤2^30*(B+1)) ∧
      BankArray.Scratch t.val ∧ BankArray.Word t.val 962 clock ∧
      Blank t.val 972 ∧ Blank t.val 973 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c0,a,e0,h0,za,f0⟩:=WordCleanup.executes clearHeaders H input tape s old
  have loadedBank : NatAssign.Bank ids (loaded v) a.val:=by
    intro i hi
    by_cases ht : i∈targets
    · rw [loaded,ite_eq_left ht,RationalAccumulator.zero_word_iff_blank]
      apply za
      exact List.mem_append_left _ (by simpa only [Finset.mem_sort] using ht)
    · have source:= (Finset.mem_union.mp hi).resolve_right ht
      rw [loaded,ite_eq_right ht]
      apply RationalAccumulator.word_of_eq (f0.tapes i ?_) (bank i source)
      have hd : Disjoint inputs clearHeaders.toFinset:=by
        simp only [clearHeaders,List.toFinset_append,Finset.sort_toFinset]
        decide
      exact Finset.disjoint_left.mp hd source
  have z0 : NatAssign.Scratch a.val:=by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i ?_)
    · interval_cases i
      · exact scratch.1
      · exact scratch.2.1
      · exact scratch.2.2.1
      · exact scratch.2.2.2.1
    · have low : ∀j∈clearHeaders,960≤j:=by
        intro j hj
        simp only [clearHeaders,List.mem_append,Finset.mem_sort,targets,GeometryOutput.ids,
          Finset.mem_union,Finset.mem_erase,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton,
          List.mem_cons,List.not_mem_nil,or_false] at hj
        omega
      intro h;have hh:=low i (by simpa only [List.mem_toFinset] using h);omega
  have loadedWidth : ∀i∈ids,(loaded v i).bits.length≤B:=by
    intro i hi
    by_cases ht : i∈targets
    · simp only [loaded,ht,ite_true,show (0:ℕ).bits.length=0 by rfl];omega
    · simpa only [loaded,ht,ite_false] using width i ((Finset.mem_union.mp hi).resolve_right ht)
  have literal : ∀a∈instructions,a.literalWidth≤B:=fun a ha=>(literals a ha).trans hB
  obtain ⟨c1,b,e1,h1,bb,zb,f1⟩:=NatAssign.executes ids ids_ge instructions valid (loaded v)
    input tape a loadedBank z0
  change NatAssign.Bank ids (values v) b.val at bb
  have price:=NatAssign.price_bound ids instructions valid (loaded v) B loadedWidth literal
  change NatAssign.price instructions (loaded v)≤3000*8^30*(B+2)^2 at price
  have widths : ∀i∈ids,(values v i).bits.length≤2^30*(B+1):=by
    intro i hi
    have h:=NatAssign.values_width ids instructions valid (loaded v) B loadedWidth literal i hi
    change (values v i).bits.length+1≤2^30*(B+1) at h
    omega
  have frame01 : BinaryPrecision.Frame work s.val b.val:=
    (f0.mono (by
      simp only [clearHeaders,List.toFinset_append,Finset.sort_toFinset]
      decide)).trans (f1.mono (changes.trans (by
      intro i hi;exact Finset.mem_union_left _ hi)))
  have cleared (i : ℕ) (hi : i=962 ∨ i=972 ∨ i=973) : Blank b.val i:=by
    have external:i∉NatAssign.changes instructions:=by
      rcases hi with rfl|rfl|rfl <;> decide
    apply RationalAccumulator.blank_of_eq (f1.tapes i external)
    apply za
    rcases hi with rfl|rfl|rfl <;> simp [clearHeaders]
  obtain ⟨t,et,ct,ft⟩:=WordCopyAppend.executes 1251 962 (by decide) input tape clock [] b
    (BankArray.word_of_eq (frame01.tapes 1251 (by decide)) clockWord) (cleared 962 (by simp))
  have frame:=frame01.trans (ft.mono (by decide))
  refine ⟨c0+(c1+(24*clock.length+28)),t,?_,?_,?_,widths,?_,?_,
    RationalAccumulator.blank_of_eq (ft.tapes 972 (by decide)) (cleared 972 (by simp)),
    RationalAccumulator.blank_of_eq (ft.tapes 973 (by decide)) (cleared 973 (by simp)),frame⟩
  · simpa only [code,List.length_nil,Nat.mul_zero,Nat.add_zero] using e0.seq (e1.seq et)
  · have main:=h1.trans price
    unfold costBound
    omega
  · intro i hi
    have external:i≠962:=by
      simp only [ids,inputs,targets,GeometryOutput.ids,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.mem_erase,Finset.mem_Icc] at hi
      omega
    exact RationalAccumulator.word_of_eq (ft.tapes i (by simpa only [Finset.mem_singleton] using external)) (bb i hi)
  · exact ⟨RationalAccumulator.blank_of_eq (ft.tapes 0 (by decide)) (zb 0 (by decide)),
      RationalAccumulator.blank_of_eq (ft.tapes 1 (by decide)) (zb 1 (by decide)),
      RationalAccumulator.blank_of_eq (ft.tapes 2 (by decide)) (zb 2 (by decide)),
      RationalAccumulator.blank_of_eq (ft.tapes 3 (by decide)) (zb 3 (by decide)),
      RationalAccumulator.blank_of_eq (frame.tapes 5 (by decide)) scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame.tapes 6 (by decide)) scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame.tapes 8 (by decide)) scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame.tapes 9 (by decide)) scratch.2.2.2.2.2.2.2⟩
  · simpa only [List.append_nil] using ct

#print axioms executes
end Maxwell.Continuum.WellStrengthInitialization.Geometry
