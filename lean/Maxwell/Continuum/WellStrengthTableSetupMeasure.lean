import Maxwell.Continuum.WellStrengthTableSetupPlan

namespace Maxwell.Continuum.WellStrengthInitialization.Table
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def measureCode : Code := .seq (WordCleanup.code clearHeaders)
  (.seq (NatAssign.LengthSum.initializedCode 2606 2607 5 sources) (NatAssign.code plan))
def scanWidth (B : ℕ) : ℕ := B+5+sources.length*B+2
def measureBound (B H : ℕ) : ℕ := clearHeaders.length*(6*H+4)+1+
  (192000*(B+2)^2+sources.length*(200000*(scanWidth B)^2)+1+
    3000*8^11*(scanWidth B+2)^2)

theorem measure_executes (v : ℕ→ℕ) (B H : ℕ) (hB : 21≤B)
    (width : ∀i∈sources,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank sources.toFinset v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded clearHeaders H s.val) :
    ∃cost t,Executes input tape measureCode cost s t ∧ cost≤measureBound B H ∧
      NatAssign.Bank ids (values v) t.val ∧
      (∀i∈ids,(values v i).bits.length≤2^11*(scanWidth B+1)) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,a,e0,h0,za,f0⟩:=WordCleanup.executes clearHeaders H input tape s old
  have loadedBank : NatAssign.Bank ids (loaded v) a.val:=by
    intro i hi
    by_cases ht : i∈clearHeaders
    · rw [loaded,ite_eq_left ht,RationalAccumulator.zero_word_iff_blank]
      exact za i ht
    · have source: i∈sources:=by simpa only [List.mem_toFinset] using
        (Finset.mem_union.mp hi).resolve_right (by simpa only [List.mem_toFinset] using ht)
      rw [loaded,ite_eq_right ht]
      exact RationalAccumulator.word_of_eq (f0.tapes i (by simpa only [List.mem_toFinset] using ht))
        (bank i (by simpa only [List.mem_toFinset] using source))
  have z0 : NatAssign.Scratch a.val:=by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i ?_) (scratch i hi)
    simp only [List.mem_toFinset,clearHeaders,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have loadedWidth : ∀i∈ids,(loaded v i).bits.length≤B:=by
    intro i hi
    by_cases ht : i∈clearHeaders
    · simp only [loaded,ite_eq_left ht,show (0:ℕ).bits.length=0 by rfl];omega
    · rw [loaded,ite_eq_right ht]
      apply width
      simpa only [List.mem_toFinset] using (Finset.mem_union.mp hi).resolve_right
        (by simpa only [List.mem_toFinset] using ht)
  obtain ⟨c1,b,e1,h1,bb,zb,f1⟩:=NatAssign.LengthSum.initialized_executes ids ids_ge 2606 2607 5
    (by decide) (by decide) (by decide) sources source_valid (loaded v) B loadedWidth (by change 3≤B;omega)
    input tape a loadedBank z0
  change NatAssign.Bank ids (scanned v) b.val at bb
  have scannedWidth : ∀i∈ids,(scanned v i).bits.length≤scanWidth B:=by
    intro i hi
    by_cases ht : i=2606
    · subst i
      simp only [scanned,NatAssign.LengthSum.initializedValues,Function.update_self,loaded_total]
      have small : (5+NatAssign.LengthSum.total sources v).bits.length≤5+NatAssign.LengthSum.total sources v:=by
        rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
      have sum:=NatAssign.LengthSum.total_le sources v B width
      unfold scanWidth;omega
    · by_cases hp : i=2607
      · subst i
        simp only [scanned,NatAssign.LengthSum.initializedValues,Function.update_of_ne ht,Function.update_self,
          show (0:ℕ).bits.length=0 by rfl]
        omega
      · simp only [scanned,NatAssign.LengthSum.initializedValues,Function.update_of_ne ht,Function.update_of_ne hp]
        exact (loadedWidth i hi).trans (by unfold scanWidth;omega)
  have literal : ∀a∈plan,a.literalWidth≤scanWidth B:=by
    intro a ha
    have small : a.literalWidth≤21:=by
      simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    unfold scanWidth;omega
  obtain ⟨c2,t,e2,h2,bt,zt,f2⟩:=NatAssign.executes ids ids_ge plan valid (scanned v) input tape b bb zb
  have price:=NatAssign.price_bound ids plan valid (scanned v) (scanWidth B) scannedWidth literal
  change NatAssign.price plan (scanned v)≤3000*8^11*(scanWidth B+2)^2 at price
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,bt,?_,zt,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  · unfold measureBound scanWidth
    dsimp only [scanWidth] at price
    omega
  · intro i hi
    have h:=NatAssign.values_width ids plan valid (scanned v) (scanWidth B) scannedWidth literal i hi
    change (values v i).bits.length+1≤2^11*(scanWidth B+1) at h
    omega

#print axioms measure_executes
end Maxwell.Continuum.WellStrengthInitialization.Table
