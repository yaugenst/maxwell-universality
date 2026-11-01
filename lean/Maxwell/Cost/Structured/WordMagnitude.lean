import Maxwell.Cost.IntegerNormSquare.Magnitude
import Maxwell.Cost.RationalAccumulator.EmitCleanup
import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.WordCall

/-! Signed magnitude from two stored natural words. The shared subtraction
kernel restores scratch and preserves both input words. -/
namespace Maxwell.Cost.Structured.WordMagnitude
open RationalAccumulator (Word Blank)

def code (left right target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone left 0))
    (.seq (.call (WordTransfer.clone right 1))
      (.seq (.call SignedDifference.program)
        (.seq (RationalAccumulator.eraseOvershootCode 0)
          (.seq (RationalAccumulator.eraseOvershootCode 1)
            (.seq (.call (Rewind.program 2)) (.call (WordTransfer.move 2 target)))))))

theorem executes (left right target : ℕ) (hl : 4 ≤ left) (hr : 4 ≤ right)
    (ht : 4 ≤ target) (input : List Bool) (tape : ℕ→Bool) (x y : ℕ)
    (s : Store) (leftWord : Word s.val left x) (rightWord : Word s.val right y)
    (targetBlank : Blank s.val target) (scratch : ∀i,i<4→Blank s.val i) :
    ∃cost t,Executes input tape (code left right target) cost s t ∧
      cost ≤ 300*(x.bits.length+y.bits.length+4) ∧ Word t.val target (IntegerNormSquare.magnitude x y) ∧
      (∀i,i<4→Blank t.val i) ∧ BinaryPrecision.Frame {0,1,2,target} s.val t.val ∧
      t.val.registers 23=SignedDifference.sign x.bits y.bits := by
  obtain ⟨lo,hleft⟩:=leftWord
  obtain ⟨ro,hright⟩:=rightWord
  obtain ⟨ao,h0⟩:=scratch 0 (by decide)
  obtain ⟨bo,h1⟩:=scratch 1 (by decide)
  obtain ⟨co,h2⟩:=scratch 2 (by decide)
  obtain ⟨outOrigin,hout⟩:=targetBlank
  obtain ⟨a,ea,atapes,af⟩:=WordCall.clone left 0 (by omega) input tape x.bits lo ao s hleft h0
  obtain ⟨b,eb,btapes,bf⟩:=WordCall.clone right 1 (by omega) input tape y.bits ro bo a
    (by simpa [atapes,show right≠0 by omega] using hright) (by simpa [atapes] using h1)
  obtain ⟨dcost,diff,origin,hdcost,ed,dp,sign,d2,d0,d1⟩:=SignedDifference.simulation_cleanup
    input tape b.val x.bits y.bits ao bo co b.property
    (by simp [btapes,atapes]) (by simp [btapes]) (by simpa [btapes,atapes] using h2)
  have df:=SignedDifference.execution_frame input tape ed
  let d:=Store.ofState diff
  have ed' : Executes input tape (.call SignedDifference.program) (dcost+1) b d :=
    .call _ _ _ _ ed (by rw [dp];rfl)
  let ps:=SignedDifference.padded x.bits
  let qs:=SignedDifference.padded y.bits
  let distance:=max ps.length qs.length
  obtain ⟨e,ee,e0,ef⟩:=RationalAccumulator.erase_overshoot 0 input tape ps ao distance
    (SignedDifference.padded_pos _) (le_max_left _ _) d d0
  obtain ⟨f,ef',f1,ff⟩:=RationalAccumulator.erase_overshoot 1 input tape qs bo distance
    (SignedDifference.padded_pos _) (le_max_right _ _) e
    ((ef.2.2.2.2.2.1 1 (by decide) (by decide)).trans d1)
  have f2 : f.val.tapes 2=BitTape.shiftedEnd (IntegerNormSquare.magnitude x y).bits origin := by
    exact (ff.2.2.2.2.2.1 2 (by decide) (by decide)).trans
      ((ef.2.2.2.2.2.1 2 (by decide) (by decide)).trans (by
        simpa only [d,Store.ofState,IntegerNormSquare.magnitude_eq x y] using d2))
  have rw2:=WordTransfer.rewind_shifted 2 origin input tape (IntegerNormSquare.magnitude x y).bits f.val f.property f2
  let r:=Store.ofState (Rewind.finishAt 2 origin f.val)
  have er : Executes input tape (.call (Rewind.program 2)) (4*(IntegerNormSquare.magnitude x y).bits.length+6) f r :=
    .call _ _ _ _ rw2.1 (by simp [Rewind.program,Rewind.finishAt])
  have rf:=WordTransfer.frame_rewind 2 2 2 (Or.inl rfl) origin f.val
  have fkeep (i : ℕ) (hi : 3 ≤ i) : f.val.tapes i=s.val.tapes i := by
    rw [ff.2.2.2.2.2.1 i (by omega) (by omega),ef.2.2.2.2.2.1 i (by omega) (by omega)]
    change diff.tapes i=_
    rw [df.2.2.2.2.2.1 i hi,btapes,atapes]
    simp [show i≠0 by omega,show i≠1 by omega]
  obtain ⟨moved,em,mp,m2,mt,mf⟩:=WordTransfer.move_steps 2 target (by omega)
    input tape (IntegerNormSquare.magnitude x y).bits origin outOrigin r.val r.property rw2.2
    ((rf.2.2.2.2.2.1 target (by omega) (by omega)).trans ((fkeep target (by omega)).trans hout))
  let t:=Store.ofState moved
  have em' : Executes input tape (.call (WordTransfer.move 2 target))
      (12*(IntegerNormSquare.magnitude x y).bits.length+11) r t := .call _ _ _ _ em (by rw [mp];rfl)
  refine ⟨_,t,ea.seq (eb.seq (ed'.seq (ee.seq (ef'.seq (er.seq em'))))),?_,⟨outOrigin,mt⟩,?_,?_,?_⟩
  · have hp:=SignedDifference.padded_length x.bits
    have hq:=SignedDifference.padded_length y.bits
    have hd:=IntegerNormSquare.magnitude_bits_length_le x y
    dsimp [distance,ps,qs]
    omega
  · intro i hi
    interval_cases i
    · exact RationalAccumulator.blank_of_eq ((mf.2.2.2.2.2.1 0 (by decide) (by omega)).trans
        ((rf.2.2.2.2.2.1 0 (by decide) (by decide)).trans
          (ff.2.2.2.2.2.1 0 (by decide) (by decide)))) e0
    · exact RationalAccumulator.blank_of_eq ((mf.2.2.2.2.2.1 1 (by decide) (by omega)).trans
        (rf.2.2.2.2.2.1 1 (by decide) (by decide))) f1
    · exact ⟨origin+(IntegerNormSquare.magnitude x y).bits.length,m2⟩
    · exact RationalAccumulator.blank_of_eq ((mf.2.2.2.2.2.1 3 (by decide) (by omega)).trans
        ((rf.2.2.2.2.2.1 3 (by decide) (by decide)).trans (fkeep 3 (by decide)))) (scratch 3 (by decide))
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · exact mf.1.trans (rf.1.trans (ff.1.trans (ef.1.trans (df.1.trans (bf.1.trans af.1)))))
    · exact mf.2.1.trans (rf.2.1.trans (ff.2.1.trans (ef.2.1.trans (df.2.1.trans (bf.2.1.trans af.2.1)))))
    · exact mf.2.2.1.trans (rf.2.2.1.trans (ff.2.2.1.trans (ef.2.2.1.trans (df.2.2.1.trans (bf.2.2.1.trans af.2.2.1)))))
    · exact mf.2.2.2.1.trans (rf.2.2.2.1.trans (ff.2.2.2.1.trans (ef.2.2.2.1.trans (df.2.2.2.1.trans (bf.2.2.2.1.trans af.2.2.2.1)))))
    · exact mf.2.2.2.2.1.trans (rf.2.2.2.2.1.trans (ff.2.2.2.2.1.trans (ef.2.2.2.2.1.trans (df.2.2.2.2.1.trans (bf.2.2.2.2.1.trans af.2.2.2.2.1)))))
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact (mf.2.2.2.2.2.1 i hi.2.2.1 hi.2.2.2).trans
        ((rf.2.2.2.2.2.1 i hi.2.2.1 hi.2.2.1).trans (fkeep i (by omega)))

  · exact (mf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
      ((rf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
        ((ff.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
          ((ef.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans sign)))

#print axioms executes
end Maxwell.Cost.Structured.WordMagnitude
