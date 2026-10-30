import Maxwell.Continuum.CutoffMonomialControlFrame
import Maxwell.Continuum.CutoffMonomialCoefficients

/-! The outer loop fetches its actual profile coefficient from the current
cache, then restores the full row count before a polynomial pass. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def monomialPrepareCode : Code := .seq (WordReplace.code 208 201)
  (.seq (rowReadCode 4 7 4) (WordReplace.code 206 201))

theorem monomialPrepare_executes {D : ℕ} (a b : Table (4*(D+1))) (j : ℕ) (hj : j<D)
    (B : ℕ) (hm : a.MetadataWidth B) (v : ℕ→Parts) (hv : WidthBank (Finset.range 8) B v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool)
    (hlen : xs.length≤B) (hold : ys.length≤B) (hjlen : j.bits.length≤B)
    (s : Store) (hs : RationalDataflow.Ready (Finset.range 8) v s)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hrow : RationalAccumulator.Word s.val 208 j)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t,Executes input tape monomialPrepareCode cost s t ∧ cost≤2^32*(B+12)^2 ∧
      RationalDataflow.Ready (Finset.range 8) (Function.update v 4 (a.getD (4*j+7))) t ∧
      a.Ready t ∧ b.OutputReady t ∧ BankArray.Word t.val 201 xs ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      (∀i∈([206,207,208,209,216]:List ℕ),t.val.tapes i=s.val.tapes i) := by
  obtain ⟨s0,e0,count0,f0⟩ := WordReplace.executes 208 201 (by decide) input tape j.bits ys s hrow hcount
  have r0 := hs.wordReplace_frame (outside_workspace _ _ (by decide)) f0
  have a0 := ha.copy_frame (Or.inl rfl) f0
  have b0 := hb.copy_frame (Or.inl rfl) f0 a0.scratch a0.seven
  have z0 : ∀i∈RowIndex.ids,RationalAccumulator.Blank s0.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.2.2.2.2.2.1 i _) (hblank i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hix : 4*addressValue j.bits+7<4*(D+1) := by rw [addressValue_bits];omega
  obtain ⟨cr,s1,er,hcr,r1,a1,z1,fr⟩ := rowRead_executes a (Finset.range 8) 4 7 4
    (by decide) v input tape j.bits hix s0 r0 a0 count0 z0
  have hget : a.get ⟨4*addressValue j.bits+7,hix⟩=a.getD (4*j+7) := by
    simp only [addressValue_bits,Table.getD,dite_eq_left (by omega : 4*j+7<4*(D+1))]
  have r1' : RationalDataflow.Ready (Finset.range 8) (Function.update v 4 (a.getD (4*j+7))) s1 := by
    simpa only [hget] using r1
  have b1 := b0.rowRead_frame fr a1.scratch a1.seven
  have saved1 : BankArray.Word s1.val 206 xs := BankArray.word_of_eq
    ((fr.tapes 206 (by decide) (by decide) (by decide)).trans (f0.2.2.2.2.2.1 206 (by decide))) hsaved
  have count1 : BankArray.Word s1.val 201 j.bits := BankArray.word_of_eq
    (fr.tapes 201 (by decide) (by decide) (by decide)) count0
  obtain ⟨t,e2,count2,f2⟩ := WordReplace.executes 206 201 (by decide) input tape xs j.bits s1 saved1 count1
  have at' := a1.copy_frame (Or.inl rfl) f2
  refine ⟨(6*ys.length+15*j.bits.length+21)+(cr+(6*j.bits.length+15*xs.length+21)),t,
    e0.seq (er.seq e2),?_,r1'.wordReplace_frame (outside_workspace _ _ (by decide)) f2,
    at',b1.copy_frame (Or.inl rfl) f2 at'.scratch at'.seven,count2,?_,?_⟩
  · have hbnd := rowReadCost_polynomial a j.bits (v 4) 4 7 B hm hjlen (hv 4 (by decide))
    have hbound : cr≤2^30*(B+11)^2 := by
      apply hcr.trans
      simpa only [show (4:ℕ).bits.length=3 from by decide,show (7:ℕ).bits.length=3 from by decide,
        show B+3+3+5=B+11 by omega] using hbnd
    norm_num at hbound ⊢
    nlinarith only [hbound,hlen,hold,hjlen,Nat.zero_le B]
  · intro i hi
    apply RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 i _) (z1 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  · intro i hi
    have hi201 : i≠201 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
    apply (f2.2.2.2.2.2.1 i hi201).trans
    apply Eq.trans _ (f0.2.2.2.2.2.1 i hi201)
    apply fr.tapes
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms monomialPrepare_executes
end Maxwell.Continuum.Calibration.RawCutoff
