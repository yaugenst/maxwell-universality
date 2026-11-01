import Maxwell.Continuum.CalibrationSeedRootMeaning
import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowArrayOutputFrame
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! Materialization of one complete sparse convolution coefficient. Both
the eight cache contributions and the three output-channel writes execute. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def emissionCode (j : Fin 3) (part : Fin 2) : Code :=
  .seq (termsCode j part parities) (PartArray.writeAtCode 789 27)
def emissionWidth (B : ℕ) : ℕ := termsWidth parities.length B
def emissionCost (B : ℕ) : ℕ := termsCost parities.length B+2^20*(emissionWidth B+5)^2

theorem termsWidth_ge (k B : ℕ) : B≤termsWidth k B := by
  induction k generalizing B with
  | zero => exact le_rfl
  | succ k ih => exact (stepWidth_ge B).trans (ih (stepWidth B))

theorem output_ready_after_terms {T U : ℕ} {a : PartArray.Table T} {b : PartArray.Table U}
    {s t : Store} (h : b.OutputReady s) (cache : a.Ready t) (frame : Frame s t) :
    b.OutputReady t := by
  apply h.transfer frame.memory _ cache.scratch cache.seven
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> exact frame.tapes _ (by decide) (by decide)

theorem emission_executes (M D T : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (b : PartArray.Table T) (outputIndex : Fin T) (j : Fin 3) (part : Fin 2)
    (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hM : n 750=M) (hD : n 751=D) (half : n 752=n 750/2) (ix : n 789=outputIndex.val)
    (naturalWidth : ∀i∈ids,(n i).bits.length≤B)
    (width : WidthBank slots B v) (good : Good slots v)
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B)
    (entryValid : ∀i,(a.get i).Valid) (outputMeta : b.MetadataWidth (emissionWidth B))
    (positive : 0<addressValue b.width) (fits : emissionWidth B≤addressValue b.width)
    (separated : b.Separated) (disjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank ids n s.val) (ready : Ready slots v s)
    (cache : a.Ready s) (output : b.OutputReady s) :
    ∃cost t w,Executes input tape (emissionCode j part) cost s t ∧ cost≤emissionCost B ∧
      Ready slots (termsValues M D a (coordinates n) j part parities v) t ∧
      Good slots (termsValues M D a (coordinates n) j part parities v) ∧
      WidthBank slots (emissionWidth B) (termsValues M D a (coordinates n) j part parities v) ∧
      NatAssign.Bank ids w t.val ∧ (∀i∈ids,(w i).bits.length≤emissionWidth B) ∧
      (∀i∈retained,w i=n i) ∧ a.Ready t ∧
      (b.set outputIndex (termsValues M D a (coordinates n) j part parities v 27)).OutputReady t ∧
      t.val.memory=b.writeMemory outputIndex
        (termsValues M D a (coordinates n) j part parities v 27) s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧
      t.val.output=s.val.output ∧
      (∀i,10 ≤ i→i∉changed→i≠37→t.val.tapes i=s.val.tapes i) ∧
      t.val.tapes 4=s.val.tapes 4 := by
  obtain ⟨c0,u,w,e0,h0,ru,gu,wu,nu,nwu,keep,au,f0⟩ := terms_executes M D a parities j part
    n v B hM hD half naturalWidth width good metadata entryWidth entryValid input tape s natural ready cache
  have iu : w 789=outputIndex.val := (keep 789 (by decide)).trans ix
  have iw := nu 789 (by decide)
  rw [iu] at iw
  obtain ⟨c1,t,e1,h1,rt,bt,mem,f1⟩ := PartArray.writeAt_executes b slots 789 (by decide) 27 (by decide)
    _ outputIndex positive ((wu 27 (by decide)).mono fits) separated input tape outputIndex.val.bits
    (by simp) u ru (output_ready_after_terms output au f0) iw
  have nt : NatAssign.Bank ids w t.val := by
    intro i hi
    have lower : 10 ≤ i := by
      simp only [ids,extra,SelectedParameters.Compare.ids,Finset.mem_union,Finset.mem_Icc,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have ne : i≠37 := by
      simp only [ids,extra,SelectedParameters.Compare.ids,Finset.mem_union,Finset.mem_Icc,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact RationalAccumulator.word_of_eq (f1.2.2.2.1 i (Or.inr lower) ne) (nu i hi)
  have cacheFinal : a.Ready t := au.write_output_frame disjoint outputIndex _ mem f1 bt.scratch bt.seven
  have price := b.writeCost_bound (emissionWidth B) outputMeta outputIndex.val.bits
    (by rw [←iu];exact nwu 789 (by decide))
    (termsValues M D a (coordinates n) j part parities v 27)
  change c1≤b.writeCost outputIndex.val.bits _ at h1
  refine ⟨c0+c1,t,w,e0.seq e1,Nat.add_le_add h0 (h1.trans price),rt,gu,wu,nt,nwu,keep,cacheFinal,bt,
    mem.trans ?_,f1.1.trans f0.inputHead,f1.2.1.trans f0.randomCursor,
    f1.2.2.1.trans f0.output,?_,(f1.2.2.2.1 4 (Or.inl rfl) (by decide)).trans f0.four⟩
  · rw [f0.memory]
  · intro i hi ho hn
    exact (f1.2.2.2.1 i (Or.inr hi) hn).trans (f0.tapes i hi ho)

#print axioms emission_executes
end Maxwell.Continuum.Calibration.SeedRoot
