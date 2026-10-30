import Maxwell.Continuum.ProfileDFTInvariant
import Maxwell.Continuum.ProfileDFTStepWidths

/-! Actual fixed counted traversal of all profile DFT samples. The loop
reads each index from its runtime counter; no input table of sample values
or per-index code is supplied. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def dftBodyCost (grid D P U wordLength : ℕ) : ℕ :=
  6*dftLoopWidth grid U+31*wordLength+39+dftStepCost D P (dftLoopWidth grid U)

theorem dft_loop_body_executes (S : Finset ℕ) (hS : Finset.range 10⊆S)
    (grid D P U : ℕ) (k : ℤ) (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U)
    (hk : k.natAbs≤U) (r : ℕ) (xs : List Bool) (origin : ℤ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hi : DFTInvariant S grid D P U k (r+1) s)
    (hc : s.val.tapes 201=BitTape.shifted xs origin) (hx : addressValue xs=r) :
    ∃cost t,Executes input tape dftLoopBody cost s t ∧
      DFTInvariant S grid D P U k r t ∧ t.val.tapes 201=BitTape.shifted xs origin ∧
      BinaryPrecision.Frame (angularWorkspace S) s.val t.val ∧
      cost≤dftBodyCost grid D P U xs.length := by
  obtain ⟨h⟩ := hi
  have hr : r<grid := by have := h.bound;omega
  have hzero : 0∈S := hS (by decide)
  obtain ⟨c0,s0,e0,h0,r0,f0⟩ := NaturalChannel.executes S .positive 201 0 hzero (by decide)
    h.values xs input tape s h.ready ⟨origin,hc⟩
  rw [hx,argument_counter_replace h.values grid r h.argumentNegative h.argumentDenominator] at r0
  let v := Function.update h.values 0 (gridArgument grid r)
  change Ready S v s0 at r0
  have f0a : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val s0.val := by
    apply f0.mono
    intro i hi
    have he : i=positivePort 0 := by simpa only [NaturalChannel.port,Finset.mem_singleton] using hi
    subst i
    exact Finset.mem_union_right _ (cell_mem hzero (by simp [cellPorts]))
  have zp0 := phaseClean_arithmetic h.phaseClean r0 f0a
  have zg0 := glueClean_arithmetic h.glueClean r0 f0a
  have hm0 := h.parameters.channel_frame f0
  have harg : (v 0).Width (U+1) := by
    simpa only [v,Function.update_self] using gridArgument_width grid r U hg (by omega)
  have hfreq : v 5=integerArgument (-k) := by simpa only [v,Function.update_of_ne (by decide : (5:ℕ)≠0)] using h.frequency
  have hfwidth : (v 5).Width (U+1) := by
    rw [hfreq]
    exact integerArgument_width (-k) U (by simpa only [Int.natAbs_neg] using hk)
  have hbase : U+1≤dftLoopWidth grid U := by unfold dftLoopWidth dftScratchWidth;omega
  have hw : WidthBank S (dftLoopWidth grid U) v := h.width.update 0 (by
    exact (gridArgument_width grid r U hg (by omega)).mono hbase)
  have hvalid : (v 0).Valid := by simpa only [v,Function.update_self] using gridArgument_valid grid r hg0
  have ha : (v 9).Width (dftAccumulatorWidth grid (r+1) U) := by
    simpa only [v,Function.update_of_ne (by decide : (9:ℕ)≠0)] using h.accumulatorWidth
  have hav : (v 9).Valid := by simpa only [v,Function.update_of_ne (by decide : (9:ℕ)≠0)] using h.accumulatorValid
  have hsmall : dftScratchWidth U≤dftLoopWidth grid U := by unfold dftLoopWidth;omega
  have hbudget : dftAccumulatorWidth grid (r+1) U+dftTermWidth U+1≤dftLoopWidth grid U := by
    have hh := Nat.mul_le_mul_right (dftTermWidth U+1) (show grid-(r+1)+1≤grid+1 by omega)
    unfold dftAccumulatorWidth dftLoopWidth
    nlinarith only [hh]
  obtain ⟨c1,t,e1,h1,rt,zpt,zgt,hmt,ft⟩ := dft_step_executes S hS D P U
    (dftAccumulatorWidth grid (r+1) U) (dftLoopWidth grid U) v hw harg hfwidth hvalid ha hD hP hsmall hbudget
    input tape s0 r0 zp0 zg0 hm0
  have hstep := dftStepValues_actual_term grid D P r k v (by simp [v]) hfreq
  have htermv := dftTerm_valid grid D P k r hg0
  have htermw := dftTerm_width grid D P U k r hg hD hP hk (by omega)
  have newWidth := dftStepValues_width S D P U (dftAccumulatorWidth grid (r+1) U)
    (dftLoopWidth grid U) v hw harg hfwidth ha hD hP hsmall hbudget
  have hcount : t.val.tapes 201=BitTape.shifted xs origin :=
    (ft.tapes 201 (scalar_external S 201 (by decide))).trans
      ((f0.tapes 201 (by decide)).trans hc)
  refine ⟨c0+c1,t,e0.seq e1,?_,hcount,(f0a.mono (arithmetic_sub_scalar S)).trans ft,?_⟩
  · refine ⟨⟨by omega,dftStepValues D P v,rt,newWidth,
      dftStepValues_good S hS D P v (h.good.update 0 (gridArgument_valid _ _ hg0)),
      ?_,?_,?_,?_,?_,?_,zpt,zgt,hmt⟩⟩
    · rw [dftStepValues_zero]
      simp only [v,Function.update_self,gridArgument]
    · rw [dftStepValues_zero]
      simp only [v,Function.update_self,gridArgument]
    · exact (dftStepValues_frequency D P v).trans hfreq
    · rw [hstep.2]
      exact Parts.add_valid hav htermv
    · rw [hstep.2]
      apply (ha.add htermw).mono
      have he : grid-r=grid-(r+1)+1 := by omega
      unfold dftAccumulatorWidth
      rw [he,Nat.add_mul,Nat.one_mul]
      omega
    · rw [hstep.2,Parts.add_value _ _ hav htermv]
      have hs : (v 9).value=∑j∈Finset.Ico (r+1) grid,(dftTerm grid D P k j).value := by
        simpa only [v,Function.update_of_ne (by decide : (9:ℕ)≠0)] using h.accumulatorValue
      rw [hs,Finset.sum_eq_sum_Ico_succ_bot hr]
      ring
  · have hwold := (h.width 0 hzero).1
    simp only [NaturalChannel.port,dataValues_positive] at h0
    unfold dftBodyCost
    omega

theorem dft_loop_executes (S : Finset ℕ) (hS : Finset.range 10⊆S)
    (grid D P U : ℕ) (k : ℤ) (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U)
    (hk : k.natAbs≤U) (xs : List Bool) (origin : ℤ) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (hi : DFTInvariant S grid D P U k grid s)
    (hc : s.val.tapes 201=BitTape.shifted xs origin) (hx : addressValue xs=grid) :
    ∃cost t finalWord,Executes input tape dftLoopCode cost s t ∧
      DFTInvariant S grid D P U k 0 t ∧ t.val.tapes 201=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧
      BinaryPrecision.Frame (insert 201 (angularWorkspace S)) s.val t.val ∧
      cost≤(grid+1)*(13*xs.length+15)+grid*dftBodyCost grid D P U xs.length := by
  let inv (r : ℕ) (t : Store) : Prop := DFTInvariant S grid D P U k r t ∧
    BinaryPrecision.Frame (insert 201 (angularWorkspace S)) s.val t.val
  have stable : ∀r a b,CountedShifted.Frame 201 a b→inv r a→inv r b := by
    intro r a b hf hh
    have f : BinaryPrecision.Frame {201} a.val b.val :=
      ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,fun i hi =>
        hf.2.2.2.2.2.1 i (by simpa only [Finset.mem_singleton] using hi)⟩
    exact ⟨hh.1.count_frame hf,hh.2.trans (f.mono (by simp))⟩
  obtain ⟨cost,t,ys,he,ht,hword,hlen,_,hcost⟩ := counted_executes_sized 201 origin dftLoopBody
    input tape xs.length inv (fun _ => dftBodyCost grid D P U xs.length) stable (by
      intro r ys a hh hword hvalue hlength
      obtain ⟨c,b,eb,ib,wb,fb,cb⟩ := dft_loop_body_executes S hS grid D P U k hg0 hg hD hP hk
        r ys origin input tape a hh.1 hword hvalue
      exact ⟨c,b,eb,⟨ib,hh.2.trans (fb.mono (Finset.subset_insert _ _))⟩,wb,by simpa only [hlength] using cb⟩)
    grid xs s hx hc rfl ⟨hi,BinaryPrecision.Frame.refl _ _⟩
  exact ⟨cost,t,ys,he,ht.1,hword,hlen,ht.2,by
    simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost⟩

#print axioms dft_loop_executes
end Maxwell.Continuum.Profile.Runtime
