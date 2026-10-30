import Maxwell.Continuum.ChebyshevWaveRuntimeCosineStages

/-! A fixed executable two-pass cosine Fourier coefficient producer. Both
sample loops, all saves and reloads, the zero-index correction, and cleanup
run on the Boolean machine and have an explicit charged cost. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def coefficientWidth (Q P grid W : ℕ) : ℕ := 16*(sumBankWidth Q P W grid+1)
def cosineCode : Code := .seq coefficientCode (.seq savePairCode
  (.seq (program restartInstructions) (.seq (WordReplace.code 681 680)
    (.seq coefficientCode (.seq restorePairCode (.seq clearPairCode finishControl.code))))))
def cosineCost (Q P grid W : ℕ) : ℕ :=
  let B := coefficientWidth Q P grid W
  2*coefficientCost Q P grid W+252*(B+1)+(12*operationCost (4*(B+1))+1)+
    (15*grid.bits.length+21)+(36*B+24)+(8*operationCost (256*(B+1))+1)

theorem grid_outside_cosine : 681∉cosineWorkspace := by
  intro h
  rcases Finset.mem_union.mp h with h|h
  · rcases Finset.mem_insert.mp h with h|h
    · omega
    · exact (Finset.mem_union.mp h).elim
        (Phase.Runtime.metadata_outside_workspace ids 681 (by decide))
        (DyadicFloor.high_outside_workspace ids 681 (by decide))
  · have := savedPorts_range 681 h;omega

theorem cosine_executes (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hW : 1 ≤ W) (hgrid : grid.bits.length ≤ W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s)
    (hn : Word s.val 680 grid) (hnSaved : Word s.val 681 grid) (hz : ∀i∈savedPorts,Blank s.val i) :
    ∃cost t,Executes input tape cosineCode cost s t ∧ cost ≤ cosineCost Q P grid W ∧
      LoopReady Q P (cosineValues Q P grid v) t ∧ Blank t.val 680 ∧ Word t.val 681 grid ∧
      (∀i∈savedPorts,Blank t.val i) ∧ WidthBank ids (256*(coefficientWidth Q P grid W+1))
        (cosineValues Q P grid v) ∧ BinaryPrecision.Frame cosineWorkspace s.val t.val := by
  let B := coefficientWidth Q P grid W
  have hwFirst : WidthBank ids B (coefficientValues Q P grid v) :=
    coefficientValues_width Q P grid W v hw hW hgrid hcount hone
  obtain ⟨c0,s0,e0,hc0,r0,z0,f0⟩ := coefficient_executes Q P grid W v hw hg hW hgrid hcount hone
    input tape s hs hn
  have hz0 : ∀i∈savedPorts,Blank s0.val i := by
    intro i hi
    exact blank_of_eq (f0.tapes i (fun hm => Finset.disjoint_left.mp savedPorts_disjoint_sum hi hm)) (hz i hi)
  obtain ⟨c1,s1,e1,hc1,r1,x1,y1,f1⟩ := save_pair_executes Q P B _ hwFirst input tape s0 r0 hz0
  have z1 : Blank s1.val 680 := blank_of_eq (f1.tapes 680 (by decide)) z0
  obtain ⟨c2,s2,e2,hc2,r2,f2⟩ := restart_executes Q P B _ hwFirst input tape s1 r1
  have z2 : Blank s2.val 680 := blank_of_eq
    (f2.tapes 680 (RationalDataflow.outside_workspace ids 680 (by decide))) z1
  have pref : BinaryPrecision.Frame cosineWorkspace s.val s2.val :=
    (f0.mono Finset.subset_union_left).trans ((f1.mono Finset.subset_union_right).trans
      (f2.mono arithmetic_subset_cosine))
  have n2 : Word s2.val 681 grid := word_of_eq (pref.tapes 681 grid_outside_cosine) hnSaved
  have x2 := stored_arithmetic_frame (Or.inl rfl) x1 f2
  have y2 := stored_arithmetic_frame (Or.inr rfl) y1 f2
  obtain ⟨s3,e3,n3,f3⟩ := WordReplace.executes 681 680 (by decide) input tape grid.bits [] s2 n2
    ((zero_word_iff_blank _ _).mpr z2)
  have e3' : Executes input tape (WordReplace.code 681 680) (15*grid.bits.length+21) s2 s3 := by
    simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add] using e3
  have cf3 := StoredParts.copy_frame f3
  have r3 := r2.counter_frame cf3
  have x3 := x2.frame cf3 (by decide)
  have y3 := y2.frame cf3 (by decide)
  have hwRestart := restart_width Q P grid W v hw hW
  have hgRestart := restart_good _ (coefficientValues_good Q P grid v hg)
  obtain ⟨c4,s4,e4,hc4,r4,z4,f4⟩ := coefficient_executes Q P grid W _ hwRestart hgRestart hW hgrid
    (restart_counter _) (restart_one Q P grid v hone) input tape s3 r3 n3
  have hwSecond : WidthBank ids B (secondValues Q P grid v) :=
    coefficientValues_width Q P grid W _ hwRestart hW hgrid (restart_counter _)
      (restart_one Q P grid v hone)
  have x4 := stored_sum_frame (Or.inl rfl) x3 f4
  have y4 := stored_sum_frame (Or.inr rfl) y3 f4
  obtain ⟨c5,s5,e5,hc5,r5,x5,y5,f5⟩ := restore_pair_executes Q P B (secondValues Q P grid v)
    (coefficientValues Q P grid v 8) (coefficientValues Q P grid v 9) hwSecond
    (hwFirst 8 (by decide)) (hwFirst 9 (by decide)) input tape s4 r4 x4 y4
  obtain ⟨c6,s6,e6,hc6,r6,z6,f6⟩ := clear_pair_executes Q P B (pairedValues Q P grid v)
    _ _ (hwFirst 8 (by decide)) (hwFirst 9 (by decide)) input tape s5 r5 x5 y5
  have hwPair : WidthBank ids B (pairedValues Q P grid v) :=
    (hwSecond.update 2 (hwFirst 8 (by decide))).update 3 (hwFirst 9 (by decide))
  have hB : 2 ≤ B := by dsimp [B,coefficientWidth];omega
  obtain ⟨c7,t,e7,hc7,r7,hw7,f7⟩ := finish_executes Q P B _ hwPair (pairedValues_good Q P grid v hg)
    hB input tape s6 r6
  have full : BinaryPrecision.Frame cosineWorkspace s.val t.val := pref.trans
    ((cf3.mono (by simp [cosineWorkspace,sumWorkspace])).trans
      ((f4.mono Finset.subset_union_left).trans ((f5.mono arithmetic_subset_cosine).trans
        ((f6.mono Finset.subset_union_right).trans (f7.mono arithmetic_subset_cosine)))))
  refine ⟨c0+(c1+(c2+((15*grid.bits.length+21)+(c4+(c5+(c6+c7)))))),t,
    e0.seq (e1.seq (e2.seq (e3'.seq (e4.seq (e5.seq (e6.seq e7)))))),?_,r7,?_,
    word_of_eq (full.tapes 681 grid_outside_cosine) hnSaved,?_,hw7,full⟩
  · change _ ≤ 2*coefficientCost Q P grid W+252*(B+1)+(12*operationCost (4*(B+1))+1)+
      (15*grid.bits.length+21)+(36*B+24)+(8*operationCost (256*(B+1))+1)
    omega
  · exact blank_of_eq (f7.tapes 680 (RationalDataflow.outside_workspace ids 680 (by decide)))
      (blank_of_eq (f6.tapes 680 (by decide))
        (blank_of_eq (f5.tapes 680 (RationalDataflow.outside_workspace ids 680 (by decide))) z4))
  · intro i hi
    apply blank_of_eq (f7.tapes i _) (z6 i hi)
    have hh := savedPorts_range i hi
    exact RationalDataflow.outside_workspace ids i (by omega)

theorem cosine_computes (grid D K Q P W : ℕ) [NeZero grid] (q : ℚ) (j : ℕ)
    (hq : |q| ≤ Q) (hk : |2*Real.pi*(q:ℝ)| ≤ K) (hj : j ≤ D)
    (hresolution : waveDegree K P+D ≤ grid) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hW : 1 ≤ W) (hgrid : grid.bits.length ≤ W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (hi : SumInput grid q (j:ℤ) 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s)
    (hn : Word s.val 680 grid) (hnSaved : Word s.val 681 grid) (hz : ∀i∈savedPorts,Blank s.val i) :
    ∃t : Store,
      (runPriced (cosineCode.compile.next input tape) (cosineCost Q P grid W+1) s.val).finished=
        some (t.place cosineCode.size) ∧
      (runPriced (cosineCode.compile.next input tape) (cosineCost Q P grid W+1) s.val).instructions ≤
        cosineCost Q P grid W ∧ LoopReady Q P (cosineValues Q P grid v) t ∧
      Blank t.val 680 ∧ (∀i∈savedPorts,Blank t.val i) ∧
      ‖waveCosineCoefficient (2*Real.pi*(q:ℝ)) j-storedCenter (cosineValues Q P grid v)‖ ≤ 18*(1/2:ℝ)^P := by
  obtain ⟨c,t,e,hc,rt,zt,_,ht,_,_⟩ := cosine_executes Q P grid W v hw hg hW hgrid hcount hone
    input tape s hs hn hnSaved hz
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (cosineCost Q P grid W+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hc,rt,zt,ht,cosineValues_error grid D K P q Q j hq hk hj hresolution v hg hi hz0 hz1⟩

#print axioms cosine_executes
#print axioms cosine_computes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
