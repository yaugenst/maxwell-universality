import Maxwell.Continuum.ProfileDFTInitializationData

/-! Charged fixed initialization, including replacement of an arbitrary
previous countdown word. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def dftInitializeCost (W grid jLength oldLength : ℕ) : ℕ :=
  11*operationCost W+6*oldLength+46*grid.bits.length+31*jLength+128

theorem DFTParameters.arithmetic_frame {S : Finset ℕ} {D P : ℕ} {s t : Store}
    (h : DFTParameters D P s) (f : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val) :
    DFTParameters D P t := by
  have keep (i : ℕ) (hi : 107 ≤ i ∧ i < 1000) : t.val.tapes i=s.val.tapes i :=
    f.tapes i (RationalDataflow.outside_workspace S i (Or.inr hi))
  exact ⟨word_of_eq (keep 663 (by decide)) h.precision,word_of_eq (keep 667 (by decide)) h.one,
    word_of_eq (keep 668 (by decide)) h.guard,word_of_eq (keep 669 (by decide)) h.range,
    word_of_eq (keep 652 (by decide)) h.phaseRange,word_of_eq (keep 653 (by decide)) h.phasePrecision,
    word_of_eq (keep 640 (by decide)) h.gluePrecision⟩

theorem dft_initialize_executes (negative : Bool) (grid D P U j W : ℕ)
    (hg0 : 0<grid) (hg : grid≤U) (hj : j≤U) (hW : 1≤W)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v) (jword oldWord : List Bool)
    (hjword : addressValue jword=j) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready dftRegisters v s) (hp : Phase.Runtime.Clean s.val) (hz : Glue.Clean s.val)
    (hm : DFTParameters D P s) (hgrid : Word s.val 664 grid)
    (hindex : BankArray.Word s.val 700 jword) (hc : BankArray.Word s.val 201 oldWord) :
    ∃cost t,Executes input tape (dftInitializeCode negative) cost s t ∧
      DFTInvariant dftRegisters grid D P U (dftFrequency negative j) grid t ∧
      Word t.val 201 grid ∧
      BinaryPrecision.Frame (insert 201 (angularWorkspace dftRegisters)) s.val t.val ∧
      cost≤dftInitializeCost W grid jword.length oldWord.length := by
  obtain ⟨c0,s0,e0,h0,r0,f0⟩ := program_executes dftRegisters dftReset dftReset_valid v W
    (dftReset_width v W hW hw) input tape s hr
  change Ready dftRegisters (dftResetValues v) s0 at r0
  have p0 := phaseClean_arithmetic hp r0 f0
  have z0 := glueClean_arithmetic hz r0 f0
  have m0 := hm.arithmetic_frame f0
  have keep0 (i : ℕ) (hi : 107 ≤ i ∧ i < 1000) : s0.val.tapes i=s.val.tapes i :=
    f0.tapes i (RationalDataflow.outside_workspace dftRegisters i (Or.inr hi))
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := NaturalChannel.executes dftRegisters .denominator 664 0
    (by decide) (by decide) (dftResetValues v) grid.bits input tape s0 r0
    (word_of_eq (keep0 664 (by decide)) hgrid)
  rw [addressValue_bits,dftArgument_replace] at r1
  have f1a : BinaryPrecision.Frame (RationalDataflow.workspace dftRegisters) s0.val s1.val :=
    f1.mono (by
      intro i hi
      have he : i=denominatorPort 0 := by simpa only [NaturalChannel.port,Finset.mem_singleton] using hi
      subst i
      exact Finset.mem_union_right _ (NaturalChannel.port_mem .denominator dftRegisters 0 (by decide)))
  have f01 := f0.trans f1a
  have p1 := phaseClean_arithmetic p0 r1 f1a
  have z1 := glueClean_arithmetic z0 r1 f1a
  have m1 := m0.arithmetic_frame f1a
  obtain ⟨c2,s2,e2,h2,r2,f2⟩ := NaturalChannel.executes dftRegisters (dftFrequencyChannel negative) 700 5
    (by decide) (by cases negative <;> decide) (dftArgumentValues grid v) jword input tape s1 r1
    (by obtain ⟨o,ho⟩ := hindex
        exact ⟨o,(f01.tapes 700 (RationalDataflow.outside_workspace _ _ (by decide))).trans ho⟩)
  rw [hjword,dftFrequency_replace] at r2
  have f2a : BinaryPrecision.Frame (RationalDataflow.workspace dftRegisters) s1.val s2.val :=
    f2.mono (by
      intro i hi
      have he : i=NaturalChannel.port (dftFrequencyChannel negative) 5 := by
        simpa only [Finset.mem_singleton] using hi
      subst i
      exact Finset.mem_union_right _ (NaturalChannel.port_mem _ _ 5 (by decide)))
  have f012 := f01.trans f2a
  have p2 := phaseClean_arithmetic p1 r2 f2a
  have z2 := glueClean_arithmetic z1 r2 f2a
  have m2 := m1.arithmetic_frame f2a
  have keep2 (i : ℕ) (hi : 107 ≤ i ∧ i < 1000) : s2.val.tapes i=s.val.tapes i :=
    f012.tapes i (RationalDataflow.outside_workspace dftRegisters i (Or.inr hi))
  obtain ⟨t,e3,c3,f3⟩ := WordReplace.executes 664 201 (by decide) input tape grid.bits oldWord s2
    (word_of_eq (keep2 664 (by decide)) hgrid) (by
      obtain ⟨o,ho⟩ := hc
      exact ⟨o,(keep2 201 (by decide)).trans ho⟩)
  have r3 := r2.wordReplace_frame (RationalDataflow.outside_workspace dftRegisters 201 (by decide)) f3
  have p3 : Phase.Runtime.Clean t.val := by
    intro i hi
    apply blank_of_eq (f3.2.2.2.2.2.1 i _) (p2 i hi)
    intro he
    subst i
    exact (show (201:ℕ)∉PhaseMachine.Runtime.ids by decide)
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
  have z3 : Glue.Clean t.val := by
    intro i hi
    apply blank_of_eq (f3.2.2.2.2.2.1 i _) (z2 i hi)
    intro he
    subst i
    exact (show (201:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hi)
  have m3 : DFTParameters D P t :=
    ⟨word_of_eq (f3.2.2.2.2.2.1 663 (by decide)) m2.precision,
      word_of_eq (f3.2.2.2.2.2.1 667 (by decide)) m2.one,
      word_of_eq (f3.2.2.2.2.2.1 668 (by decide)) m2.guard,
      word_of_eq (f3.2.2.2.2.2.1 669 (by decide)) m2.range,
      word_of_eq (f3.2.2.2.2.2.1 652 (by decide)) m2.phaseRange,
      word_of_eq (f3.2.2.2.2.2.1 653 (by decide)) m2.phasePrecision,
      word_of_eq (f3.2.2.2.2.2.1 640 (by decide)) m2.gluePrecision⟩
  have frame3 : BinaryPrecision.Frame {201} s2.val t.val :=
    ⟨f3.1,f3.2.1,f3.2.2.1,f3.2.2.2.1,f3.2.2.2.2.1,
      fun i hi => f3.2.2.2.2.2.1 i (by simpa only [Finset.mem_singleton] using hi)⟩
  refine ⟨_,t,e0.seq (e1.seq (e2.seq e3)),?_,c3,
    (f012.mono ((arithmetic_sub_scalar dftRegisters).trans (Finset.subset_insert _ _))).trans
      (frame3.mono (by simp)),?_⟩
  · refine ⟨⟨le_rfl,dftInitialValues negative grid j v,r3,?_,?_,?_,?_,
      dftInitialValues_frequency _ _ _ _,?_,?_,?_,p3,z3,m3⟩⟩
    · exact (dftInitialValues_width negative grid j U v hg hj).mono
        (by unfold dftLoopWidth dftScratchWidth;omega)
    · have hg : Good dftRegisters (dftResetValues v) := by
        intro i hi
        rw [dftResetValues_eq,ite_eq_left (Finset.mem_range.mp hi)]
        exact Parts.literal_valid 0
      exact (hg.update 0 (gridArgument_valid _ _ hg0)).update 5 (integerArgument_valid _)
    · rw [dftInitialValues_zero];rfl
    · rw [dftInitialValues_zero];rfl
    · rw [dftInitialValues_accumulator];exact Parts.literal_valid 0
    · rw [dftInitialValues_accumulator]
      simp [dftAccumulatorWidth,Parts.Width,Parts.literal]
    · rw [dftInitialValues_accumulator,Parts.literal_value]
      simp
  · simp only [show dftReset.length=11 by rfl] at h0
    have one : (dftResetValues v 0).denominator.bits.length=1 := by
      simp [dftResetValues_eq,Parts.literal]
    simp only [NaturalChannel.port,dataValues_denominator,one] at h1
    have zero : dataValues (dftArgumentValues grid v) (NaturalChannel.port (dftFrequencyChannel negative) 5)=0 := by
      cases negative <;> simp [dftFrequencyChannel,NaturalChannel.port,dataValues_positive,dataValues_negative,
        dftArgumentValues,dftResetValues_eq,Parts.literal]
    rw [zero] at h2
    simp only [Nat.zero_bits,List.length_nil] at h2
    unfold dftInitializeCost
    omega

#print axioms dft_initialize_executes
end Maxwell.Continuum.Profile.Runtime
