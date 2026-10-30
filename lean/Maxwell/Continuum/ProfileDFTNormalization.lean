import Maxwell.Continuum.ProfileDFTInitialization

/-! The final division by the runtime grid size is executed on the actual
DFT accumulator. The result equals the literal finite rational DFT. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def dftNormalizationWidth (grid U : ℕ) : ℕ := dftLoopWidth grid U+U+2
def dftNormalizeCode : Code := .seq (Instruction.code (.literal 10 1))
  (.seq (NaturalChannel.code .denominator 664 10) (Instruction.code (.binary .mul 9 10 9)))
def dftNormalizeCost (grid U : ℕ) : ℕ :=
  2*operationCost (dftNormalizationWidth grid U)+31*grid.bits.length+45
def dftNormalizedValues (grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update v 10 (gridArgument grid 1)) 9 ((gridArgument grid 1).mul (v 9))

structure DFTResult (grid D P U : ℕ) (k : ℤ) (s : Store) where
  values : ℕ→Parts
  ready : Ready dftRegisters values s
  width : WidthBank dftRegisters (dftNormalizationWidth grid U) values
  good : Good dftRegisters values
  frequency : values 5=integerArgument (-k)
  resultValid : (values 9).Valid
  resultWidth : (values 9).Width (dftRawWidth U)
  resultValue : (values 9).value=(dftParts grid D P k).value
  phaseClean : Phase.Runtime.Clean s.val
  glueClean : Glue.Clean s.val
  parameters : DFTParameters D P s

theorem dft_normalize_executes (grid D P U : ℕ) (k : ℤ) (hg0 : 0<grid) (hg : grid≤U)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hi : DFTState dftRegisters grid D P U k 0 s)
    (hgrid : Word s.val 664 grid) :
    ∃cost t,Executes input tape dftNormalizeCode cost s t ∧
      Nonempty (DFTResult grid D P U k t) ∧
      BinaryPrecision.Frame (angularWorkspace dftRegisters) s.val t.val ∧
      cost≤dftNormalizeCost grid U := by
  let W := dftNormalizationWidth grid U
  have hW : 1≤W := by dsimp [W,dftNormalizationWidth];omega
  have hw : WidthBank dftRegisters W hi.values := hi.width.mono (by dsimp [W,dftNormalizationWidth];omega)
  have one : (Parts.literal 1).Width W := (Parts.literal_width RationalWords.width_one).mono hW
  obtain ⟨c0,s0,e0,h0,r0,f0⟩ := Instruction.executes dftRegisters (.literal 10 1) (by
    change (10:ℕ)∈dftRegisters;decide)
    hi.values W hw one input tape s hi.ready
  let v0 := Function.update hi.values 10 (Parts.literal 1)
  change Ready dftRegisters v0 s0 at r0
  have p0 := phaseClean_arithmetic hi.phaseClean r0 f0
  have z0 := glueClean_arithmetic hi.glueClean r0 f0
  have m0 := hi.parameters.arithmetic_frame f0
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := NaturalChannel.executes dftRegisters .denominator 664 10
    (by decide) (by decide) v0 grid.bits input tape s0 r0
    (word_of_eq (f0.tapes 664 (RationalDataflow.outside_workspace _ _ (by decide))) hgrid)
  have eqv : Function.update v0 10 (NaturalChannel.replace .denominator (v0 10) (addressValue grid.bits))=
      Function.update hi.values 10 (gridArgument grid 1) := by
    simp [v0,NaturalChannel.replace,Parts.literal,gridArgument]
  rw [eqv] at r1
  let v1 := Function.update hi.values 10 (gridArgument grid 1)
  change Ready dftRegisters v1 s1 at r1
  have f1a : BinaryPrecision.Frame (RationalDataflow.workspace dftRegisters) s0.val s1.val :=
    f1.mono (by
      intro i hi
      have he : i=denominatorPort 10 := by simpa only [NaturalChannel.port,Finset.mem_singleton] using hi
      subst i
      exact Finset.mem_union_right _ (NaturalChannel.port_mem .denominator dftRegisters 10 (by decide)))
  have f01 := f0.trans f1a
  have p1 := phaseClean_arithmetic p0 r1 f1a
  have z1 := glueClean_arithmetic z0 r1 f1a
  have m1 := m0.arithmetic_frame f1a
  have hn : (gridArgument grid 1).Width (U+1) := gridArgument_width grid 1 U hg (by omega)
  have hw1 : WidthBank dftRegisters W v1 := hw.update 10 (hn.mono (by dsimp [W,dftNormalizationWidth];omega))
  obtain ⟨c2,t,e2,h2,r2,f2⟩ := Instruction.executes dftRegisters (.binary .mul 9 10 9)
    (by change (9:ℕ)∈dftRegisters ∧ (10:ℕ)∈dftRegisters ∧ (9:ℕ)∈dftRegisters;decide)
    v1 W hw1 trivial input tape s1 r1
  have eqout : (Instruction.binary .mul 9 10 9).update v1=dftNormalizedValues grid hi.values := by
    simp [Instruction.update,BinaryOp.eval,v1,dftNormalizedValues]
  rw [eqout] at r2
  have output : dftNormalizedValues grid hi.values 9=(gridArgument grid 1).mul (hi.values 9) := by
    simp [dftNormalizedValues]
  have hacc : (hi.values 9).Width (grid*(dftTermWidth U+1)+1) := by
    simpa only [dftAccumulatorWidth,Nat.sub_zero] using hi.accumulatorWidth
  have hresult : (dftNormalizedValues grid hi.values 9).Width (dftRawWidth U) := by
    rw [output]
    exact (hn.mul hacc).mono (by
      have hx := Nat.mul_le_mul_right (dftTermWidth U+1) hg
      unfold dftRawWidth
      omega)
  have hresultW : ((gridArgument grid 1).mul (hi.values 9)).Width W :=
    (hn.mul hacc).mono (by
      dsimp [W,dftNormalizationWidth]
      unfold dftLoopWidth
      nlinarith only [Nat.zero_le (dftScratchWidth U),Nat.zero_le (dftTermWidth U)])
  have resultValue : (dftNormalizedValues grid hi.values 9).value=(dftParts grid D P k).value := by
    rw [output,Parts.mul_value,hi.accumulatorValue]
    unfold dftParts
    rw [Parts.mul_value,
      Calibration.RawCutoff.sum_value _ _ (fun i _ => dftTerm_valid _ _ _ _ i hg0)]
    rw [Finset.range_eq_Ico]
  have p2 := phaseClean_arithmetic p1 r2 f2
  have z2 := glueClean_arithmetic z1 r2 f2
  have m2 := m1.arithmetic_frame f2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,
    (f01.trans f2).mono (arithmetic_sub_scalar _),?_⟩
  · refine ⟨⟨dftNormalizedValues grid hi.values,r2,hw1.update 9 hresultW,
      (hi.good.update 10 (gridArgument_valid _ _ hg0)).update 9
        (Parts.mul_valid (gridArgument_valid _ _ hg0) hi.accumulatorValid),
      ?_,?_,hresult,resultValue,p2,z2,m2⟩⟩
    · simpa [dftNormalizedValues] using hi.frequency
    · rw [output]
      exact Parts.mul_valid (gridArgument_valid _ _ hg0) hi.accumulatorValid
  · have den : (v0 10).denominator.bits.length=1 := by simp [v0,Parts.literal]
    simp only [NaturalChannel.port,dataValues_denominator,den] at h1
    unfold dftNormalizeCost
    change c0≤operationCost (dftNormalizationWidth grid U) at h0
    change c2≤operationCost (dftNormalizationWidth grid U) at h2
    omega

#print axioms dft_normalize_executes
end Maxwell.Continuum.Profile.Runtime
