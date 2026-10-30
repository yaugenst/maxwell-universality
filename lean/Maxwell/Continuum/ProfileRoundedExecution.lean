import Maxwell.Continuum.ProfileFloorFrames

/-! A fixed profile-coefficient evaluator, from runtime dimensions and
frequency through literal samples, DFTs and signed dyadic floor. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def roundedCode : Code := .seq cosineCode (DyadicFloor.StoredPower.code 9 9)
def roundedWidth (grid U : ℕ) : ℕ := cosineWidth grid U+roundedRawWidth U+1
def roundedWorkspace : Finset ℕ := cosineWorkspace∪DyadicFloor.StoredPower.workspace dftRegisters
def roundedCost (grid D P U W indexLength oldLength : ℕ) : ℕ :=
  cosineCost grid D P U W indexLength oldLength+DyadicFloor.costBound P (cosineWidth grid U)

structure RoundedResult (grid D P U j : ℕ) (s : Store) where
  values : ℕ→Parts
  ready : Ready dftRegisters values s
  width : WidthBank dftRegisters (roundedWidth grid U) values
  good : Good dftRegisters values
  resultWidth : (values 9).Width (roundedRawWidth U)
  resultDenominator : (values 9).denominator=1
  resultValue : (values 9).value=(DyadicFloor.result P (sampledParts grid D P j)).value
  phaseClean : Phase.Runtime.Clean s.val
  glueClean : Glue.Clean s.val
  floorClean : DyadicFloor.Clean s.val
  parameters : DFTParameters D P s
  power : Word s.val 144 (2^P)

theorem rounded_executes (grid D P U j W : ℕ)
    (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hj : j≤U) (hW : 1≤W)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v) (saved : Parts) (hsaved : saved.Width W)
    (jword oldWord : List Bool) (hjword : addressValue jword=j)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready dftRegisters v s) (hp : Phase.Runtime.Clean s.val) (hz : Glue.Clean s.val)
    (hfloor : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P))
    (hm : DFTParameters D P s) (hgrid : Word s.val 664 grid)
    (hindex : BankArray.Word s.val 700 jword) (hc : BankArray.Word s.val 201 oldWord)
    (hstore : StoredParts.Stored 701 saved s.val) :
    ∃cost t finalWord outputSaved,Executes input tape roundedCode cost s t ∧
      Nonempty (RoundedResult grid D P U j t) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=grid.bits.length ∧
      StoredParts.Stored 701 outputSaved t.val ∧ outputSaved.Width (dftRawWidth U) ∧
      BinaryPrecision.Frame roundedWorkspace s.val t.val ∧
      cost≤roundedCost grid D P U W jword.length oldWord.length := by
  obtain ⟨c0,s0,word0,saved0,e0,result0,count0,len0,store0,ws0,f0,h0⟩ := cosine_executes grid D P U j W
    hg0 hg hD hP hj hW v hw saved hsaved jword oldWord hjword input tape s hr hp hz hm hgrid hindex hc hstore
  obtain ⟨r0⟩ := result0
  have clean0 := floorClean_cosine_frame hfloor f0
  have power0 := word_of_eq (f0.tapes 144 floor_power_outside_cosine) hpower
  obtain ⟨c1,t,e1,h1,rt,zt,powt,f1⟩ := DyadicFloor.StoredPower.executes dftRegisters P 9 9 (by decide)
    (by decide) r0.values (cosineWidth grid U) r0.width (r0.good 9 (by decide))
    input tape s0 r0.ready clean0 power0
  let vt := Function.update r0.values 9 (DyadicFloor.result P (r0.values 9))
  change Ready dftRegisters vt t at rt
  have outputWidth : (vt 9).Width (roundedRawWidth U) := by
    simpa only [vt,Function.update_self] using
      (DyadicFloor.result_raw_width P (sampledRawWidth U) (r0.values 9) r0.resultWidth).mono
        (show 2*sampledRawWidth U+P+2≤roundedRawWidth U by unfold roundedRawWidth;omega)
  have bankWidth : WidthBank dftRegisters (roundedWidth grid U) vt :=
    (r0.width.mono (by unfold roundedWidth;omega)).update 9
      (outputWidth.mono (by unfold roundedWidth;omega))
  have good : Good dftRegisters vt := r0.good.update 9 (DyadicFloor.result_valid _ _)
  have outputValue : (vt 9).value=(DyadicFloor.result P (sampledParts grid D P j)).value := by
    simp only [vt,Function.update_self]
    rw [DyadicFloor.result_value _ _ (r0.good 9 (by decide)),r0.resultValue,
      DyadicFloor.result_value _ _ (sampledParts_valid _ _ _ _ hg0)]
  have ct : BankArray.Word t.val 201 word0 := by
    obtain ⟨o,ho⟩ := count0
    exact ⟨o,(f1.tapes 201 (by decide)).trans ho⟩
  refine ⟨c0+c1,t,word0,saved0,e0.seq e1,?_,ct,len0,store0.frame f1 (by decide),ws0,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right),?_⟩
  · exact ⟨⟨vt,rt,bankWidth,good,outputWidth,rfl,outputValue,
      phaseClean_floor_frame r0.phaseClean rt f1,glueClean_floor_frame r0.glueClean rt f1,
      zt,r0.parameters.floor_frame f1,powt⟩⟩
  · unfold roundedCost
    omega

theorem RoundedResult.profile_value (N j U : ℕ) {s : Store}
    (h : RoundedResult (profileGrid N) (profileDegree N) (profileWorkBits N) U j s) :
    (h.values 9).value=((roundedCoefficient N j).numerator:ℚ) :=
  h.resultValue.trans (roundedIntegerParts_value N j)

#print axioms rounded_executes
#print axioms RoundedResult.profile_value
end Maxwell.Continuum.Profile.Runtime
