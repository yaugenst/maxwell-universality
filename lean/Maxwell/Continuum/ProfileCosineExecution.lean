import Maxwell.Continuum.ProfileCosineData

/-! Actual fixed execution of both signed DFTs, external storage between
them, and the zero-frequency cosine convention. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem cosine_executes (grid D P U j W : ℕ)
    (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hj : j≤U) (hW : 1≤W)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v) (saved : Parts) (hsaved : saved.Width W)
    (jword oldWord : List Bool) (hjword : addressValue jword=j)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready dftRegisters v s) (hp : Phase.Runtime.Clean s.val) (hz : Glue.Clean s.val)
    (hm : DFTParameters D P s) (hgrid : Word s.val 664 grid)
    (hindex : BankArray.Word s.val 700 jword) (hc : BankArray.Word s.val 201 oldWord)
    (hstore : StoredParts.Stored 701 saved s.val) :
    ∃cost t finalWord outputSaved,Executes input tape cosineCode cost s t ∧
      Nonempty (CosineResult grid D P U j t) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=grid.bits.length ∧
      StoredParts.Stored 701 outputSaved t.val ∧ outputSaved.Width (dftRawWidth U) ∧
      BinaryPrecision.Frame cosineWorkspace s.val t.val ∧
      cost≤cosineCost grid D P U W jword.length oldWord.length := by
  obtain ⟨c0,s0,word0,e0,hresult0,count0,len0,f0,h0⟩ := dft_executes true grid D P U j W
    hg0 hg hD hP hj hW v hw jword oldWord hjword input tape s hr hp hz hm hgrid hindex hc
  obtain ⟨r0⟩ := hresult0
  have saved0 := hstore.frame f0 stored701_dft_disjoint
  obtain ⟨c1,s1,e1,h1,b1,saved1,f1⟩ := StoredParts.save_executes dftRegisters 701 9 (by decide)
    (by decide) (by decide) r0.values saved (W+dftRawWidth U)
    (r0.resultWidth.mono (by omega)) (hsaved.mono (by omega)) input tape s0 r0.ready saved0
  have p1 := phaseClean_save r0.phaseClean f1
  have z1 := glueClean_save r0.glueClean f1
  have m1 := r0.parameters.save_frame f1
  have f01 : BinaryPrecision.Frame cosineWorkspace s.val s1.val :=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have outside (i : ℕ) (hi : i=664 ∨ i=700) : i∉cosineWorkspace := by
    simp only [cosineWorkspace,Finset.mem_union,not_or]
    exact ⟨dft_external i (by omega),by rcases hi with rfl|rfl <;> decide⟩
  have grid1 := word_of_eq (f01.tapes 664 (outside 664 (Or.inl rfl))) hgrid
  have index1 : BankArray.Word s1.val 700 jword := by
    obtain ⟨o,ho⟩ := hindex
    exact ⟨o,(f01.tapes 700 (outside 700 (Or.inr rfl))).trans ho⟩
  have count1 : BankArray.Word s1.val 201 word0 := by
    obtain ⟨o,ho⟩ := count0
    exact ⟨o,(f1.tapes 201 (by decide)).trans ho⟩
  obtain ⟨c2,s2,word2,e2,hresult2,count2,len2,f2,h2⟩ := dft_executes false grid D P U j
    (dftNormalizationWidth grid U) hg0 hg hD hP hj (by unfold dftNormalizationWidth;omega)
    r0.values r0.width jword word0 hjword input tape s1 b1 p1 z1 m1 grid1 index1 count1
  obtain ⟨r2⟩ := hresult2
  have saved2 := saved1.frame f2 stored701_dft_disjoint
  have hn : dftNormalizationWidth grid U≤cosineWidth grid U := by unfold cosineWidth;omega
  have hs : dftRawWidth U≤cosineWidth grid U := by unfold cosineWidth;omega
  obtain ⟨c3,s3,e3,h3,b3,saved3,f3⟩ := StoredParts.restore_executes dftRegisters 701 10
    (by decide) (by decide) r2.values (r0.values 9) (cosineWidth grid U)
    ((r2.width 10 (by decide)).mono hn) (r0.resultWidth.mono hs) input tape s2 r2.ready saved2
  let v3 := Function.update r2.values 10 (r0.values 9)
  change Ready dftRegisters v3 s3 at b3
  have f3a : BinaryPrecision.Frame (RationalDataflow.workspace dftRegisters) s2.val s3.val :=
    f3.mono (fun _ hi => Finset.mem_union_right _ (cell_mem (show 10∈dftRegisters by decide) hi))
  have p3 := phaseClean_arithmetic r2.phaseClean b3 f3a
  have z3 := glueClean_arithmetic r2.glueClean b3 f3a
  have m3 := r2.parameters.arithmetic_frame f3a
  have w3 : WidthBank dftRegisters (cosineWidth grid U) v3 :=
    (r2.width.mono hn).update 10 (r0.resultWidth.mono hs)
  have g3 : Good dftRegisters v3 := r2.good.update 10 r0.resultValid
  have w39 : (v3 9).Width (dftRawWidth U) := by simpa [v3] using r2.resultWidth
  have w310 : (v3 10).Width (dftRawWidth U) := by simpa [v3] using r0.resultWidth
  have trace := cosineCombine_width grid U v3 w3 w39 w310
  obtain ⟨c4,t,e4,h4,bt,f4⟩ := cosineCombine.executes dftRegisters cosineCombine_valid v3
    (cosineWidth grid U) trace g3 (cosineCombine_admissible v3) input tape s3 b3
  have hfreq : v3 5=integerArgument (j:ℤ) := by simpa [v3,dftFrequency] using r2.frequency
  have e39 : (v3 9).value=(dftParts grid D P (-(j:ℤ))).value := by
    simpa [v3,dftFrequency] using r2.resultValue
  have e310 : (v3 10).value=(dftParts grid D P (j:ℤ)).value := by
    simpa [v3,dftFrequency] using r0.resultValue
  have result := cosineCombine_result grid D P U j v3 hfreq (g3 9 (by decide))
    (g3 10 (by decide)) w39 w310 e39 e310 hg0
  have p4 := phaseClean_arithmetic p3 bt f4
  have z4 := glueClean_arithmetic z3 bt f4
  have m4 := m3.arithmetic_frame f4
  have f34 := f3a.trans f4
  have count4 : BankArray.Word t.val 201 word2 := by
    obtain ⟨o,ho⟩ := count2
    exact ⟨o,(f34.tapes 201 (RationalDataflow.outside_workspace _ _ (by decide))).trans ho⟩
  have saved4 := saved3.frame f4 (by
    apply Finset.disjoint_left.mpr
    intro i hi
    apply RationalDataflow.outside_workspace dftRegisters i
    simp only [StoredParts.ports,Finset.mem_insert,Finset.mem_singleton] at hi
    omega)
  refine ⟨c0+(c1+(c2+(c3+c4))),t,word2,r0.values 9,
    e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,count4,len2,saved4,r0.resultWidth,
    f01.trans ((f2.mono Finset.subset_union_left).trans
      (f34.mono ((arithmetic_sub_scalar dftRegisters).trans
        ((Finset.subset_insert _ _).trans Finset.subset_union_left)))),?_⟩
  · exact ⟨⟨cosineCombine.evaluate v3,bt,trace.result,
      cosineCombine.evaluate_good dftRegisters cosineCombine_valid v3 g3 (cosineCombine_admissible v3),
      result.2.1,result.2.2,p4,z4,m4⟩⟩
  · rw [len0] at h2
    simp only [show cosineCombine.steps=2 by rfl] at h4
    unfold cosineCost
    omega

#print axioms cosine_executes
end Maxwell.Continuum.Profile.Runtime
