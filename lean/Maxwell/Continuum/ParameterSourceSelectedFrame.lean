import Maxwell.Continuum.ParameterSourceSelected

/-! Retained geometry and fresh banks after source-driven parameter selection.
These facts supply actual operands to later allocation and calibration code. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceSelected
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RoutingPorts.Complete
open Maxwell.Logical.Routing Maxwell.Composition
open RationalAccumulator (Word Blank)
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
  {hn : 0<S.n} {hm2 : 2≤S.nnz} {e : ℕ} {s : Store}

theorem retainedWork_bound : ∀i∈retainedWork,i<4261 := by
  intro i hi
  rcases Finset.mem_union.mp hi with first|second
  · have bound : ∀j∈SourcePrepare.work,j≤2340 := by decide +kernel
    have :=bound i first
    omega
  · obtain ⟨j,hj,eq⟩:=Finset.mem_image.mp second
    have bound : ∀j∈OuterMachine.workspace,j<2300 := by decide +kernel
    have :=bound j hj
    change TapeBlockSwap.index 4 1257 3000 j=i at eq
    simp only [TapeBlockSwap.index] at eq
    split_ifs at eq <;> omega

theorem Result.fresh (h : Result p S hm hn hm2 e s) (i : ℕ)
    (lo : 1261≤ i) (outside : i∉retainedWork) : Blank s.val i := by
  obtain ⟨previous,geometry,frame⟩:=h.saved
  exact RationalAccumulator.blank_of_eq (frame.tapes i outside) (geometry.fresh i lo)

theorem Result.fresh_large (h : Result p S hm hn hm2 e s) (i : ℕ)
    (lo : 4261≤ i) : Blank s.val i := by
  apply h.fresh i (by omega)
  intro member
  have :=retainedWork_bound i member
  omega

theorem Result.geometryWords (h : Result p S hm hn hm2 e s) :
    let precision:=(SelectedInput.input p S hm).precision
    Word s.val 1250 (GeometryStartup.outputWidth (SourceGeometry.history S precision)) ∧
    Word s.val 1252 (GeometryStartup.outputBase (SourceGeometry.history S precision)) ∧
    Word s.val 1253 (SourceDecorationEnumeration.packedLength (SourceEmission.geometry S precision)) := by
  obtain ⟨previous,geometry,frame⟩:=h.saved
  have kept (i : ℕ) (lo : 5≤ i) (hi : i≤1260) : s.val.tapes i=previous.val.tapes i :=
    frame.tapes i (Finset.disjoint_left.mp retainedWork_disjoint (Finset.mem_Icc.mpr ⟨lo,hi⟩))
  exact ⟨RationalAccumulator.word_of_eq (kept 1250 (by decide) (by decide)) geometry.output.wordWidth,
    RationalAccumulator.word_of_eq (kept 1252 (by decide) (by decide)) geometry.output.baseWord,
    RationalAccumulator.word_of_eq (kept 1253 (by decide) (by decide)) geometry.cursorWord⟩

theorem Result.storedGeometry (h : Result p S hm hn hm2 e s) :
    let precision:=(SelectedInput.input p S hm).precision
    SourceDecorationEnumeration.StoredGeometry (SourceEmission.geometry S precision)
      (GeometryStartup.outputBase (SourceGeometry.history S precision))
      (GeometryStartup.outputWidth (SourceGeometry.history S precision)) s.val.memory := by
  obtain ⟨previous,geometry,frame⟩:=h.saved
  rw [frame.memory]
  exact geometry.stored

theorem Result.lengthWord (h : Result p S hm hn hm2 e s) :
    Word s.val 2221 (stageLength (SourceOuter.exponent p S hm e)) := by
  obtain ⟨v,bank,_,output⟩:=h.parameters
  have word:=bank 2221 (by decide +kernel)
  have fixed : SourceOuter.relocation 2221=2221 := by decide +kernel
  rw [fixed,output.core.length] at word
  exact word

theorem Result.spacingWord (h : Result p S hm hn hm2 e s) :
    Word s.val 2227 (stageSpacing (sourceInput p S hm) e (SourceOuter.exponent p S hm e)) ∧
    Word s.val 2228 (3^stageSpacing (sourceInput p S hm) e (SourceOuter.exponent p S hm e)) := by
  obtain ⟨v,bank,_,output⟩:=h.parameters
  have first:=bank 2227 (by decide +kernel)
  have second:=bank 2228 (by decide +kernel)
  have f1 : SourceOuter.relocation 2227=2227 := by decide +kernel
  have f2 : SourceOuter.relocation 2228=2228 := by decide +kernel
  rw [f1,output.spacing.spacing,SourceOuter.data_input] at first
  rw [f2,output.spacing.zetaDen,SourceOuter.data_input] at second
  exact ⟨first,second⟩

#print axioms Result.geometryWords
#print axioms Result.storedGeometry
#print axioms Result.spacingWord
end Maxwell.Continuum.Parameters.SourceSelected
