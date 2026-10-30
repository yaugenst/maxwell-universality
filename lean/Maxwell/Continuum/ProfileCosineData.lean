import Maxwell.Continuum.ProfileDFTStoredExecution
import Maxwell.Continuum.RationalDataflowStoredParts
import Maxwell.Continuum.RationalDataflowControlTraceResult

/-! The two signed Fourier coefficients are combined by one fixed
runtime zero-index decision. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def cosineCombine : Control := .positive 5 (.step (.binary .add 9 10 9) .done) .done
def cosineWidth (grid U : ℕ) : ℕ := dftNormalizationWidth grid U+2*dftRawWidth U+2
def cosineWorkspace : Finset ℕ := dftWorkspace∪StoredParts.ports 701
def cosineCode : Code := .seq (dftCode true) (.seq (StoredParts.saveCode 701 9)
  (.seq (dftCode false) (.seq (StoredParts.restoreCode 701 10) cosineCombine.code)))
def cosineCost (grid D P U W indexLength oldLength : ℕ) : ℕ :=
  dftCost grid D P U W indexLength oldLength+
    63*(W+dftRawWidth U+1)+
    dftCost grid D P U (dftNormalizationWidth grid U) indexLength grid.bits.length+
    63*(cosineWidth grid U+1)+(2*operationCost (cosineWidth grid U)+1)

theorem cosineCombine_valid : cosineCombine.Valid dftRegisters := by
  simp [cosineCombine,Control.Valid,Instruction.Valid,dftRegisters]

theorem cosineCombine_admissible (v : ℕ→Parts) : cosineCombine.AdmissibleTrace v := by
  simp [cosineCombine,Control.AdmissibleTrace,Instruction.Admissible]

theorem cosineCombine_width (grid U : ℕ) (v : ℕ→Parts)
    (hw : WidthBank dftRegisters (cosineWidth grid U) v)
    (h9 : (v 9).Width (dftRawWidth U)) (h10 : (v 10).Width (dftRawWidth U)) :
    cosineCombine.WidthTrace dftRegisters (cosineWidth grid U) v := by
  refine ⟨hw,?_⟩
  split_ifs
  · exact ⟨hw,trivial,hw.update 9 ((h10.add h9).mono (by unfold cosineWidth;omega))⟩
  · exact hw

theorem cosineCombine_result (grid D P U j : ℕ) (v : ℕ→Parts)
    (h5 : v 5=integerArgument (j:ℤ)) (h9 : (v 9).Valid) (h10 : (v 10).Valid)
    (w9 : (v 9).Width (dftRawWidth U)) (w10 : (v 10).Width (dftRawWidth U))
    (e9 : (v 9).value=(dftParts grid D P (-(j:ℤ))).value)
    (e10 : (v 10).value=(dftParts grid D P (j:ℤ)).value) (hg : 0<grid) :
    (cosineCombine.evaluate v 9).Valid ∧
      (cosineCombine.evaluate v 9).Width (sampledRawWidth U) ∧
      (cosineCombine.evaluate v 9).value=(sampledParts grid D P j).value := by
  have test : (0<(v 5).value)↔0<j := by rw [h5,integerArgument_value];norm_cast
  by_cases hz : j=0
  · subst j
    simp only [cosineCombine,Control.evaluate,test,lt_self_iff_false,ite_false]
    refine ⟨h9,w9.mono (by unfold sampledRawWidth;omega),?_⟩
    simpa [sampledParts] using e9
  · have hj : 0<j := by omega
    simp only [cosineCombine,Control.evaluate,test,hj,ite_true,Instruction.update,Function.update_self,
      BinaryOp.eval]
    refine ⟨Parts.add_valid h10 h9,(w10.add w9).mono (by unfold sampledRawWidth;omega),?_⟩
    rw [Parts.add_value _ _ h10 h9,e10,e9,sampledParts,ite_eq_right hz,
      Parts.add_value _ _ (dftParts_valid _ _ _ _ hg) (dftParts_valid _ _ _ _ hg)]

theorem stored701_dft_disjoint : Disjoint (StoredParts.ports 701) dftWorkspace := by
  apply Finset.disjoint_left.mpr
  intro i hi
  apply dft_external i
  simp only [StoredParts.ports,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem phaseClean_save {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame (StoredParts.ports 701) s.val t.val) : Phase.Runtime.Clean t.val := by
  have hd : Disjoint (StoredParts.ports 701) PhaseMachine.Runtime.ids := by decide
  intro i hi
  apply blank_of_eq (f.tapes i _) (h i hi)
  exact fun hm => Finset.disjoint_left.mp hd hm (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))

theorem glueClean_save {s t : Store} (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame (StoredParts.ports 701) s.val t.val) : Glue.Clean t.val := by
  have hd : Disjoint (StoredParts.ports 701) GlueMachine.Runtime.ids := by decide
  intro i hi
  apply blank_of_eq (f.tapes i _) (h i hi)
  exact fun hm => Finset.disjoint_left.mp hd hm (Finset.mem_of_mem_erase hi)

theorem DFTParameters.save_frame {D P : ℕ} {s t : Store} (h : DFTParameters D P s)
    (f : BinaryPrecision.Frame (StoredParts.ports 701) s.val t.val) : DFTParameters D P t :=
  ⟨word_of_eq (f.tapes 663 (by decide)) h.precision,word_of_eq (f.tapes 667 (by decide)) h.one,
    word_of_eq (f.tapes 668 (by decide)) h.guard,word_of_eq (f.tapes 669 (by decide)) h.range,
    word_of_eq (f.tapes 652 (by decide)) h.phaseRange,word_of_eq (f.tapes 653 (by decide)) h.phasePrecision,
    word_of_eq (f.tapes 640 (by decide)) h.gluePrecision⟩

structure CosineResult (grid D P U j : ℕ) (s : Store) where
  values : ℕ→Parts
  ready : Ready dftRegisters values s
  width : WidthBank dftRegisters (cosineWidth grid U) values
  good : Good dftRegisters values
  resultWidth : (values 9).Width (sampledRawWidth U)
  resultValue : (values 9).value=(sampledParts grid D P j).value
  phaseClean : Phase.Runtime.Clean s.val
  glueClean : Glue.Clean s.val
  parameters : DFTParameters D P s

#print axioms cosineCombine_result
end Maxwell.Continuum.Profile.Runtime
