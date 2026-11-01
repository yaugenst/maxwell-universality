import Maxwell.Continuum.CalibrationFiniteSeedSparse
import Maxwell.Continuum.RationalDataflowFixedWidths
import Maxwell.Continuum.RationalDataflowControlResults
import Maxwell.Continuum.RationalDataflowArrayIndexRead
import Maxwell.Continuum.RationalDataflowArrayFrame
import Maxwell.Cost.Structured.Footprint

/-! One charged cache lookup and its contribution to a seed convolution.
Raw slots28..30 retain the three computed seed components,24 receives the
cache entry, and27 accumulates the requested real or imaginary output. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def slots : Finset ℕ := Finset.Icc 24 31
def scalarPart (z : RationalComplex) (part : Fin 2) : ℚ := if part.val=0 then z.1 else z.2
def cachePart (part : Fin 2) : Fin 2 := ⟨1-part.val,by have := part.isLt;omega⟩
def sign (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) : ℚ :=
  if part.val=0 then -seedSign parity j else seedSign parity j
def termControl (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) : Control :=
  .step (.literal 25 (sign parity j part))
    (.step (.binary .mul 26 24 (28+j.val))
      (.step (.binary .mul 26 26 25) (.step (.binary .add 27 27 26) .done)))
def termWidth (B : ℕ) : ℕ := 16*(B+2)
def termCost (B : ℕ) : ℕ := 4*operationCost (termWidth B)+1
def readTermCode (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) : Code :=
  .seq (PartArray.readAtCode 765 24) (termControl parity j part).code
def readTermCost (B : ℕ) : ℕ := 2^20*(B+5)^2+termCost B

theorem sign_width (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) :
    (Parts.literal (sign parity j part)).Width 1 := by
  obtain ⟨a,b,c⟩ := parity
  cases a <;> cases b <;> cases c <;> fin_cases j <;> fin_cases part <;>
    norm_num [sign,seedSign,Parts.Width,Parts.literal]

theorem term_valid (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) :
    (termControl parity j part).Valid slots := by
  have hj := j.isLt
  simp [termControl,Control.Valid,Instruction.Valid,slots]
  omega
theorem term_admissible (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts) :
    (termControl parity j part).AdmissibleTrace v := by
  simp [termControl,Control.AdmissibleTrace,Instruction.Admissible]

theorem term_value (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts)
    (good : Good slots v) :
    ((termControl parity j part).evaluate v 27).value=
      (v 27).value+(v 24).value*(v (28+j.val)).value*sign parity j part := by
  have he := congrFun ((termControl parity j part).evaluate_value slots
    (term_valid parity j part) v good (term_admissible parity j part v)) 27
  have hj := j.isLt
  simpa [termControl,Control.rationalEvaluate,Instruction.rationalUpdate,valueBank,
    show 28+j.val≠25 by omega] using he

theorem term_keep (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts)
    (i : ℕ) (hi : i≠25 ∧ i≠26 ∧ i≠27) : (termControl parity j part).evaluate v i=v i := by
  simp [termControl,Control.evaluate,Instruction.update,hi.1,hi.2.1,hi.2.2]

theorem scalar_contribution (N : ℕ) (parity : Corner.Parity) (j : Fin 3) (part : Fin 2)
    (z : RationalComplex) :
    scalarPart z (cachePart part)*seedComponent N j*sign parity j part=
      scalarPart (rationalComplexMul z (Supercell.seedCoefficient N parity j)) part := by
  fin_cases part <;> simp [scalarPart,cachePart,sign,rationalComplexMul,Supercell.seedCoefficient] <;> ring

theorem term_executes (parity : Corner.Parity) (j : Fin 3) (part : Fin 2)
    (v : ℕ→Parts) (B : ℕ) (width : WidthBank slots B v) (good : Good slots v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready slots v s) :
    ∃cost t,Executes input tape (termControl parity j part).code cost s t ∧ cost≤termCost B ∧
      Ready slots ((termControl parity j part).evaluate v) t ∧
      Good slots ((termControl parity j part).evaluate v) ∧
      WidthBank slots (termWidth B) ((termControl parity j part).evaluate v) ∧
      BinaryPrecision.Frame (RationalDataflow.workspace slots) s.val t.val := by
  have literals : (termControl parity j part).LiteralsFit (B+1) := by
    refine ⟨(sign_width parity j part).mono (by omega),?_,?_,?_,?_⟩ <;> trivial
  have trace := (termControl parity j part).automatic_widthTrace slots (term_valid parity j part)
    v (B+1) (width.mono (by omega)) literals
  change (termControl parity j part).WidthTrace slots (termWidth B) v at trace
  obtain ⟨cost,t,ex,bound,rt,frame⟩ := (termControl parity j part).executes slots
    (term_valid parity j part) v (termWidth B) trace good (term_admissible parity j part v)
    input tape s ready
  exact ⟨cost,t,ex,bound,rt,(termControl parity j part).evaluate_good slots
    (term_valid parity j part) v good (term_admissible parity j part v),trace.result,frame⟩

theorem readTerm_executes {T : ℕ} (a : PartArray.Table T) (index : Fin T)
    (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts) (B : ℕ)
    (width : WidthBank slots B v) (good : Good slots v) (metadata : a.MetadataWidth B)
    (entryWidth : (a.get index).Width B) (entryValid : (a.get index).Valid)
    (indexWidth : index.val.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready slots v s)
    (table : a.Ready s) (word : RationalAccumulator.Word s.val 765 index.val) :
    ∃cost t,Executes input tape (readTermCode parity j part) cost s t ∧ cost≤readTermCost B ∧
      Ready slots ((termControl parity j part).evaluate (Function.update v 24 (a.get index))) t ∧
      Good slots ((termControl parity j part).evaluate (Function.update v 24 (a.get index))) ∧
      WidthBank slots (termWidth B)
        ((termControl parity j part).evaluate (Function.update v 24 (a.get index))) ∧
      a.Ready t ∧ t.val.output=s.val.output ∧ t.val.memory=s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧
      (∀i,10 ≤ i→i∉RationalDataflow.workspace slots→t.val.tapes i=s.val.tapes i) ∧
      t.val.tapes 4=s.val.tapes 4 := by
  obtain ⟨c0,u,e0,h0,ru,au,_,f0⟩ := PartArray.readAt_executes a slots 765 24
    (by decide) (by decide) (by decide) v input tape index.val.bits index
    (by simp) s ready table word
  obtain ⟨c1,t,e1,h1,rt,gt,wt,f1⟩ := term_executes parity j part
    (Function.update v 24 (a.get index)) B (width.update 24 entryWidth) (good.update 24 entryValid)
    input tape u ru
  have readBound := a.readCost_bound B metadata index.val.bits indexWidth (v 24) (width 24 (by decide))
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add (h0.trans readBound) h1,rt,gt,wt,
    au.arithmetic_frame slots f1 rt.2,f1.output.trans f0.output,f1.memory.trans f0.memory,
    f1.inputHead.trans f0.inputHead,f1.randomCursor.trans f0.randomCursor,?_,?_⟩
  · intro i hi ho
    exact (f1.tapes i ho).trans (f0.tapes i hi (fun hm=>ho
      (Finset.mem_union_right _ (cell_mem (by decide : 24∈slots) hm))))
  · exact (f1.tapes 4 (by decide)).trans
      (e0.protectsTape 4 (by decide : (PartArray.readAtCode 765 24).protectsTape 4=true))

#print axioms readTerm_executes
end Maxwell.Continuum.Calibration.SeedRoot
