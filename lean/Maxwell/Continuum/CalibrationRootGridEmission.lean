import Maxwell.Continuum.CalibrationRootGridOutputFrame
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! Actual indexed output of a computed root Fourier coefficient component.
The target array receives raw signed numerator channels and a positive
denominator, with every arithmetic and memory-write operation charged. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def component (grid N : ℕ) [NeZero grid] (scale : ℚ) (frequency : Fin 3→ℤ) (entry : ℕ) : ℚ :=
  if entry=10 then (Calibration.rationalRootCoefficient grid scale N frequency).re.center
  else (Calibration.rationalRootCoefficient grid scale N frequency).im.center

theorem CoefficientState.component_value {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : CoefficientState S grid N frequency B I initial s) (entry : ℕ) (he : entry=10 ∨ entry=11) :
    (h.parts entry).value=component grid N (initial 9).value frequency entry := by
  rcases he with rfl|rfl
  · simpa only [component,ite_true] using h.real_value
  · simpa only [component,show (11:ℕ)≠10 by decide,ite_false] using h.imag_value

def storeCoefficientCode (entry : ℕ) : Code := .seq coefficientCode (PartArray.writeAtCode 201 entry)

theorem storeCoefficient_executes {T : ℕ} (a : PartArray.Table T) (target : Fin T)
    (entry : ℕ) (he : entry=10 ∨ entry=11) (S : Finset ℕ) (hS : coefficientInputs⊆S)
    (grid N : ℕ) [NeZero grid] (frequency : Fin 3→ℤ) (B I W : ℕ) (hB : 1≤B) (hI : 1≤I)
    (n : ℕ→ℕ) (initial : ℕ→Parts)
    (hgrid : n 331=grid)
    (hfrequency : ∀i,![n 336,n 337,n 338] i=
      ((-(PeriodicSampling.Product.frequency grid frequency)) i).val)
    (hzero : ∀i∈NaturalQuotient.workPorts,n i=0)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hcw : ∀i∈clockIds,(n i).bits.length≤B)
    (hw : WidthBank S I initial) (hg : Good S initial)
    (hm : a.MetadataWidth W) (hfit : coefficientRawWidth grid N B I≤addressValue a.width)
    (hsep : a.Separated) (index : List Bool) (hindex : addressValue index=target.val) (hlen : index.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S initial s) (hb : NatAssign.Bank ids n s.val) (hc : NatAssign.Bank clockIds n s.val)
    (hz : ∀i,i<5 → Blank s.val i) (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hprec : Word s.val 653 N)
    (ha : a.OutputReady s) (hi : BankArray.Word s.val 201 index) :
    ∃ (cost : ℕ) (t : Store) (out : CoefficientState S grid N frequency B I initial t),
      Executes input tape (storeCoefficientCode entry) cost s t ∧
      cost≤coefficientCost grid N B I+2^20*(W+5)^2 ∧
      (a.set target (out.parts entry)).OutputReady t ∧
      ((a.set target (out.parts entry)).get target).value=component grid N (initial 9).value frequency entry ∧
      (out.parts entry).Valid ∧ t.val.memory=a.writeMemory target (out.parts entry) s.val.memory ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  have heS : entry∈S := hS (by rcases he with rfl|rfl <;> decide)
  obtain ⟨c0,u,e0,h0,ho,f0⟩ := coefficient_executes S hS grid N frequency B I hB hI n initial
    hgrid hfrequency hzero hn hcw hw hg input tape s hs hb hc hz hglue hphase hp hq hprec
  rcases ho with ⟨out⟩
  have au := coefficient_outputReady a ha f0 out.rational_bank
  have iu := BankArray.word_of_eq (f0.tapes 201 (coefficient_protected S 201 (by simp))) hi
  have hpositive : 0<addressValue a.width := by
    have hh : 0<coefficientRawWidth grid N B I := by unfold coefficientRawWidth;omega
    omega
  have wf := (out.width entry heS).mono hfit
  obtain ⟨c1,t,e1,h1,r1,a1,m1,f1⟩ := PartArray.writeAt_executes a S 201 (by decide) entry heS
    out.parts target hpositive wf hsep input tape index hindex u out.rational_bank au iu
  let result := out.write_frame f1 r1
  refine ⟨c0+c1,t,result,e0.seq e1,?_,a1,?_,out.good entry heS,?_,?_,f1.2.2.1.trans f0.output⟩
  · change c1≤a.writeCost index (out.parts entry) at h1
    have hwrite := a.writeCost_bound W hm index hlen (out.parts entry)
    omega
  · change ((a.set target (out.parts entry)).get target).value=_
    rw [a.set_get target (out.parts entry) wf]
    exact out.component_value entry he
  · change t.val.memory=a.writeMemory target (out.parts entry) s.val.memory
    rw [m1,f0.memory]
  · exact (f1.2.2.2.1 201 (Or.inr (by decide)) (by decide)).trans
      (f0.tapes 201 (coefficient_protected S 201 (by simp)))

#print axioms storeCoefficient_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
