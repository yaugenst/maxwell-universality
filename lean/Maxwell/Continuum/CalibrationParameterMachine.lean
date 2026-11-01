import Maxwell.Continuum.CalibrationParameterData
import Maxwell.Cost.Structured.NatAssign.BankFrame

/-! Execute the dimension arithmetic and all three binary-length scans.
Only stored operands and ordinary scratch tapes occur in the input contract. -/
namespace Maxwell.Continuum.Calibration.ParameterMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

def assignmentWidth (xs : List NatAssign.Instruction) (B : ℕ) : ℕ := 2^xs.length*(B+108)
def assignmentCost (xs : List NatAssign.Instruction) (B : ℕ) : ℕ := 3000*8^xs.length*(B+109)^2
def scanCost (B : ℕ) : ℕ := 48*(B+1)^2+1
def firstWidth (B : ℕ) : ℕ := assignmentWidth prepare B
def secondWidth (B : ℕ) : ℕ := assignmentWidth sizeInstructions (firstWidth B)
def width (B : ℕ) : ℕ := assignmentWidth finish (secondWidth B)
def costBound (B : ℕ) : ℕ := assignmentCost prepare B+
  (scanCost (firstWidth B)+(scanCost (firstWidth B)+
    (assignmentCost sizeInstructions (firstWidth B)+
      (scanCost (secondWidth B)+assignmentCost finish (secondWidth B)))))

theorem assignment_executes (xs : List NatAssign.Instruction) (hv : ∀a∈xs,a.Valid ids)
    (hl : ∀a∈xs,a.literalWidth≤107) (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code xs) cost s t ∧ cost≤assignmentCost xs B ∧
      NatAssign.Bank ids (NatAssign.values xs v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(NatAssign.values xs v i).bits.length≤assignmentWidth xs B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have wh : ∀i∈ids,(v i).bits.length≤B+107 := fun i hi=>(hw i hi).trans (by omega)
  have lh : ∀a∈xs,a.literalWidth≤B+107 := fun a ha=>(hl a ha).trans (by omega)
  obtain ⟨cost,t,execution,bound,bt,st,frame⟩ := NatAssign.executes ids ids_lower xs hv v input tape s bank scratch
  refine ⟨cost,t,execution,bound.trans ?_,bt,st,?_,frame.mono (NatAssign.changes_subset ids xs hv)⟩
  · simpa only [assignmentCost,Nat.add_assoc] using NatAssign.price_bound ids xs hv v (B+107) wh lh
  · intro i hi
    exact (Nat.le_add_right _ 1).trans (by
      simpa only [assignmentWidth,Nat.add_assoc] using NatAssign.values_width ids xs hv v (B+107) wh lh i hi)

theorem executes (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈ids,(v i).bits.length≤B)
    (hC : v 4403=2^(4*MasterConstants.exponent))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound B ∧
      NatAssign.Bank ids (values v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(values v i).bits.length≤width B) ∧
      Outputs (v 4400) (v 4401) (v 4402) (values v) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,sa,wa,f0⟩ := assignment_executes prepare valid_prepare (by decide +kernel)
    v B hw input tape s bank scratch
  change NatAssign.Bank ids (prepared v) a.val at ba
  change ∀i∈ids,(prepared v i).bits.length≤firstWidth B at wa
  obtain ⟨c1,b,e1,h1,bb,sb,wb,f1⟩ := NatAssign.wordLength_executes ids 4400 4404 (firstWidth B)
    (by decide) (by decide) (by decide) (by decide) (prepared v) (prepared_fields v).2.2.1
    wa input tape a ba sa
  let vb := Function.update (prepared v) 4404 (v 4400).bits.length
  change NatAssign.Bank ids vb b.val at bb
  change ∀i∈ids,(vb i).bits.length≤firstWidth B at wb
  obtain ⟨c2,c,e2,h2,bc,sc,wc,f2⟩ := NatAssign.wordLength_executes ids 4406 4407 (firstWidth B)
    (by decide) (by decide) (by decide) (by decide) vb
    (by simpa only [vb,Function.update_of_ne (by decide : 4407≠4404)] using (prepared_fields v).2.2.2.1)
    wb input tape b bb sb
  have eqMeasured : Function.update vb 4407 (vb 4406).bits.length=measured v := by
    simp only [vb,measured,Function.update_of_ne (by decide : 4406≠4404),(prepared_fields v).2.1]
  rw [eqMeasured] at bc wc
  obtain ⟨c3,d,e3,h3,bd,sd,wd,f3⟩ := assignment_executes sizeInstructions valid_size (by decide)
    (measured v) (firstWidth B) wc input tape c bc sc
  change NatAssign.Bank ids (sized v) d.val at bd
  change ∀i∈ids,(sized v i).bits.length≤secondWidth B at wd
  obtain ⟨c4,f,e4,h4,bf,sf,wf,f4⟩ := NatAssign.wordLength_executes ids 4409 4410 (secondWidth B)
    (by decide) (by decide) (by decide) (by decide) (sized v) (sized_fields v hC).2.2
    wd input tape d bd sd
  obtain ⟨c5,t,e5,h5,bt,st,wt,f5⟩ := assignment_executes finish valid_finish (by decide)
    (sizeMeasured v) (secondWidth B) wf input tape f bf sf
  refine ⟨c0+(c1+(c2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),
    Nat.add_le_add h0 (Nat.add_le_add h1 (Nat.add_le_add h2 (Nat.add_le_add h3 (Nat.add_le_add h4 h5)))),
    bt,st,wt,output_values v hC,?_⟩
  exact f0.trans ((f1.mono (by decide)).trans ((f2.mono (by decide)).trans
    (f3.trans ((f4.mono (by decide)).trans f5))))

#print axioms executes
end Maxwell.Continuum.Calibration.ParameterMachine
