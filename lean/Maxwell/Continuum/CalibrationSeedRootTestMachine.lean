import Maxwell.Continuum.CalibrationSeedRootIndexMachine

/-! Charged support testing for one sparse seed term.  Both bounds in
each of the three coordinates are actual comparisons of stored words. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def testCode (s : Corner.Parity) (part : Fin 2) : Code :=
  .seq (NatAssign.code (prepare s part)) (SelectedParameters.AllComparisons.code tests)
def testWidth (B : ℕ) : ℕ := 2^28*(B+3)
def testCost (B : ℕ) : ℕ := 3000*8^28*(B+4)^2+
  6*(SelectedParameters.AllComparisons.unitCost (testWidth B)+2)+2

theorem prepare_length (s : Corner.Parity) (part : Fin 2) : (prepare s part).length=28 := rfl
theorem prepare_literals (s : Corner.Parity) (part : Fin 2) (B : ℕ) :
    ∀a∈prepare s part,a.literalWidth≤B+2 := by
  fin_cases part <;> simp [prepare,coordinatePlan,NatAssign.Instruction.literalWidth,
    show (2:ℕ).bits.length=2 by decide,show (3:ℕ).bits.length=2 by decide]

theorem test_executes (parity : Corner.Parity) (part : Fin 2) (v : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B) (half : v 752=v 750/2)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t w,Executes input tape (testCode parity part) cost s t ∧ cost≤testCost B ∧
      NatAssign.Bank ids w t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(w i).bits.length≤testWidth B) ∧
      (∀i∈extra,w i=prepared parity part v i) ∧
      t.val.registers 35=decide (¬inside (v 750) (v 751) parity (coordinates v)) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,sa,f0⟩ := NatAssign.executes ids ids_lower (prepare parity part)
    (prepare_valid parity part) v input tape s bank scratch
  change NatAssign.Bank ids (prepared parity part v) a.val at ba
  have wa : ∀i∈ids,(prepared parity part v i).bits.length≤testWidth B := by
    intro i hi
    have hh := NatAssign.values_width ids (prepare parity part) (prepare_valid parity part) v
      (B+2) (fun i hi=>(width i hi).trans (by omega)) (prepare_literals parity part B) i hi
    rw [prepare_length] at hh
    exact (Nat.le_add_right _ 1).trans hh
  have fields := prepared_fields parity part v half
  have enabled : ∀q∈tests,SelectedParameters.AllComparisons.Enabled (prepared parity part v) q := by
    simp [tests,SelectedParameters.AllComparisons.Enabled,fields.2.2.2.2.2.1]
  obtain ⟨c1,t,w,e1,h1,flag,bt,st,keep,wt,_,_,f1⟩ := SelectedParameters.AllComparisons.executes
    extra extra_lower tests tests_valid (prepared parity part v) (testWidth B) wa enabled
    fields.2.2.2.2.2.2.1 fields.2.2.2.2.2.2.2 input tape a ba sa
  have price := NatAssign.price_bound ids (prepare parity part) (prepare_valid parity part) v
    (B+2) (fun i hi=>(width i hi).trans (by omega)) (prepare_literals parity part B)
  rw [prepare_length,show B+2+2=B+4 by omega] at price
  refine ⟨c0+c1,t,w,e0.seq e1,?_,bt,st,wt,keep,?_,?_⟩
  · change c1≤6*(SelectedParameters.AllComparisons.unitCost (testWidth B)+2)+2 at h1
    unfold testCost
    omega
  · exact flag.trans (prepared_failed parity part v half)
  · exact (f0.mono (NatAssign.changes_subset ids (prepare parity part) (prepare_valid parity part))).trans
      (f1.mono (by decide))

#print axioms test_executes
end Maxwell.Continuum.Calibration.SeedRoot
