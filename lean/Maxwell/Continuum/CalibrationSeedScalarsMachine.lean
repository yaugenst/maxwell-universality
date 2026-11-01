import Maxwell.Continuum.CalibrationSeedComponentsMachine

/-! One fixed program computes all three corner-seed scalars from its
runtime precision word. Both square roots and every rational product are
executed; no seed coefficient is supplied by the caller. -/
namespace Maxwell.Continuum.Calibration.SeedMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

def scalarsCode : Code := .seq radicalCode (.seq denominatorCode (NatAssign.code componentsPlan))
def scalarsCost (N B : ℕ) : ℕ := radicalCost N B+
  (denominatorCost N (radicalWidth N B)+componentsCost (denominatorWidth N (radicalWidth N B)))
def scalarsWidth (N B : ℕ) : ℕ := componentsWidth (denominatorWidth N (radicalWidth N B))

theorem scalars_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t w,Executes input tape scalarsCode cost s t ∧ cost≤scalarsCost (v 700) B ∧
      NatAssign.Bank componentIds w t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈componentIds,(w i).bits.length≤scalarsWidth (v 700) B) ∧
      (∀j,(storedComponent w j).Valid ∧ (storedComponent w j).value=seedComponent (v 700) j) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,sa,wa,f0⟩ := radical_executes v B width input tape s bank scratch
  let rv := radicalValues v
  obtain ⟨rnum,rden,rprecision,_⟩ := radicalValues_fields v
  have rpositive : 0<rv 548 := by rw [show rv 548=_ from rden];positivity
  have radical : (rv 32:ℚ)/rv 548=seedRadical (v 700) := by
    rw [show rv 32=_ from rnum,show rv 548=_ from rden]
    exact radicalValue (v 700)
  obtain ⟨c1,b,num,den,e1,h1,bb,sb,wb,hnum,hden,value,f1⟩ := denominator_executes
    (v 700) rv (radicalWidth (v 700) B) wa rprecision rpositive radical input tape a ba sa
  let dv := denominatorValues rv num den
  obtain ⟨c2,t,e2,h2,bt,st,wt,f2⟩ := components_executes dv
    (denominatorWidth (v 700) (radicalWidth (v 700) B)) wb input tape b bb sb
  have fields := denominatorValues_fields rv num den
  have exactParts (j : Fin 3) :
      storedComponent (componentsValues dv) j=componentParts (rv 32) (rv 548) num den j := by
    rw [components_values]
    simp only [dv,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1]
  refine ⟨c0+(c1+c2),t,componentsValues dv,e0.seq (e1.seq e2),
    Nat.add_le_add h0 (Nat.add_le_add h1 h2),bt,st,wt,?_,f0.trans (f1.trans f2)⟩
  intro j
  rw [exactParts j]
  exact ⟨componentParts_valid _ _ _ _ rpositive hnum j,
    componentParts_value (v 700) _ _ _ _ rpositive hden radical value j⟩

#print axioms scalars_executes
end Maxwell.Continuum.Calibration.SeedMachine
