import Maxwell.Continuum.FourierTensorRowMetadata

/-! Every workspace and allocation width in component execution is now
a literal function of its represented input array and integer parameters. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5500000
set_option maxRecDepth 32768

def tableWidth {n : ℕ} (a : Table n) : ℕ := descriptorWidth a+a.clock.length

theorem tableWidth_spec {n : ℕ} (a : Table n) : a.MetadataWidth (tableWidth a) := by
  constructor <;> unfold tableWidth descriptorWidth <;> omega

def computedWorkWidth (M A L R P Q N E : ℕ) (a : Table (2*aliasArraySize R)) : ℕ :=
  ModePrelude.arithmeticWidth M A L R P Q N E+rowMetadataWidth M L R P a

def computedInputWidth (M A L R P Q N E : ℕ) (a : Table (2*aliasArraySize R)) : ℕ :=
  computedWorkWidth M A L R P Q N E a+tableWidth a

def computedComponentCost {p : ℕ} (M A L R P Q N E : ℕ)
    (a : Table (2*aliasArraySize R)) (old : Table p) : ℕ :=
  completeComponentCost M A L R P Q N (ModePrelude.inputWidth M A L)
    (computedInputWidth M A L R P Q N E a) (computedWorkWidth M A L R P Q N E a)
    (allocationInputWidth M L R P a) (tableWidth old)

theorem computedComponent_executes {p : ℕ} (M A L R P Q N E : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (old : Table p) (j : Fin 3)
    (hav : ∀i,(a.get i).Valid) (hmode : ‖(GlobalPower.tableData R a).value‖≤2)
    (hfreq : L*R≤2*M*Q) (hmass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hr : Ready RowArithmetic.bank ModePrelude.zeroValues s) (hz : PhysicalFactorMachine.Clean s.val)
    (wa : Word s.val 351 A)
    (ha : a.Ready s) (ho : old.OutputReady s) (hfloor : DyadicFloor.Clean s.val)
    (hphase : Phase.Runtime.Clean s.val) (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (hfresh : ∀i∈TensorStart.freshPorts,Blank s.val i) :
    ∃cost t,Executes input tape (completeComponentCode j) cost s t ∧
      cost≤computedComponentCost M A L R P Q N E a old ∧
      t.val.output=(componentPayload M A L R P Q N a j).reverse++s.val.output := by
  rcases ModePrelude.inputWidth_spec M A L with ⟨hi,hm,hA,hl⟩
  rcases ModePrelude.arithmeticWidth_spec M A L R P Q N E with
    ⟨hfactor,h6,hR,hsize,hcount,hcoeff,hQ,hN,hd,hprec,hgrid⟩
  have lift {x : ℕ} (hx : x≤ModePrelude.arithmeticWidth M A L R P Q N E) :
      x≤computedWorkWidth M A L R P Q N E a := hx.trans (Nat.le_add_right _ _)
  have inputLarge : computedWorkWidth M A L R P Q N E a≤computedInputWidth M A L R P Q N E a :=
    Nat.le_add_right _ _
  have rowLarge : rowMetadataWidth M L R P a≤computedWorkWidth M A L R P Q N E a := Nat.le_add_left _ _
  exact completeComponent_executes M A L R P Q N E (ModePrelude.inputWidth M A L)
    (computedInputWidth M A L R P Q N E a) (computedWorkWidth M A L R P Q N E a)
    (allocationInputWidth M L R P a) (tableWidth old) hi hm hA hl (lift hfactor)
    inputLarge (lift h6) (allocationInputWidth_spec M L R P a).1 a old j
    ((tableWidth_spec a).mono (Nat.le_add_left _ _)) (tableWidth_spec old) hav
    (lift hR) ((lift hsize).trans inputLarge) (lift hcount) hmode hfreq hmass
    (lift hcoeff) (lift hQ) (lift hN) (lift hd) (lift hprec) (lift hgrid)
    (allocationInputWidth_spec M L R P a).2 input tape s
    ((buffer_metadata_computed M L R P a s.val.memory).mono rowLarge)
    hb hr hz wa ha ho hfloor hphase hsetup hfresh

#print axioms computedComponent_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
