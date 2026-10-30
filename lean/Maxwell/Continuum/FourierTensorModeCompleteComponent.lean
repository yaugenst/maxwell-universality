import Maxwell.Continuum.FourierTensorModePreludeFrame
import Maxwell.Continuum.FourierTensorModePayload

/-! Complete fixed component generation from the normalized mode array
and stored integer parameters, with no prepared physical constants. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5500000
set_option maxRecDepth 32768

def completeComponentCode (j : Fin 3) : Code := .seq ModePrelude.code (componentCode j)
def completeComponentCost (M A L R P Q N W Win Wout Wsetup H : ℕ) : ℕ :=
  ModePrelude.costBound A W+componentCost M L R P Q N Win Wout Wsetup H

theorem completeComponent_executes {p : ℕ} (M A L R P Q N E W Win Wout Wsetup H : ℕ) [NeZero M]
    (hW : 1≤W) (hm : M.bits.length≤W) (hA : A.bits.length≤W) (hl : L.bits.length≤W)
    (hsmall : ModePrelude.factorWidth A W≤Wout)
    (hWin : Wout≤Win) (hWout : 6≤Wout) (hsetupWidth : 5≤Wsetup)
    (a : Table (2*aliasArraySize R)) (old : Table p) (j : Fin 3)
    (hma : a.MetadataWidth Win) (hmo : old.MetadataWidth H)
    (hav : ∀i,(a.get i).Valid) (hR : R.bits.length≤Wout)
    (hsize : (aliasArraySize R).bits.length≤Win) (hcount : (RowArithmetic.rowCount R).bits.length≤Wout)
    (hmode : ‖(GlobalPower.tableData R a).value‖≤2)
    (hfreq : L*R≤2*M*Q) (hmass : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (hcoeff : P+3*waveWorkBits (8*Q) N+E+16≤Wout)
    (hQ : Q.bits.length≤Wout) (hN : N.bits.length≤Wout)
    (hdegree : (waveDegree (8*Q) N).bits.length≤Wout)
    (hprecision : waveWorkBits (8*Q) N+7≤Wout) (hgrid : (waveGrid (8*Q) N).bits.length≤Wout)
    (hiw : InputWidth M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator) Wsetup)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hmb : (buffer M L R P a s.val.memory).MetadataWidth Wout)
    (hb : NatAssign.Bank ids (initial M L R P (addressValue a.width) (addressValue a.basePositive)
      (addressValue a.baseNegative) (addressValue a.baseDenominator)) s.val)
    (hr : Ready RowArithmetic.bank ModePrelude.zeroValues s) (hz : PhysicalFactorMachine.Clean s.val)
    (wa : Word s.val 351 A)
    (ha : a.Ready s) (ho : old.OutputReady s) (hfloor : DyadicFloor.Clean s.val)
    (hphase : Phase.Runtime.Clean s.val) (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (hfresh : ∀i∈TensorStart.freshPorts,Blank s.val i) :
    ∃cost t,Executes input tape (completeComponentCode j) cost s t ∧
      cost≤completeComponentCost M A L R P Q N W Win Wout Wsetup H ∧
      t.val.output=(componentPayload M A L R P Q N a j).reverse++s.val.output := by
  have wm : Word s.val 350 M := by simpa [initial] using hb 350 (by decide)
  have wl : Word s.val 352 L := by simpa [initial] using hb 352 (by decide)
  have z353 : Blank s.val 353 := by
    simpa [initial,RationalAccumulator.zero_word_iff_blank] using hb 353 (by decide)
  obtain ⟨c0,u,e0,hc0,r0,m0,_,l0,z0,f0⟩ := ModePrelude.executes M A L W (NeZero.pos M) hW hm hA hl
    input tape s hr hz wm wa wl z353
  have source0 := ModePrelude.table_frame ha f0 r0.2
  have target0 := ModePrelude.output_frame ho f0 source0.scratch source0.seven
  have ready0 : Ready RowArithmetic.bank (ModePrepare.canonical (ModePrelude.values M A L)) u := by
    rwa [ModePrelude.values_canonical]
  have meta0 : (buffer M L R P a u.val.memory).MetadataWidth Wout := by rwa [f0.memory]
  obtain ⟨c1,t,e1,hc1,out⟩ := component_executes M A L R P Q N E Win Wout Wsetup H
    hWin hWout hsetupWidth a old j (ModePrelude.values M A L) hma hmo
    (ModePrelude.values_width M A L W Wout hm hA hl hsmall) (ModePrelude.values_good M A L (NeZero.pos M))
    hav hR hsize hcount (ModePrelude.values_factor M A L (NeZero.pos M)) (ModePrelude.values_scale M A L)
    hmode hfreq hmass hcoeff hQ hN hdegree hprecision hgrid hiw input tape u meta0
    (ModePrelude.allocation_frame hb f0 m0 l0 z0) ready0 source0 target0 (ModePrelude.floor_frame hfloor f0)
    (ModePrelude.phase_frame hphase f0 r0) (ModePrelude.setup_frame hsetup f0) (ModePrelude.fresh_frame hfresh f0)
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,by simpa only [f0.output] using out⟩

#print axioms completeComponent_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
