import Maxwell.Continuum.FourierTensorModeComponentCost

/-! The fixed component compiler starts with the represented calibrated
mode, generates its rounded physical Fourier rows, allocates its wave
cache, and emits the declared tensor coefficient payload. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5500000
set_option maxRecDepth 32768

theorem component_executes {p : ℕ} (M A L R P Q N E Win Wout Wsetup H : ℕ) [NeZero M]
    (hWin : Wout≤Win) (hWout : 6≤Wout) (hsetupWidth : 5≤Wsetup)
    (a : Table (2*aliasArraySize R)) (old : Table p) (j : Fin 3) (v : ℕ→Parts)
    (hma : a.MetadataWidth Win) (hmo : old.MetadataWidth H)
    (hw : WidthBank RowArithmetic.bank Wout v) (hg : Good RowArithmetic.bank v)
    (hav : ∀i,(a.get i).Valid) (hR : R.bits.length≤Wout)
    (hsize : (aliasArraySize R).bits.length≤Win) (hcount : (RowArithmetic.rowCount R).bits.length≤Wout)
    (hnorm : (v 0).value=Supercell.physicalFactorApprox M A)
    (hscale : v 1=FrequencyScaleMachine.result M L) (hmode : ‖(GlobalPower.tableData R a).value‖≤2)
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
    (hr : Ready RowArithmetic.bank (ModePrepare.canonical v) s)
    (ha : a.Ready s) (ho : old.OutputReady s) (hfloor : DyadicFloor.Clean s.val)
    (hphase : Phase.Runtime.Clean s.val) (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (hfresh : ∀i∈TensorStart.freshPorts,Blank s.val i) :
    ∃cost t,Executes input tape (componentCode j) cost s t ∧
      cost≤componentCost M L R P Q N Win Wout Wsetup H ∧
      t.val.output=(componentPayload M A L R P Q N a j).reverse++s.val.output := by
  have z144 := hfresh 144 (by simp [TensorStart.freshPorts])
  have z146 := hfresh 146 (by simp [TensorStart.freshPorts])
  have z216 := hfresh 216 (by simp [TensorStart.freshPorts])
  obtain ⟨c0,u,ys,origin,e0,hc0,st,output0,rows,counter,length⟩ := generated_executes M A L R P Win Wsetup H
    (by omega) hsetupWidth a old j v hma hmo (fun i hi => (hw i hi).mono hWin) hg hav
    (hR.trans hWin) hsize (hcount.trans hWin) hnorm hscale hmode hiw input tape s (hmb.mono hWin)
    hb hr ha ho z216 hfloor z144 z146
  let rowsTable := generatedTable M L R P a j v s.val.memory
  have rowMeta : rowsTable.MetadataWidth Wout := ⟨hmb.width,hmb.basePositive,hmb.baseNegative,hmb.baseDenominator,hmb.clock⟩
  obtain ⟨storage,storageWidth⟩ := generated_stored M L R P Wsetup H hsetupWidth a old j hiw hmo
    input tape s u hb hr.2 ha ho z216 e0
  have precision0 := generated_precision M L R P Wsetup hsetupWidth a j hiw input tape s u hb hr.2 z144 z146 e0
  have count0 := generated_power_count M L R P Wsetup hsetupWidth a j hiw input tape s u hb hr.2 z144 z146 e0
  have temp0 : Blank u.val 216 := by
    cases e0 with
    | seq allocated rest =>
      obtain ⟨c,g,run,_,_,_,_,_,_,_,temp,frame⟩ := allocated_executes M L R P Wsetup H hsetupWidth a old
        hiw hmo RowArithmetic.bank (ModePrepare.canonical v) input tape s hb hr ha ho z216
      have same := allocated.deterministic run
      rw [same.2] at rest
      cases rest with
      | seq power generated =>
        exact RationalAccumulator.blank_of_eq
          ((ModePrepare.table_executes_retained generated 216 (by simp [ModePrepare.retainedPorts])).trans
            (power.protectsTape 216 (by decide))) temp
  obtain ⟨c1,w,e1,hc1,r1,source1,target1,floor1,clear1,temp1,frame1⟩ :=
    RowHandoff.executes a rowsTable RowArithmetic.bank (ModePrepare.canonical v) P Win
      (2^8*(2^32*(Wsetup+1)+1)) hma (rowMeta.mono hWin) (allocationValues M L R P a) storageWidth
      input tape u st.ready st.source output0 st.floor st.power precision0 ⟨ys,length,origin,counter⟩ storage temp0
  let d := TensorSetup.allocatedInput R P Q N Wout rowsTable w.val.memory
    (frequency M L R) (amplitude M A P R a j) E rowMeta rows (frequency_bound M L R Q hfreq)
    (amplitude_mass M A P R E a hmode hmass j) hcoeff hQ hN hcount hdegree hWout hprecision hgrid
  have radius : Word w.val 311 R := by
    have hn := st.naturals 311 (by decide)
    rw [show ModeIndex.initial R (aliasArraySize R) 0 311=R by simp [ModeIndex.initial]] at hn
    exact RationalAccumulator.word_of_eq (frame1.tapes 311 (by decide)) hn
  obtain ⟨c2,z,e2,hc2,⟨state⟩,buffers,frame2⟩ := TensorStart.executes d a Win hma v hw hR
    (TensorSetup.generated_headers M L R P a j v s.val.memory) input tape w rfl r1 source1 target1
    (handoff_phase (generated_phase e0 hphase st.ready) frame1) floor1
    (handoff_setup e0 hsetup frame1 clear1) radius (handoff_fresh e0 hfresh count0 frame1 clear1 temp1)
  obtain ⟨c3,t,_,e3,hc3,_,out⟩ := tensorComponent_executes d input tape z state buffers
  have finalCost : c3≤tensorTimeCoefficient*(RowArithmetic.rowCount R+1)^3*(Q+N+Wout+64)^243 :=
    hc3.trans (tensorTraversalCost_polynomial Q N (RowArithmetic.rowCount R) Wout)
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,?_⟩
  · have prep := (Nat.add_le_add hc0 (Nat.add_le_add hc1 hc2)).trans
      (preparation_cost M L R P Q N Win Wout Wsetup H)
    unfold componentCost
    omega
  · change t.val.output=(d.componentPayload).reverse++s.val.output
    rw [out,frame2.output,frame1.output,st.output]

theorem component_compiled_run {p : ℕ} (M A L R P Q N E Win Wout Wsetup H : ℕ) [NeZero M]
    (hWin : Wout≤Win) (hWout : 6≤Wout) (hsetupWidth : 5≤Wsetup)
    (a : Table (2*aliasArraySize R)) (old : Table p) (j : Fin 3) (v : ℕ→Parts)
    (hma : a.MetadataWidth Win) (hmo : old.MetadataWidth H)
    (hw : WidthBank RowArithmetic.bank Wout v) (hg : Good RowArithmetic.bank v)
    (hav : ∀i,(a.get i).Valid) (hR : R.bits.length≤Wout)
    (hsize : (aliasArraySize R).bits.length≤Win) (hcount : (RowArithmetic.rowCount R).bits.length≤Wout)
    (hnorm : (v 0).value=Supercell.physicalFactorApprox M A)
    (hscale : v 1=FrequencyScaleMachine.result M L) (hmode : ‖(GlobalPower.tableData R a).value‖≤2)
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
    (hr : Ready RowArithmetic.bank (ModePrepare.canonical v) s)
    (ha : a.Ready s) (ho : old.OutputReady s) (hfloor : DyadicFloor.Clean s.val)
    (hphase : Phase.Runtime.Clean s.val) (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (hfresh : ∀i∈TensorStart.freshPorts,Blank s.val i) :
    ∃t : Store,(runPriced ((componentCode j).compile.next input tape)
      (componentCost M L R P Q N Win Wout Wsetup H+1) s.val).finished=some (t.place (componentCode j).size) ∧
      t.val.output=(componentPayload M A L R P Q N a j).reverse++s.val.output := by
  obtain ⟨cost,t,e,hc,out⟩ := component_executes M A L R P Q N E Win Wout Wsetup H hWin hWout hsetupWidth
    a old j v hma hmo hw hg hav hR hsize hcount hnorm hscale hmode hfreq hmass hcoeff hQ hN hdegree
    hprecision hgrid hiw input tape s hmb hb hr ha ho hfloor hphase hsetup hfresh
  exact ⟨t,(e.compiled_run _ (by omega)).1,out⟩

#print axioms component_executes
#print axioms component_compiled_run
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
