import Maxwell.Continuum.ParameterOuterTauStage

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2048
attribute [local irreducible] BufferMachine.values

def spanSources : Finset ℕ := {2217,2218,2219,2221,2227,2223,2225}
def spanInputWidth (B : ℕ) : ℕ := 2^prepareSpans.length*(B+1)
def bufferSteps (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  Nat.find (bufferSearch_exists e D.wells D.sourceSize (stageLength k) (stageSpacing (D.input hD) e k)
    (stageSpan (D.input hD) e k) (D.input hD).K (D.input hD).epsilon (stageTau (D.input hD) e k)
    hD.sourceSize (D.input hD).epsilon_pos (stageTau_pos (D.input hD) e k))
def bufferStageCode : Code := .seq (NatAssign.code prepareSpans)
  (.seq (NatAssign.code loadBuffer) (.seq BufferMachine.restartCode (NatAssign.code saveBuffer)))
def bufferStageCost (D : Data) (hD : D.Positive) (e k W B : ℕ) : ℕ :=
  3000*8^prepareSpans.length*(W+2)^2+(3000*8^loadBuffer.length*(W+2)^2+
    (BufferMachine.resetCost W+BufferMachine.costBound (bufferSteps D hD e k) B+
      3000*8^saveBuffer.length*(W+2)^2))

structure BufferOutputs (D : Data) (hD : D.Positive) (e k : ℕ) (v : ℕ→ℕ) : Prop where
  buffer : v 2244=stageBuffer (D.input hD) e k
  box : v 2245=boxCount (stageSpan (D.input hD) e k) (stageLength k) (stageBuffer (D.input hD) e k)
  numerator : v 2246=BufferMachine.numerator (D.buffer hD e k) (stageBuffer (D.input hD) e k)
  denominator : v 2247=BufferMachine.denominator (D.buffer hD e k)

theorem bufferStage (D : Data) (hD : D.Positive) (e k W B S : ℕ) (hC : D.constant=2^e)
    (v : ℕ→ℕ) (hc : Core D k v) (ho : SpacingOutputs D hD e k v) (ht : TauOutputs D hD e k v)
    (hw : ∀i∈ids,(v i).bits.length ≤ W) (hsrc : ∀i∈spanSources,(v i).bits.length ≤ S)
    (hspan : spanInputWidth S ≤ W) (hdw : (D.buffer hD e k).Width B)
    (hbuf : BufferMachine.width (bufferSteps D hD e k) B ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    ∃cost t w,Executes input tape bufferStageCode cost s t ∧
      cost ≤ bufferStageCost D hD e k W B ∧ NatAssign.Bank ids w t.val ∧
      (∀i,i<5→RationalAccumulator.Blank t.val i) ∧ (∀i∈ids,(w i).bits.length ≤ W) ∧
      Core D k w ∧ SpacingOutputs D hD e k w ∧ TauOutputs D hD e k w ∧ BufferOutputs D hD e k w ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cp,p,ep,pp,bp,sp,fp⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) prepareSpans prepareSpans_valid v input tape s hb hs
  let vp := NatAssign.values prepareSpans v
  have wp : ∀i∈ids,(vp i).bits.length ≤ W := NatAssign.values_local_width ids spanSources prepareSpans
    prepareSpans_valid v W S hw hsrc (by simp [prepareSpans,NatAssign.Instruction.literalWidth])
    (by decide +kernel) hspan
  obtain ⟨cl,l,el,pl,bl,sl,fl⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) loadBuffer loadBuffer_valid vp input tape p bp sp
  let vl := NatAssign.values loadBuffer vp
  have wl : ∀i∈ids,(vl i).bits.length ≤ W := NatAssign.values_assignment_width ids loadBuffer
    loadBuffer_valid vp W wp (by simp [loadBuffer,NatAssign.Instruction.AssignmentBound])
  have keep : ∀i∈retained∪{2227,2228,2229,2243,2234,2237},vl i=v i := by
    intro i hi
    have bounds : (2200 ≤ i ∧ i ≤ 2226) ∨ i=2227 ∨ i=2228 ∨ i=2229 ∨ i=2243 ∨ i=2234 ∨ i=2237 := by
      simpa only [retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] using hi
    dsimp only [vl,vp]
    rw [NatAssign.values_preserves loadBuffer _ i (by simp [loadBuffer,NatAssign.Instruction.target];omega)]
    exact NatAssign.values_preserves prepareSpans v i (by simp [prepareSpans,NatAssign.Instruction.target];omega)
  have pc : Core D k vp := hc.congr (by
    intro i hi
    apply NatAssign.values_preserves
    simp only [retained,Finset.mem_Icc] at hi
    simp [prepareSpans,NatAssign.Instruction.target]
    omega)
  have pkeep (i : ℕ) (hi : i∈({2227,2229,2243,2234,2237}:Finset ℕ)) : vp i=v i := by
    apply NatAssign.values_preserves
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    simp [prepareSpans,NatAssign.Instruction.target]
    omega
  have hd : BufferMachine.dataOf vl=D.buffer hD e k := by
    rw [loadBuffer_fields]
    have span : (fun j:Fin 3=>vp (2240+j.val))=stageSpan (D.input hD) e k := by
      funext j
      dsimp only [vp]
      rw [prepareSpans_fields v hc.two hc.four j,hc.length,ho.spacing]
      change 2*stageLength k*stageSpacing (D.input hD) e k*v (2217+j.val)+4=
        2*stageLength k*stageSpacing (D.input hD) e k*D.span j+4
      have hh := congrArg (fun A:Data=>A.span j) hc.data
      exact congrArg (fun n=>2*stageLength k*stageSpacing (D.input hD) e k*n+4) hh
    simp only [pkeep 2229 (by decide +kernel),pkeep 2243 (by decide +kernel),
      pkeep 2234 (by decide +kernel),pkeep 2237 (by decide +kernel),
      ho.alphaNum,ho.alphaDen,ht.numerator,ht.denominator,pc.length,span]
    have c0 := congrArg Data.constant pc.data
    have c1 := congrArg Data.sourceSize pc.data
    have c2 := congrArg Data.wells pc.data
    have c3 := congrArg Data.conditionNum pc.data
    have c4 := congrArg Data.conditionDen pc.data
    have c5 := congrArg Data.epsilonNum pc.data
    have c6 := congrArg Data.epsilonDen pc.data
    dsimp only [dataOf] at c0 c1 c2 c3 c4 c5 c6
    rw [c0,c1,c2,c3,c4,c5,c6]
    rfl
  have h0 : vl 2100=D.constant := congrArg BufferMachine.Data.constant hd
  have hm : vl 2103=D.sourceSize := congrArg BufferMachine.Data.sourceSize hd
  have hkd : vl 2105=D.conditionDen := congrArg BufferMachine.Data.conditionDen hd
  have hen : vl 2106=D.epsilonNum := congrArg BufferMachine.Data.epsilonNum hd
  have hed : vl 2107=D.epsilonDen := congrArg BufferMachine.Data.epsilonDen hd
  have han : vl 2108=(stageLength k)^2 := congrArg BufferMachine.Data.alphaNum hd
  have had : vl 2109=2^1026*8^(stageSpacing (D.input hD) e k) := congrArg BufferMachine.Data.alphaDen hd
  have htn : vl 2110=1 := congrArg BufferMachine.Data.tauNum hd
  have htd : vl 2111=D.detuningDen hD e k := congrArg BufferMachine.Data.tauDen hd
  have hlen : vl 2101=stageLength k := congrArg BufferMachine.Data.length hd
  have ha : (vl 2108:ℚ)/vl 2109=alpha (vl 2101) (stageSpacing (D.input hD) e k) := by
    rw [han,had,hlen]
    exact D.buffer_alpha hD e k
  have eb := buffer vl e (stageSpacing (D.input hD) e k) W B (h0.trans hC)
    (hm.symm ▸ hD.sourceSize) (hkd.symm ▸ hD.conditionDen)
    (by rw [han];exact pow_pos (stageLength_pos k) 2) (by rw [had];positivity)
    (by rw [htn];decide) (by rw [htd];unfold Data.detuningDen;positivity)
    (hen.symm ▸ hD.epsilonNum) (hed.symm ▸ hD.epsilonDen) ha wl (by rw [hd];exact hdw)
    input tape l bl sl
  simp only [hd,D.buffer_tau hD e k] at eb
  change ∃cost t w,Executes input tape BufferMachine.restartCode cost l t ∧
    cost ≤ BufferMachine.resetCost W+BufferMachine.costBound (bufferSteps D hD e k) B ∧
    NatAssign.Bank ids w t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
    (∀i∈ids,(w i).bits.length ≤ max W (BufferMachine.width (bufferSteps D hD e k) B)) ∧
    (∀i∈BufferMachine.extra,w i=BufferMachine.values (D.buffer hD e k) (bufferSteps D hD e k) i) ∧
    (∀i∉BufferMachine.ids,w i=vl i) ∧ w 35=0 ∧ w 36=0 ∧
    RationalAccumulator.Word t.val 2115 (stageBuffer (D.input hD) e k) ∧
    BinaryPrecision.Frame workspace l.val t.val at eb
  obtain ⟨cb,b,u,eb,pb,bb,sb,wb,ub,uo,_,_,_,fb⟩ := eb
  have uw : ∀i∈ids,(u i).bits.length ≤ W := by simpa only [max_eq_left hbuf] using wb
  obtain ⟨cr,t,er,pr,br,sr,fr⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) saveBuffer saveBuffer_valid u input tape b bb sb
  let w := NatAssign.values saveBuffer u
  have ww := NatAssign.values_assignment_width ids saveBuffer saveBuffer_valid u W uw
    (by simp [saveBuffer,NatAssign.Instruction.AssignmentBound])
  have outside : ∀i∈retained∪{2227,2228,2229,2243,2234,2237},w i=v i := by
    intro i hi
    have hnot : i∉BufferMachine.ids := Finset.disjoint_left.mp
      (show Disjoint (retained∪{2227,2228,2229,2243,2234,2237}) BufferMachine.ids by decide +kernel) hi
    rw [show w i=u i from NatAssign.values_preserves saveBuffer u i (by
      simp only [retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
      simp [saveBuffer,NatAssign.Instruction.target];omega),uo i hnot,keep i hi]
  have wc : Core D k w := hc.congr (fun i hi=>outside i (Finset.mem_union_left _ hi))
  have wo : SpacingOutputs D hD e k w := ⟨
    (outside _ (by decide +kernel)).trans ho.spacing,(outside _ (by decide +kernel)).trans ho.zetaDen,
    (outside _ (by decide +kernel)).trans ho.alphaNum,(outside _ (by decide +kernel)).trans ho.alphaDen⟩
  have wt : TauOutputs D hD e k w := ⟨(outside _ (by decide +kernel)).trans ht.numerator,
    (outside _ (by decide +kernel)).trans ht.denominator⟩
  obtain ⟨h44,h45,h46,h47⟩ := saveBuffer_fields u
  have u15 := (ub 2115 (by decide +kernel)).trans
    (BufferMachine.input_fields (D.buffer hD e k) (bufferSteps D hD e k) 2115 (by decide))
  obtain ⟨u30,u55,u56⟩ := BufferMachine.fields (D.buffer hD e k) (bufferSteps D hD e k)
  have db : 2^(bufferSteps D hD e k)=stageBuffer (D.input hD) e k := rfl
  have bo : BufferOutputs D hD e k w := ⟨
    h44.trans (by simpa [BufferMachine.inputs,db] using u15),
    h45.trans ((ub 2130 (by decide +kernel)).trans (by simpa only [db,Data.buffer] using u30)),
    h46.trans ((ub 2155 (by decide +kernel)).trans (by simpa only [db] using u55)),
    h47.trans ((ub 2156 (by decide +kernel)).trans u56)⟩
  have ppb := NatAssign.price_bound ids prepareSpans prepareSpans_valid v W hw
    (by simp [prepareSpans,NatAssign.Instruction.literalWidth])
  have plb := NatAssign.price_bound ids loadBuffer loadBuffer_valid vp W wp
    (by simp [loadBuffer,NatAssign.Instruction.literalWidth])
  have prb := NatAssign.price_bound ids saveBuffer saveBuffer_valid u W uw
    (by simp [saveBuffer,NatAssign.Instruction.literalWidth])
  exact ⟨cp+(cl+(cb+cr)),t,w,ep.seq (el.seq (eb.seq er)),
    Nat.add_le_add (pp.trans ppb) (Nat.add_le_add (pl.trans plb) (Nat.add_le_add pb (pr.trans prb))),
    br,sr,ww,wc,wo,wt,bo,(fp.mono (by decide +kernel)).trans
      ((fl.mono (by decide +kernel)).trans (fb.trans (fr.mono (by decide +kernel))))⟩

#print axioms bufferStage
end Maxwell.Continuum.Parameters.OuterMachine
