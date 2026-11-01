import Maxwell.Continuum.ParameterOuterState

/-! Actual operand loading, complete spacing search, and retained output
transfer for one outer candidate. The source parameter bank survives. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
attribute [local irreducible] SpacingMachine.values

def spacingSteps (D : Data) (hD : D.Positive) (e k : ℕ) : ℕ :=
  Nat.find (spacingSearch_exists e (stageLength k) (D.input hD).K (D.input hD).epsilon
    (D.input hD).K_pos (D.input hD).epsilon_pos)

def spacingCode : Code := .seq (NatAssign.code loadSpacing)
  (.seq SpacingMachine.restartCode (NatAssign.code saveSpacing))
def spacingCost (D : Data) (hD : D.Positive) (e k W B : ℕ) : ℕ :=
  3000*8^loadSpacing.length*(W+2)^2+
    (SpacingMachine.resetCost W+SpacingMachine.costBound (spacingSteps D hD e k) B+
      3000*8^saveSpacing.length*(W+2)^2)

structure SpacingOutputs (D : Data) (hD : D.Positive) (e k : ℕ) (v : ℕ→ℕ) : Prop where
  spacing : v 2227=stageSpacing (D.input hD) e k
  zetaDen : v 2228=3^(stageSpacing (D.input hD) e k)
  alphaNum : v 2229=(stageLength k)^2
  alphaDen : v 2243=2^1026*8^(stageSpacing (D.input hD) e k)

theorem spacingStage (D : Data) (hD : D.Positive) (e k W B : ℕ) (hC : D.constant=2^e)
    (hdw : (D.spacing k).Width B) (hsw : SpacingMachine.width (spacingSteps D hD e k) B ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready D k W s) :
    ∃cost t v,Executes input tape spacingCode cost s t ∧ cost ≤ spacingCost D hD e k W B ∧
      NatAssign.Bank ids v t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
      (∀i∈ids,(v i).bits.length ≤ W) ∧ Core D k v ∧ SpacingOutputs D hD e k v ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨v,hb,hsc,hw,hcore⟩ := hs
  obtain ⟨cl,l,el,pl,bl,sl,fl⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) loadSpacing loadSpacing_valid v input tape s hb hsc
  let vl := NatAssign.values loadSpacing v
  have wl : ∀i∈ids,(vl i).bits.length ≤ W := NatAssign.values_assignment_width ids loadSpacing
    loadSpacing_valid v W hw (by simp [loadSpacing,NatAssign.Instruction.AssignmentBound])
  have lc : Core D k vl := hcore.congr (by
    intro i hi
    apply NatAssign.values_preserves
    simp only [retained,Finset.mem_Icc] at hi
    simp [loadSpacing,NatAssign.Instruction.target]
    omega)
  have hd := hcore.spacing_data
  change SpacingMachine.dataOf vl=D.spacing k at hd
  have h0 : vl 2000=D.constant := congrArg SpacingMachine.Data.constant hd
  have h2 : vl 2002=D.conditionNum := congrArg SpacingMachine.Data.conditionNum hd
  have h3 : vl 2003=D.conditionDen := congrArg SpacingMachine.Data.conditionDen hd
  have h4 : vl 2004=D.epsilonNum := congrArg SpacingMachine.Data.epsilonNum hd
  have h5 : vl 2005=D.epsilonDen := congrArg SpacingMachine.Data.epsilonDen hd
  have es := spacing vl e W B (h0.trans hC) (h2.symm ▸ hD.conditionNum) (h3.symm ▸ hD.conditionDen)
    (h4.symm ▸ hD.epsilonNum) (h5.symm ▸ hD.epsilonDen) wl (by rw [hd];exact hdw) input tape l bl sl
  simp only [hd] at es
  change ∃cost t w,Executes input tape SpacingMachine.restartCode cost l t ∧
    cost ≤ SpacingMachine.resetCost W+SpacingMachine.costBound (spacingSteps D hD e k) B ∧
    NatAssign.Bank ids w t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
    (∀i∈ids,(w i).bits.length ≤ max W (SpacingMachine.width (spacingSteps D hD e k) B)) ∧
    (∀i∈SpacingMachine.extra,w i=SpacingMachine.values (D.spacing k) (spacingSteps D hD e k) i) ∧
    (∀i∉SpacingMachine.ids,w i=vl i) ∧ w 35=0 ∧ w 36=0 ∧
    RationalAccumulator.Word t.val 2006 (stageSpacing (D.input hD) e k) ∧
    BinaryPrecision.Frame workspace l.val t.val at es
  obtain ⟨cs,a,u,es,ps,ba,sa,wa,ua,uo,_,_,_,fa⟩ := es
  have uw : ∀i∈ids,(u i).bits.length ≤ W := by simpa only [max_eq_left hsw] using wa
  have uc : Core D k u := lc.congr (fun i hi=>uo i (Finset.disjoint_left.mp retained_disjoint_spacing hi))
  obtain ⟨cr,t,er,pr,br,sr,fr⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) saveSpacing saveSpacing_valid u input tape a ba sa
  let w := NatAssign.values saveSpacing u
  have ww : ∀i∈ids,(w i).bits.length ≤ W := NatAssign.values_assignment_width ids saveSpacing
    saveSpacing_valid u W uw (by simp [saveSpacing,NatAssign.Instruction.AssignmentBound])
  have wc : Core D k w := uc.congr (by
    intro i hi
    apply NatAssign.values_preserves
    simp only [retained,Finset.mem_Icc] at hi
    simp [saveSpacing,NatAssign.Instruction.target]
    omega)
  obtain ⟨h27,h28,h29,h43⟩ := saveSpacing_fields u
  have u06 := (ua 2006 (by decide +kernel)).trans
    (SpacingMachine.input_fields (D.spacing k) (spacingSteps D hD e k) 2006 (by decide))
  have u07 := (ua 2007 (by decide +kernel)).trans
    (SpacingMachine.input_fields (D.spacing k) (spacingSteps D hD e k) 2007 (by decide))
  obtain ⟨_,_,h22,_,_,h25,_⟩ := SpacingMachine.fields (D.spacing k) (spacingSteps D hD e k)
  have u22 := (ua 2022 (by decide +kernel)).trans h22
  have u25 := (ua 2025 (by decide +kernel)).trans h25
  have ds : 2^(spacingSteps D hD e k)=stageSpacing (D.input hD) e k := rfl
  have outs : SpacingOutputs D hD e k w := by
    refine ⟨?_,?_,?_,?_⟩
    · exact h27.trans (by simpa [SpacingMachine.inputs,ds] using u06)
    · exact h28.trans (by simpa [SpacingMachine.inputs,ds] using u07)
    · exact h29.trans u22
    · exact h43.trans (by simpa only [ds] using u25)
  have plb := NatAssign.price_bound ids loadSpacing loadSpacing_valid v W hw
    (by simp [loadSpacing,NatAssign.Instruction.literalWidth])
  have prb := NatAssign.price_bound ids saveSpacing saveSpacing_valid u W uw
    (by simp [saveSpacing,NatAssign.Instruction.literalWidth])
  exact ⟨cl+(cs+cr),t,w,el.seq (es.seq er),Nat.add_le_add (pl.trans plb) (Nat.add_le_add ps (pr.trans prb)),
    br,sr,ww,wc,outs,(fl.mono (by decide +kernel)).trans (fa.trans (fr.mono (by decide +kernel)))⟩

#print axioms spacingStage
end Maxwell.Continuum.Parameters.OuterMachine
