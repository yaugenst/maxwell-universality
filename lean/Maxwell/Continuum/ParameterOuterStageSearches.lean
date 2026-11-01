import Maxwell.Continuum.ParameterOuterStageData

/-! Lift the checked inner searches into the complete outer word bank.
Each search retains every other stage's words through its proved frame. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Blank Word)
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
attribute [local irreducible] SpacingMachine.values BufferMachine.values

theorem spacing (v : ℕ→ℕ) (e W B : ℕ) (hC : v 2000=2^e)
    (hKn : 0<v 2002) (hKd : 0<v 2003) (hEn : 0<v 2004) (hEd : 0<v 2005)
    (hw : ∀i∈ids,(v i).bits.length ≤ W) (hD : (SpacingMachine.dataOf v).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→Blank s.val i) :
    let D := SpacingMachine.dataOf v
    let K := (D.conditionNum:ℚ)/D.conditionDen
    let ε := (D.epsilonNum:ℚ)/D.epsilonDen
    let hK : 0<K := div_pos (by exact_mod_cast hKn) (by exact_mod_cast hKd)
    let hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
    let N := Nat.find (spacingSearch_exists e D.length K ε hK hε)
    ∃cost t w,Executes input tape SpacingMachine.restartCode cost s t ∧
      cost ≤ SpacingMachine.resetCost W+SpacingMachine.costBound N B ∧
      NatAssign.Bank ids w t.val ∧ (∀i,i<5→Blank t.val i) ∧
      (∀i∈ids,(w i).bits.length ≤ max W (SpacingMachine.width N B)) ∧
      (∀i∈SpacingMachine.extra,w i=SpacingMachine.values D N i) ∧
      (∀i∉SpacingMachine.ids,w i=v i) ∧ w 35=0 ∧ w 36=0 ∧
      Word t.val 2006 (selectedSpacing e D.length K ε hK hε) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  have sub : SpacingMachine.ids⊆ids := by decide +kernel
  have ee := SpacingMachine.restart v e W B hC hKn hKd hEn hEd (fun i hi=>hw i (sub hi)) hD
    input tape s (fun i hi=>hb i (sub hi)) (fun i hi=>hs i (by omega))
  obtain ⟨cost,t,he,hc,ht,hword,hf⟩ := ee
  obtain ⟨u,bu,su,hu,wu,u35,u36⟩ := ht
  let w := NatAssign.overlay SpacingMachine.ids u v
  have frame : BinaryPrecision.Frame (SpacingMachine.ids∪{0,1,2,3,4}) s.val t.val :=
    hf.mono (by decide +kernel)
  have bt : NatAssign.Bank ids w t.val := hb.overlay bu (by decide +kernel) frame
  have st : ∀i,i<5→Blank t.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact su i h4
    · have hi4 : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (hf.tapes 4 (by decide +kernel)) (hs 4 (by decide))
  refine ⟨cost,t,w,he,hc,bt,st,NatAssign.overlay_width hw wu,?_,?_,?_,?_,hword,hf.mono (by decide +kernel)⟩
  · intro i hi
    have hh : i∈SpacingMachine.ids := Finset.mem_union_left _ hi
    simpa only [w,NatAssign.overlay,ite_eq_left hh] using hu i hi
  · intro i hi;exact NatAssign.overlay_outside v u i hi
  · simpa only [w,NatAssign.overlay,show 35∈SpacingMachine.ids by decide,ite_true] using u35
  · simpa only [w,NatAssign.overlay,show 36∈SpacingMachine.ids by decide,ite_true] using u36

theorem buffer (v : ℕ→ℕ) (e d W B : ℕ) (hC : v 2100=2^e)
    (hm : 0<v 2103) (hKd : 0<v 2105) (hAn : 0<v 2108) (hAd : 0<v 2109)
    (hTn : 0<v 2110) (hTd : 0<v 2111) (hEn : 0<v 2106) (hEd : 0<v 2107)
    (hA : (v 2108:ℚ)/v 2109=alpha (v 2101) d)
    (hw : ∀i∈ids,(v i).bits.length ≤ W) (hD : (BufferMachine.dataOf v).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→Blank s.val i) :
    let D := BufferMachine.dataOf v
    let K := (D.conditionNum:ℚ)/D.conditionDen
    let ε := (D.epsilonNum:ℚ)/D.epsilonDen
    let τ := (D.tauNum:ℚ)/D.tauDen
    let hε : 0<ε := div_pos (by exact_mod_cast hEn) (by exact_mod_cast hEd)
    let hτ : 0<τ := div_pos (by exact_mod_cast hTn) (by exact_mod_cast hTd)
    let N := Nat.find (bufferSearch_exists e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ)
    ∃cost t w,Executes input tape BufferMachine.restartCode cost s t ∧
      cost ≤ BufferMachine.resetCost W+BufferMachine.costBound N B ∧
      NatAssign.Bank ids w t.val ∧ (∀i,i<5→Blank t.val i) ∧
      (∀i∈ids,(w i).bits.length ≤ max W (BufferMachine.width N B)) ∧
      (∀i∈BufferMachine.extra,w i=BufferMachine.values D N i) ∧
      (∀i∉BufferMachine.ids,w i=v i) ∧ w 35=0 ∧ w 36=0 ∧
      Word t.val 2115 (selectedBuffer e D.wells D.sourceSize D.length d D.span K ε τ hm hε hτ) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  have sub : BufferMachine.ids⊆ids := by decide +kernel
  obtain ⟨cost,t,he,hc,ht,hword,hf⟩ := BufferMachine.restart v e d W B hC hm hKd hAn hAd hTn hTd hEn hEd hA
    (fun i hi=>hw i (sub hi)) hD input tape s (fun i hi=>hb i (sub hi)) hs
  obtain ⟨u,bu,su,hu,wu,u35,u36⟩ := ht
  let w := NatAssign.overlay BufferMachine.ids u v
  have frame : BinaryPrecision.Frame (BufferMachine.ids∪{0,1,2,3,4}) s.val t.val :=
    hf.mono (by decide +kernel)
  have bt : NatAssign.Bank ids w t.val := hb.overlay bu (by decide +kernel) frame
  refine ⟨cost,t,w,he,hc,bt,su,NatAssign.overlay_width hw wu,?_,?_,?_,?_,hword,hf.mono (by decide +kernel)⟩
  · intro i hi
    have hh : i∈BufferMachine.ids := Finset.mem_union_left _ hi
    simpa only [w,NatAssign.overlay,ite_eq_left hh] using hu i hi
  · intro i hi;exact NatAssign.overlay_outside v u i hi
  · simpa only [w,NatAssign.overlay,show 35∈BufferMachine.ids by decide +kernel,ite_true] using u35
  · simpa only [w,NatAssign.overlay,show 36∈BufferMachine.ids by decide +kernel,ite_true] using u36


theorem tau (v : ℕ→ℕ) (L d W B : ℕ) (hL : 0<L)
    (hden : v 2233=OuterTau.budgetDen L d) (hone : v 2234=1)
    (hcounter : v 2238=0) (houtput : v 2237=0)
    (hgeo : ∀i∈Geometric.extra,v i=0) (hw : ∀i∈ids,(v i).bits.length ≤ W)
    (htw : ∀i∈OuterTau.ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→Blank s.val i) :
    let N := Nat.clog 2 (OuterTau.budgetDen L d)
    let w := NatAssign.overlay OuterTau.ids (OuterTau.result v N) v
    ∃cost t,Executes input tape OuterTau.code cost s t ∧ cost ≤ OuterTau.costBound N B ∧
      NatAssign.Bank ids w t.val ∧ (∀i,i<5→Blank t.val i) ∧
      (∀i∈ids,(w i).bits.length ≤ max W (OuterTau.width N B)) ∧
      Word t.val 2237 (2^N) ∧ (1:ℚ)/(2^N)=Parameters.tau L d hL ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  have sub : OuterTau.ids⊆ids := by decide +kernel
  obtain ⟨cost,t,he,hc,bt,st,wt,hwout,hval,hf⟩ := OuterTau.executes v L d B hL hden hone hcounter houtput
    hgeo htw input tape s (fun i hi=>hb i (sub hi)) hs
  have frame : BinaryPrecision.Frame (OuterTau.ids∪{0,1,2,3,4}) s.val t.val := hf.mono (by decide +kernel)
  exact ⟨cost,t,he,hc,hb.overlay bt (by decide +kernel) frame,st,NatAssign.overlay_width hw wt,
    hwout,hval,hf.mono (by decide +kernel)⟩

#print axioms spacing
#print axioms buffer
#print axioms tau
end Maxwell.Continuum.Parameters.OuterMachine
