import Maxwell.Continuum.ParameterOuterTestData

/-! Execute the leakage and tail floor powers, construct their exact
comparison operands, and return the outer stopping flag. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def stoppingCode : Code := .seq (decayCode 2220 2250 2251)
  (.seq (decayCode 2221 2252 2253) (.seq (NatAssign.code tailPrepare) (AllComparisons.code tests)))
def stoppingCost (W : ℕ) : ℕ := decayCost W+(decayCost W+
  (3000*8^tailPrepare.length*(W+2)^2+(tests.length*(AllComparisons.unitCost W+2)+2)))

theorem extra_ge : ∀i∈extra,40 ≤ i := by
  intro i hi
  simp only [extra,SpacingMachine.extra,BufferMachine.extra,Geometric.extra,DynamicPower.ids,
    Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem stoppingStage (D : Data) (hD : D.Positive) (e k W B : ℕ) (hC : D.constant=2^e)
    (v : ℕ→ℕ) (ho : StageOutputs D hD e k v) (hw : ∀i∈ids,(v i).bits.length ≤ W)
    (hu : 2^k+1 ≤ W) (hL : stageLength k+1 ≤ W)
    (hsrc : ∀i∈tailSources,(v i).bits.length ≤ B) (htail : tailInputWidth B ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→RationalAccumulator.Blank s.val i) :
    ∃cost t w,Executes input tape stoppingCode cost s t ∧ cost ≤ stoppingCost W ∧
      NatAssign.Bank ids w t.val ∧ (∀i,i<5→RationalAccumulator.Blank t.val i) ∧
      (∀i∈ids,(w i).bits.length ≤ W) ∧ StageOutputs D hD e k w ∧
      t.val.registers 35=decide (¬OuterTest (D.input hD) e k) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c1,a,e1,p1,b1,s1,w1,f1⟩ := decay_executes 2220 2250 2251 (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) v W ho.core.slow (by simpa only [ho.core.binary] using hu) hw input tape s hb hs
  let v1 := decayValues v 2220 2250 2251
  have keep1 (i : ℕ) (hi : i∈stageRetained) : v1 i=v i := by
    apply decayValues_other
    simp only [stageRetained,retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [decayClears];omega
  have h1 := ho.congr keep1
  obtain ⟨c2,b,e2,p2,b2,s2,w2,f2⟩ := decay_executes 2221 2252 2253 (Or.inr rfl) (Or.inr rfl)
    (Or.inr rfl) v1 W h1.core.slow (by simpa only [h1.core.length] using hL) w1 input tape a b1 s1
  change NatAssign.Bank ids (decayed v) b.val at b2
  change ∀i∈ids,(decayed v i).bits.length ≤ W at w2
  have h2 := ho.congr (decayed_other v)
  have src : ∀i∈tailSources,(decayed v i).bits.length ≤ B := by
    intro i hi
    rw [decayed_other v i ((show tailSources⊆stageRetained by decide +kernel) hi)]
    exact hsrc i hi
  obtain ⟨cp,p,ep,pp,bp,sp,fp⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) tailPrepare tailPrepare_valid (decayed v) input tape b b2 s2
  let vp := NatAssign.values tailPrepare (decayed v)
  have wp : ∀i∈ids,(vp i).bits.length ≤ W := NatAssign.values_local_width ids tailSources tailPrepare
    tailPrepare_valid (decayed v) W B w2 src
    (by simp [tailPrepare,prepareTail,Rational.clear,NatAssign.Instruction.literalWidth])
    (by decide +kernel) htail
  have keep (i : ℕ) (hi : i∈stageRetained∪{2251,2253}) : vp i=decayed v i := by
    apply NatAssign.values_preserves
    simp only [stageRetained,retained,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    simp [tailPrepare,prepareTail,Rational.clear,NatAssign.Instruction.target]
    omega
  have hp := h2.congr (fun i hi=>keep i (Finset.mem_union_left _ hi))
  obtain ⟨pn,p35,p36⟩ := tailPrepare_fields (decayed v) h2.core.four
  have dc := congrArg Data.constant h2.core.data
  have dj := congrArg Data.wells h2.core.data
  change decayed v 2210=D.constant at dc
  change decayed v 2212=D.wells at dj
  have pn' : vp 2260=OuterStopping.tailNumerator D.constant D.wells (stageLength k)
      (3^(stageSpacing (D.input hD) e k)) := by
    simpa only [dc,dj,h2.core.length,h2.spacing.zetaDen] using pn
  have pl : vp 2251=2^((2^k)/slowDivisor) :=
    (keep _ (by decide +kernel)).trans (by simpa only [ho.core.binary] using (decayed_fields v).1)
  have pt : vp 2253=2^(stageLength k/slowDivisor) :=
    (keep _ (by decide +kernel)).trans (by simpa only [ho.core.length] using (decayed_fields v).2)
  obtain ⟨ct,t,wt,et,ptc,hflag,bt,st,ht,ww,_,_,ft⟩ := AllComparisons.executes extra extra_ge tests
    tests_valid vp W wp (tests_enabled D hD e k vp hp) p35 p36 input tape p bp (fun i hi=>sp i (by omega))
  have hf : tests.any (AllComparisons.failed vp)=decide (¬OuterTest (D.input hD) e k) := by
    have iff := tests_iff D hD e k hC vp hp pl pt pn'
    cases hh : tests.any (AllComparisons.failed vp) with
    | false => simp [iff.mp hh]
    | true =>
      have hn : ¬OuterTest (D.input hD) e k := by intro hn;have := iff.mpr hn;simp_all
      simp [hn]
  have wtout := hp.congr (fun i hi=>ht i ((show stageRetained⊆extra by decide +kernel) hi))
  have ppb := NatAssign.price_bound ids tailPrepare tailPrepare_valid (decayed v) W w2
    (by simp [tailPrepare,prepareTail,Rational.clear,NatAssign.Instruction.literalWidth])
  refine ⟨c1+(c2+(cp+ct)),t,wt,e1.seq (e2.seq (ep.seq et)),
    Nat.add_le_add p1 (Nat.add_le_add p2 (Nat.add_le_add (pp.trans ppb) ptc)),bt,?_,ww,wtout,
    hflag.trans hf,f1.trans (f2.trans ((fp.mono (by decide +kernel)).trans (ft.mono (by decide +kernel))))⟩
  intro i hi
  by_cases h4 : i<4
  · exact st i h4
  · have he : i=4 := by omega
    subst i
    exact RationalAccumulator.blank_of_eq (ft.tapes 4 (by decide +kernel)) (sp 4 (by decide))

#print axioms stoppingStage
end Maxwell.Continuum.Parameters.OuterMachine
