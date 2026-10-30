import Maxwell.Continuum.FourierTensorAliasRead

/-! A fixed alias step loads the actual Fourier row and computes its
complete tensor summand, preserving the stored alias countdown. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

theorem generatedTerm_preserves_count {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} (h : Executes input tape generatedTermCode cost s t) :
    t.val.tapes 1099=s.val.tapes 1099 := by
  apply h.tapesBelow (bound := 1099) _ _ le_rfl
  simp only [generatedTermCode,Code.tapesBelow,Bool.and_eq_true]
  exact ⟨Code.tapesBelow_mono axesCode_tapesBelow (by decide),by decide⟩

theorem FactorReady.alias_count_frame {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (f : CountedShifted.Frame 1099 s t) : FactorReady a Q N b v t := by
  have keep (i : ℕ) (hi : i≠1099) := f.2.2.2.2.2.1 i hi
  have hr := Ready.count_frame tensorBank v 1099 (by decide) h.ready f
  have fb : BinaryPrecision.Frame (RationalDataflow.workspace (insert 33 termBank)) s.val t.val :=
    ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,fun i hi => keep i (by
      intro he;subst i;exact hi (by decide))⟩
  have ha := h.source.arithmetic_frame (insert 33 termBank) fb hr.2
  have hb : b.OutputReady t := by
    apply h.output.transfer f.2.2.1 _ ha.scratch ha.seven
    intro i hi
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  refine ⟨hr,?_,⟨blank_of_eq (keep 4 (by decide)) h.floor.1,?_⟩,?_,ha,hb,
    blank_of_eq (keep 144 (by decide)) h.power,blank_of_eq (keep 146 (by decide)) h.powerCount,
    blank_of_eq (keep 680 (by decide)) h.inner,?_⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    exact blank_of_eq (keep i (by intro he;subst i;exact (by decide : 1099∉PhaseMachine.Runtime.ids) hip)) (h.phase i hi)
  · intro i hi
    apply blank_of_eq (keep i _ ) (h.floor.2 i hi)
    intro he;subst i
    exact (by decide : 1099∉DyadicFloor.extraIds∪NaturalQuotient.workPorts) hi
  · intro i hi
    exact word_of_eq (keep i (by intro he;subst i;exact (by decide : 1099∉setupIds) hi)) (h.setup i hi)
  · intro i hi
    have hh := savedPorts_range i hi
    exact blank_of_eq (keep i (by omega)) (h.saved i hi)

def aliasStepCode : Code := .seq aliasReadCode generatedTermCode
def aliasStepCost (Q N A W k : ℕ) (j : Fin 3→ℕ) : ℕ :=
  aliasReadCost W k+generatedTermCost Q N A W j

theorem aliasStep_executes {n B : ℕ} (a : Table (5*n)) (Q N A W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1))) (hma : a.MetadataWidth W)
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (q : Fin n→Fin 3→ℚ) (amp : Fin n→ComplexDyadic B) (hrows : FourierRows a q amp)
    (hq : ∀r i,|q r i| ≤ Q) (j : Fin 3→ℕ) (hj : ∀i,j i<waveDegree (8*Q) N+1)
    (v : ℕ→Parts) (hw : WidthBank tensorBank W v) (hWA : W ≤ A) (ha : (v 32).Width A)
    (hvalid : (v 32).Valid) (hindices : ∀i,(v (17+i.val)).positive=j i)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (oldIndex : ℕ) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length ≤ W)
    (r : Fin n) (hrow : addressValue xs=r.val) (s : Store)
    (hs : FactorReady a Q N b v s) (hr : Ready termBank v s)
    (hindex : Word s.val 1048 oldIndex) (hcount : BankArray.Word s.val 1099 xs) :
    ∃cost t w output,Executes input tape aliasStepCode cost s t ∧
      cost ≤ aliasStepCost Q N A W xs.length j ∧ FactorReady a Q N output w t ∧
      Ready termBank w t ∧ WidthBank tensorBank W w ∧ (w 32).Width (A+22*W+23) ∧
      CacheTableMetadata output b ∧ (∀i,(w (17+i.val)).positive=j i) ∧ (w 32).Valid ∧
      (w 32).denominator=(v 32).denominator ∧
      (w 32).value=(v 32).value+
        ((complexDyadicMul (amp r) (complexDyadicTriple (fun i => waveRoundedCoefficient (q r i) Q N (j i)))).1.numerator:ℚ) ∧
      Word t.val 1048 (j 2) ∧ t.val.tapes 1099=s.val.tapes 1099 := by
  obtain ⟨c0,s0,e0,h0,f0,r0,w0,ix0,count0⟩ := aliasRead_executes a b W hma v hw input tape xs hlen
    (by rw [hrow];exact r.isLt) s hs hr hcount
  rw [hrow] at f0 r0 w0
  have hi := hrows.loaded r v j hindices
  have acc : aliasLoaded a r.val v 32=v 32 := aliasLoaded_keep a r.val v 32 (by omega)
  obtain ⟨c1,t,w,output,e1,h1,f1,r1,w1,acc1,m1,in1,val1,den1,result,index1⟩ :=
    generatedTerm_executes a Q N A W b hm hsep hdisjoint hfit
      (aliasLoaded a r.val v) w0 hWA (by simpa only [acc] using ha) (q r) j (amp r)
      hi.1 hi.2.1 hi.2.2 (by simpa only [acc] using hvalid) (hq r) hj hQ hN hW hprecision hgrid
      oldIndex hold input tape s0 f0 r0 (word_of_eq ix0 hindex)
  refine ⟨c0+c1,t,w,output,e0.seq e1,Nat.add_le_add h0 h1,f1,r1,w1,acc1,m1,
    fun i => (in1 i).2.2,val1,den1.trans (congrArg Parts.denominator acc),?_,index1,
    (generatedTerm_preserves_count e1).trans count0⟩
  simpa only [acc] using result

theorem aliasStepCost_mono {Q N A A' W k : ℕ} (j : Fin 3→ℕ) (h : A ≤ A') :
    aliasStepCost Q N A W k j ≤ aliasStepCost Q N A' W k j := by
  have h0 := Nat.pow_le_pow_left (by omega : A+22*W+22+3 ≤ A'+22*W+22+3) 2
  have h1 := Nat.pow_le_pow_left (by omega : A+22*W+23+3 ≤ A'+22*W+23+3) 2
  unfold aliasStepCost generatedTermCost termReturnCost termCost operationCost
  exact Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right
      (Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left _ h0)) 1)
      (Nat.mul_le_mul_left 7 (Nat.mul_le_mul_left _ h1))) 1) _) _

#print axioms aliasStep_executes
#print axioms aliasStepCost_mono
end Maxwell.Continuum.Profile.WaveMachine.Runtime
