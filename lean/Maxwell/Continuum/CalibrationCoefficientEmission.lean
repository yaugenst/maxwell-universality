import Maxwell.Continuum.CalibrationTableCounter
import Maxwell.Continuum.CalibrationForcingTableLoop

/-! One fixed program generates the complete source prefix and transition
matrix from the stored source field and five scalar inputs. Both runtime
loop lengths are computed, and every raw coefficient is written. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def coefficientBaseWidth (B : ℕ) : ℕ := countWidth (forcingEmissionWidth (countWidth B))
def coefficientWidth (B : ℕ) : ℕ := emissionWidth (coefficientBaseWidth B)
def coefficientCode : Code := .seq (tableCounterCode aliasCountPlan)
  (.seq forcingTableCode (.seq (tableCounterCode matrixCountPlan) matrixTableCode))
def coefficientCost (R B W : ℕ) : ℕ :=
  2^120*(2*B+10)^2+
  ((aliasRowCount R+1)*(13*countWidth B+15)+
    aliasRowCount R*(2^1120*(forcingEmissionWidth (countWidth B)+W+10)^2))+
  2^120*(forcingEmissionWidth (countWidth B)+countWidth B+10)^2+
  ((aliasArraySize R*aliasArraySize R+1)*(13*coefficientBaseWidth B+15)+
    aliasArraySize R*aliasArraySize R*(2^600*(coefficientWidth B+W+10)^2))

theorem countWidth_ge (B : ℕ) : B≤countWidth B := by unfold countWidth; omega
theorem forcingEmissionWidth_base_ge (B : ℕ) : B≤forcingEmissionWidth B :=
  (forcingBaseWidth_ge B).trans (forcingEmissionWidth_ge B)

theorem sameMetadata_trans {T : ℕ} (a b c : PartArray.Table T)
    (hab : sameMetadata a b) (hbc : sameMetadata b c) : sameMetadata a c :=
  ⟨hbc.1.trans hab.1,hbc.2.1.trans hab.2.1,hbc.2.2.1.trans hab.2.2.1,
    hbc.2.2.2.1.trans hab.2.2.2.1,hbc.2.2.2.2.trans hab.2.2.2.2⟩

theorem coefficient_executes {T : ℕ} (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table T) (B W : ℕ) (hB : 101≤B)
    (hT : aliasArraySize R+aliasArraySize R*aliasArraySize R≤T)
    (v : ℕ→Parts) (n : ℕ→ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hradius : n 311=R) (haValid : ∀ i, (a.get i).Valid)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (hfit : coefficientWidth B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (hlen : xs.length≤B)
    (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hword : BankArray.Word s.val 201 xs) :
    ∃ (cost : ℕ) (t : Store) (c : PartArray.Table T) (vf : ℕ→Parts) (nf : ℕ→ℕ) (finalWord : List Bool),
      Executes input tape coefficientCode cost s t ∧ cost≤coefficientCost R B W ∧
      c.OutputReady t ∧ sameMetadata b c ∧ NatAssign.Bank emissionIds nf t.val ∧
      (∀ k∈ids RawFree.neighborRegisters, nf k=dataValues vf k) ∧
      (∀ k∈emissionIds, (nf k).bits.length≤coefficientWidth B) ∧
      (∀ k∈matrixParameters, vf k=v k) ∧ nf 311=R ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀ i : Fin (aliasArraySize R),
        (c.get (sourceSlot R (show aliasArraySize R≤T by omega) i)).Valid ∧
        (c.get (sourceSlot R (show aliasArraySize R≤T by omega) i)).value=
          cachedForcing (v 0).value (v 1).value (fun j => (RawFree.quasiParts v j).value)
            R (tableSource R a) i) ∧
      (∀ k : Fin (aliasArraySize R*aliasArraySize R),
        (c.get (matrixSlot R hT k)).Valid ∧
        (c.get (matrixSlot R hT k)).value=cachedTransitionMatrix (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (flatRow R k) (flatColumn R k)) ∧
      (∀ i : Fin T, aliasArraySize R+aliasArraySize R*aliasArraySize R ≤ i.val → c.get i=b.get i) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length≤coefficientBaseWidth B ∧
      (∀ k∈([200,202,203,204,205]:List ℕ), BankArray.Word t.val k
        (if k=200 then a.width else if k=202 then a.basePositive else if k=203 then a.baseNegative
          else if k=204 then a.baseDenominator else a.clock)) ∧
      ContinuationFrame s.val t.val := by
  let F := countWidth B
  let U := forcingEmissionWidth F
  let G := coefficientBaseWidth B
  let M := coefficientWidth B
  have hBF : B≤F := countWidth_ge B
  have hFU : F≤U := forcingEmissionWidth_base_ge F
  have hUG : U≤G := countWidth_ge U
  have hGM : G≤M := emission_width_ge G
  have hR : R.bits.length≤B := by simpa only [hradius] using hw 311 (by decide)
  obtain ⟨c0,u0,e0,hc0,bank0,width0,_,a0,b0,z0,count0,continuation0⟩ := tableCounter_executes a b aliasCountPlan
    (Or.inl rfl) v n B (by omega) hn hw input tape xs s hs hz ha hb hword
  let n0 := NatAssign.values aliasCountPlan n
  have radius0 : n0 311=R := (countPlans_keep aliasCountPlan (Or.inl rfl) n 311 (by decide)).trans hradius
  have countValue0 : n0 332=aliasRowCount R := by
    change NatAssign.values aliasCountPlan n 332=_
    rw [aliasCount_value,hradius]
  let xs0 := (n0 332).bits
  obtain ⟨origin0,word0⟩ := count0
  obtain ⟨c1,u1,b1,v1,n1,word1,e1,hc1,a1,out1,meta1,bank1,agree1,width1,param1,radius1,z1,
      source1,padding1,counter1,len1,continuation1⟩ := forcingTable_executes R a b F W (by omega) (by omega) v n0
    (countPlans_agrees aliasCountPlan (Or.inl rfl) n v hn)
    (fun k hk => (width0 k hk).trans hFU)
    (fun k hk => ⟨(hp k hk).1.mono hBF,(hp k hk).2⟩) (hR.trans hBF) radius0 haValid
    (haMeta.mono hBF) hbMeta ((hUG.trans hGM).trans hfit) hsep hdisjoint ht hE hr input tape
    xs0 origin0 (width0 332 (by decide)) (by simp only [xs0,addressValue_bits,countValue0])
    u0 bank0 z0 a0 b0 word0
  have p0 := param1 0 (by decide)
  have p1 := param1 1 (by decide)
  have quasi : RawFree.quasiParts v1=RawFree.quasiParts v := by
    funext k
    fin_cases k
    · exact param1 16 (by decide)
    · exact param1 17 (by decide)
    · exact param1 18 (by decide)
  obtain ⟨c2,u2,e2,hc2,bank2,width2,_,a2,out2,z2,count2,continuation2⟩ := tableCounter_executes a b1 matrixCountPlan
    (Or.inr (Or.inl rfl)) v1 n1 U (by omega) agree1 width1 input tape word1 u1 bank1 z1 a1 out1
    ⟨origin0,counter1⟩
  let n2 := NatAssign.values matrixCountPlan n1
  have radius2 : n2 311=R := (countPlans_keep matrixCountPlan (Or.inr (Or.inl rfl)) n1 311 (by decide)).trans radius1
  have countValue2 : n2 332=aliasArraySize R*aliasArraySize R := by
    change NatAssign.values matrixCountPlan n1 332=_
    rw [(matrixCount_values n1).2,radius1]
  let xs2 := (n2 332).bits
  obtain ⟨origin2,word2⟩ := count2
  have fitG : emissionWidth G≤addressValue b.width := hfit
  obtain ⟨c3,t,c,vf,nf,word3,e3,hc3,out3,meta3,bank3,agree3,width3,param3,radius3,z3,
      matrix3,outside3,counter3,len3,headers3,continuation3⟩ := matrixTable_executes b1 R G W (by omega) hT v1 n2
    (countPlans_agrees matrixCountPlan (Or.inr (Or.inl rfl)) n1 v1 agree1)
    (fun k hk => (width2 k hk).trans hGM)
    (fun k hk => by rw [param1 k hk]; exact ⟨(hp k hk).1.mono (hBF.trans (hFU.trans hUG)),(hp k hk).2⟩)
    (hR.trans (hBF.trans (hFU.trans hUG))) radius2 (sameMetadata_width b b1 meta1 W hbMeta)
    (by simpa only [meta1.1] using fitG) (sameMetadata_separated b b1 meta1 hsep)
    (by simpa only [p0] using ht) (by simpa only [p1] using hE) (by simpa only [quasi] using hr)
    input tape xs2 origin2 (width2 332 (by decide)) (by simp only [xs2,addressValue_bits,countValue2])
    u2 bank2 z2 out2 word2
  refine ⟨c0+(c1+(c2+c3)),t,c,vf,nf,word3,e0.seq (e1.seq (e2.seq e3)),?_,out3,
    sameMetadata_trans b b1 c meta1 meta3,bank3,agree3,width3,
    (fun k hk => (param3 k hk).trans (param1 k hk)),radius3,z3,?_,?_,?_,⟨origin2,counter3⟩,?_,?_,continuation0.trans (continuation1.trans (continuation2.trans continuation3))⟩
  · have len0 : xs0.length≤F := width0 332 (by decide)
    have len2 : xs2.length≤G := width2 332 (by decide)
    have len1' : word1.length≤F := len1.trans_le len0
    have h0 := hc0.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : B+xs.length+10≤2*B+10) 2))
    have h1 : c1≤(aliasRowCount R+1)*(13*F+15)+aliasRowCount R*(2^1120*(U+W+10)^2) := by
      exact hc1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)
    have h2 := hc2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : U+word1.length+10≤U+F+10) 2))
    have h3 : c3≤(aliasArraySize R*aliasArraySize R+1)*(13*G+15)+
        aliasArraySize R*aliasArraySize R*(2^600*(M+W+10)^2) := by
      exact hc3.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)
    change c0+(c1+(c2+c3))≤_
    unfold coefficientCost
    dsimp only [F,U,G,M] at h0 h1 h2 h3
    omega
  · intro i
    rw [outside3 (sourceSlot R (by omega) i) (Or.inl i.isLt)]
    exact source1 i
  · intro k
    simpa only [p0,p1,quasi] using matrix3 k
  · intro i hi
    rw [outside3 i (Or.inr hi),padding1 i (by omega)]
  · exact len3.trans_le (width2 332 (by decide))

  · intro k hk
    apply BankArray.word_of_eq (headers3 k hk)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl
    · simpa using a2.width
    · simpa using a2.basePositive
    · simpa using a2.baseNegative
    · simpa using a2.baseDenominator
    · simpa using a2.clock

#print axioms coefficient_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
