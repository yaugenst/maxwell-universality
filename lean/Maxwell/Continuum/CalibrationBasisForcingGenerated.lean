import Maxwell.Continuum.CalibrationBasisForcingCounter

/-! Source generation starts from the runtime radius and arbitrary old counter
contents. The program computes its traversal length and all source coefficients. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray
open ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank counterCode tableCode

def generatedCode (column : Fin 24) : Code := .seq counterCode (tableCode column)
def generatedCost (R B W H : ℕ) : ℕ := 2^120*(B+H+10)^2+
  (aliasArraySize R+1)*(13*counterWidth B+15)+aliasArraySize R*bodyCost (counterWidth B) W

theorem generated_executes (column : Fin 24) (R B W : ℕ) (hB : 103≤B)
    (a : Table (aliasArraySize R)) (v : ℕ → Parts) (n : ℕ → ℕ)
    (hn : ∀k∈ids bank,n k=dataValues v k) (hg : Good bank v)
    (hw : ∀k∈naturalIds,(n k).bits.length≤B) (hv : ∀k∈retained,(v k).Width B) (hR : n 311=R)
    (hm : a.MetadataWidth W) (hfit : 625≤addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank naturalIds n s.val) (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.OutputReady s) (hword : BankArray.Word s.val 201 xs) :
    ∃cost t b vf nf finalWord,Executes input tape (generatedCode column) cost s t ∧
      cost≤generatedCost R B W xs.length ∧ b.OutputReady t ∧ sameMetadata a b ∧ Good bank vf ∧
      NatAssign.Bank naturalIds nf t.val ∧ (∀k∈ids bank,nf k=dataValues vf k) ∧
      (∀k∈naturalIds,(nf k).bits.length≤prepareWidth (counterWidth B)) ∧
      (∀k∈retained,vf k=v k) ∧ nf 311=R ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀i : Fin (aliasArraySize R),(b.get i).Valid ∧
        (b.get i).value=rationalRightCoupling (rationalBasisField column)
          (arrayAliasAt R i) (arrayPolarizationAt R i)) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length≤counterWidth B ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,hc0,n0,r0,a0,z0,word0,ih0,random0,emitted0⟩ :=
    counter_executes a n v hn B (by omega) hw input tape xs s hs hz ha hword
  rw [hR] at word0
  obtain ⟨origin,word0⟩ := word0
  have width := counter_width n B (by omega) hw
  have countBits : (aliasArraySize R).bits.length≤counterWidth B := by
    have hh := width 315 (naturalIds_decode (by decide))
    rwa [counterValue,hR] at hh
  have hBC : B≤counterWidth B := by unfold counterWidth;omega
  have hCP : counterWidth B≤prepareWidth (counterWidth B) := by unfold prepareWidth;omega
  have radius : counterValues n 311=R := (counterValues_keep n 311 (by decide)).trans hR
  have radiusWidth : R.bits.length≤counterWidth B := by
    rw [← hR]
    exact (hw 311 (naturalIds_decode (by decide))).trans hBC
  obtain ⟨c1,t,b,vf,nf,finalWord,e1,hc1,b1,metadata,g1,n1,agree1,w1,keep1,radius1,z1,values,word1,len1,ih1,random1,emitted1,_⟩ :=
    table_executes column R (counterWidth B) W (hB.trans hBC) a v (counterValues n)
      (counterValues_agrees n v hn) hg (fun k hk => (width k hk).trans hCP)
      (fun k hk => (hv k hk).mono hBC) radiusWidth radius hm hfit hsep input tape
      (aliasArraySize R).bits origin countBits (addressValue_bits _) u n0 z0 a0 word0
  refine ⟨c0+c1,t,b,vf,nf,finalWord,e0.seq e1,?_,b1,metadata,g1,n1,agree1,w1,keep1,radius1,z1,
    values,⟨origin,word1⟩,len1.trans_le countBits,ih1.trans ih0,random1.trans random0,emitted1.trans emitted0⟩
  have countCost := Nat.mul_le_mul_left (aliasArraySize R+1)
    (show 13*(aliasArraySize R).bits.length+15≤13*counterWidth B+15 by omega)
  unfold generatedCost
  omega

#print axioms generated_executes
end Maxwell.Continuum.Calibration.BasisForcing
