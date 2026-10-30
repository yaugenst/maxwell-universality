import Maxwell.Continuum.RationalDataflowInverseStages

/-! The exact signed reciprocal program and its bit-operation bound. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def inverseCode (target source : ℕ) : Code :=
  .seq (NatAssign.code (prepareInverse source))
    (.seq RationalMagnitude.program
      (.branch 23 (NatAssign.code (inverseTail true target source))
        (NatAssign.code (inverseTail false target source))))

def operationCost (B : ℕ) : ℕ := 2^100*(B+3)^2

theorem stageCost_le_operationCost (B : ℕ) : stageCost B≤operationCost B := by
  unfold stageCost operationCost
  exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 2)

theorem inverse_cost (B : ℕ) :
    stageCost B+300*(2*B+4)+(1+stageCost (B+1))≤operationCost B := by
  have h : (B+2)^2≤(B+3)^2 := Nat.pow_le_pow_left (by omega) 2
  unfold stageCost operationCost
  norm_num
  nlinarith

theorem magnitude_sign (p n : ℕ) : SignedDifference.sign p.bits n.bits=decide (p<n) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,RationalAccumulator.address_bits] using SignedDifference.sign_iff p.bits n.bits

theorem inverse_executes (S : Finset ℕ) (target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (B : ℕ) (hw : ∀ i∈S, (v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (inverseCode target source) cost s t ∧ cost≤operationCost B ∧
      Ready S (Function.update v target (v source).inverse) t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := fixedStage_executes S (prepareInverse source)
    (prepareInverse_valid S source hs') (by simp [prepareInverse]) (dataValues v) B
    (dataValues_width S v B hw)
    (by simp [prepareInverse,NatAssign.Instruction.literalWidth]) input tape s hs.1 hs.2
  rw [prepareInverse_values] at b0
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,sg⟩ := RationalMagnitude.executes (ids S) (magnitude_subset S)
    (ids_ge S) (beforeInverse v source) (beforeInverse_inputs v source).2.2 input tape s0 b0 z0
  have hb1 : NatAssign.Bank (ids S) (afterInverseMagnitude v source) s1.val := by
    simpa only [afterInverseMagnitude,(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1] using b1
  have hc1 : c1≤300*(2*B+4) := by
    rw [(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1] at h1
    exact h1.trans (Nat.mul_le_mul_left 300 (by
      have hp := (hw source hs').1
      have hn := (hw source hs').2.1
      omega))
  have hsg : s1.val.registers 23=decide ((v source).positive<(v source).negative) := by
    simpa only [(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1,magnitude_sign] using sg
  have hframe : BinaryPrecision.Frame (workspace S) s.val s1.val :=
    f0.trans (f1.mono (by
      intro i hi
      rcases Finset.mem_union.mp hi with hz | hm
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ (magnitude_subset S hm)))
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := fixedStage_executes S
    (inverseTail (decide ((v source).positive<(v source).negative)) target source)
    (inverseTail_valid S _ target source ht hs') (by rw [inverseTail_length]; decide)
    (afterInverseMagnitude v source) (B+1) (afterInverseMagnitude_width S v source hs' B hw)
    (fun a ha => by rw [inverseTail_literalWidth _ target source a ha]; omega)
    input tape s1 hb1 z1
  rw [inverseTail_values] at b2
  have hrun : Executes input tape
      (.branch 23 (NatAssign.code (inverseTail true target source))
        (NatAssign.code (inverseTail false target source))) (1+c2) s1 t := by
    by_cases hp : (v source).positive<(v source).negative
    · have hs1 : s1.val.registers 23=true := by simpa only [hp,decide_true] using hsg
      have he2 : Executes input tape (NatAssign.code (inverseTail true target source)) c2 s1 t := by
        simpa only [hp,decide_true] using e2
      exact Executes.yes hs1 he2
    · have hs1 : s1.val.registers 23=false := by simpa only [hp,decide_false] using hsg
      have he2 : Executes input tape (NatAssign.code (inverseTail false target source)) c2 s1 t := by
        simpa only [hp,decide_false] using e2
      exact Executes.no hs1 he2
  refine ⟨c0+(c1+(1+c2)),t,e0.seq (e1.seq hrun),?_,⟨b2,z2⟩,hframe.trans f2⟩
  have hc := inverse_cost B
  omega

#print axioms inverse_executes

end Maxwell.Continuum.RationalDataflow
