import Maxwell.Continuum.RationalDataflowInverse

/-! A fixed signed-magnitude normalization for integer-valued raw registers.
It subtracts the two stored numerator channels and emits the literal integer
representation, including zero, without a rational-reduction oracle. -/
namespace Maxwell.Continuum.RationalDataflow.IntegerCanonical
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def result (x : Parts) : Parts :=
  if x.positive<x.negative then ⟨0,IntegerNormSquare.magnitude x.positive x.negative,1⟩
  else ⟨IntegerNormSquare.magnitude x.positive x.negative,0,1⟩

theorem result_literal (x : Parts) : result x=Parts.literal (((x.positive:ℤ)-x.negative:ℤ):ℚ) := by
  simp only [Parts.literal,Rat.num_intCast,Rat.den_intCast]
  by_cases h : x.positive<x.negative
  · rw [result,ite_eq_left h,Parts.magnitude_eq_of_lt x h]
    congr 1 <;> omega
  · rw [result,ite_eq_right h,Parts.magnitude_eq_of_le x (by omega)]
    congr 1 <;> omega

theorem result_eq_literal_value (x : Parts) (hd : x.denominator=1) : result x=Parts.literal x.value := by
  rw [result_literal]
  congr 1
  simp [Parts.value,hd]

theorem result_valid (x : Parts) : (result x).Valid := by
  unfold result Parts.Valid
  split_ifs <;> exact Nat.zero_lt_one

theorem result_width (B : ℕ) (x : Parts) (hx : x.Width B) : (result x).Width (B+1) := by
  have hm := (IntegerNormSquare.magnitude_bits_length_le x.positive x.negative).trans
    (Nat.add_le_add_right (max_le hx.1 hx.2.1) 1)
  unfold result
  have hz : (0:ℕ).bits.length ≤ B+1 := by simp
  have ho : (1:ℕ).bits.length ≤ B+1 := by simpa only [show (1:ℕ).bits.length=1 by decide] using Nat.le_add_left 1 B
  split_ifs
  · exact ⟨hz,hm,ho⟩
  · exact ⟨hm,hz,ho⟩

def tail (negative : Bool) (target : ℕ) : List NatAssign.Instruction :=
  (if negative then [.literal (positivePort target) 0,.copy 34 (negativePort target),.literal (denominatorPort target) 1]
  else [.copy 34 (positivePort target),.literal (negativePort target) 0,.literal (denominatorPort target) 1])++clearMagnitude

def code (target source : ℕ) : Code := .seq (NatAssign.code (prepareInverse source))
  (.seq RationalMagnitude.program (.branch 23 (NatAssign.code (tail true target)) (NatAssign.code (tail false target))))

theorem tail_valid (S : Finset ℕ) (negative : Bool) (target : ℕ) (ht : target∈S) :
    ∀a∈tail negative target,a.Valid (ids S) := by
  have hp := cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts])
  have hn := cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts])
  have hd := cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts])
  have hmem (i : ℕ) (hi : i∈RationalMagnitude.ids) := magnitude_subset S hi
  have hpg := positivePort_ge target
  have hng := negativePort_ge target
  cases negative <;>
    simp [tail,clearMagnitude,NatAssign.Instruction.Valid,hp,hn,hd,
      hmem 30 (by decide),hmem 31 (by decide),hmem 32 (by decide),hmem 33 (by decide),
      hmem 34 (by decide),hmem 35 (by decide),hmem 36 (by decide)] <;> omega

theorem tail_length (negative : Bool) (target : ℕ) : (tail negative target).length=10 := by
  cases negative <;> rfl

theorem tail_literalWidth (negative : Bool) (target : ℕ) : ∀a∈tail negative target,a.literalWidth ≤ 1 := by
  cases negative <;> simp [tail,clearMagnitude,NatAssign.Instruction.literalWidth]

theorem tail_values (v : ℕ→Parts) (target source : ℕ) :
    NatAssign.values (tail (decide ((v source).positive<(v source).negative)) target)
      (afterInverseMagnitude v source)=dataValues (Function.update v target (result (v source))) := by
  rw [←writeParts_dataValues]
  have htp := positivePort_ge target
  have htn := negativePort_ge target
  have htd := denominatorPort_ge target
  by_cases hneg : (v source).positive<(v source).negative
  all_goals
    simp only [hneg,decide_true,decide_false,tail,ite_true]
    rw [values_append]
    ext i
    by_cases hi : i<1000
    · simp (disch := omega) [clearMagnitude,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,afterInverseMagnitude,beforeInverse,
        writeParts,result,hneg,Function.update_apply,dataValues_small v hi]
    · simp (disch := omega) [clearMagnitude,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,afterInverseMagnitude,beforeInverse,
        writeParts,result,hneg,Function.update_apply]

theorem executes (S : Finset ℕ) (target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (B : ℕ) (hw : ∀i∈S,(v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃cost t,Executes input tape (code target source) cost s t ∧ cost ≤ operationCost B ∧
      Ready S (Function.update v target (result (v source))) t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := fixedStage_executes S (prepareInverse source)
    (prepareInverse_valid S source hs') (by simp [prepareInverse]) (dataValues v) B
    (dataValues_width S v B hw) (by simp [prepareInverse,NatAssign.Instruction.literalWidth])
    input tape s hs.1 hs.2
  rw [prepareInverse_values] at b0
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,sg⟩ := RationalMagnitude.executes (ids S) (magnitude_subset S)
    (ids_ge S) (beforeInverse v source) (beforeInverse_inputs v source).2.2 input tape s0 b0 z0
  have hb1 : NatAssign.Bank (ids S) (afterInverseMagnitude v source) s1.val := by
    simpa only [afterInverseMagnitude,(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1] using b1
  have hc1 : c1 ≤ 300*(2*B+4) := by
    rw [(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1] at h1
    exact h1.trans (Nat.mul_le_mul_left 300 (by
      have hp := (hw source hs').1
      have hn := (hw source hs').2.1
      omega))
  have hsg : s1.val.registers 23=decide ((v source).positive<(v source).negative) := by
    simpa only [(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1,magnitude_sign] using sg
  have frame : BinaryPrecision.Frame (workspace S) s.val s1.val := f0.trans (f1.mono (by
    intro i hi
    rcases Finset.mem_union.mp hi with hz|hm
    · exact Finset.mem_union_left _ hz
    · exact Finset.mem_union_right _ (magnitude_subset S hm)))
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := fixedStage_executes S
    (tail (decide ((v source).positive<(v source).negative)) target) (tail_valid S _ target ht)
    (by rw [tail_length];decide) (afterInverseMagnitude v source) (B+1)
    (afterInverseMagnitude_width S v source hs' B hw)
    (fun a ha => (tail_literalWidth _ target a ha).trans (by omega)) input tape s1 hb1 z1
  rw [tail_values] at b2
  have erun : Executes input tape (.branch 23 (NatAssign.code (tail true target))
      (NatAssign.code (tail false target))) (1+c2) s1 t := by
    by_cases hp : (v source).positive<(v source).negative
    · exact Executes.yes (by simpa only [hp,decide_true] using hsg)
        (by simpa only [hp,decide_true] using e2)
    · exact Executes.no (by simpa only [hp,decide_false] using hsg)
        (by simpa only [hp,decide_false] using e2)
  refine ⟨c0+(c1+(1+c2)),t,e0.seq (e1.seq erun),?_,⟨b2,z2⟩,frame.trans f2⟩
  have hc := inverse_cost B
  omega

#print axioms result_eq_literal_value
#print axioms executes
end Maxwell.Continuum.RationalDataflow.IntegerCanonical
