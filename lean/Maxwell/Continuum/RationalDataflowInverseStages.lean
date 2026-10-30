import Maxwell.Continuum.RationalDataflowLiteral

/-! Runtime signed reciprocal stages, retaining all other logical registers. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def prepareInverse (source : ℕ) : List NatAssign.Instruction :=
  [.copy (positivePort source) 30,.copy (negativePort source) 31]

def beforeInverse (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (dataValues v) 30 (v source).positive) 31 (v source).negative

def afterInverseMagnitude (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (beforeInverse v source) 34
    (IntegerNormSquare.magnitude (v source).positive (v source).negative)

def clearMagnitude : List NatAssign.Instruction :=
  [.literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,
   .literal 34 0,.literal 35 0,.literal 36 0]

def inverseTail (negative : Bool) (target source : ℕ) : List NatAssign.Instruction :=
  (if negative then
    [.copy (denominatorPort source) (negativePort target),.literal (positivePort target) 0,
     .copy 34 (denominatorPort target)]
   else
    [.copy (denominatorPort source) (positivePort target),.literal (negativePort target) 0,
     .copy 34 (denominatorPort target)]) ++ clearMagnitude

theorem workPort_mem (S : Finset ℕ) {i : ℕ} (hi : i∈workPorts) : i∈ids S :=
  Finset.mem_union_right _ hi

theorem magnitude_subset (S : Finset ℕ) : RationalMagnitude.ids⊆ids S := by
  intro i hi
  exact workPort_mem S (Finset.mem_union_right _ hi)

theorem prepareInverse_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀ a∈prepareInverse source, a.Valid (ids S) := by
  have hp := cell_mem hs (show positivePort source∈cellPorts source by simp [cellPorts])
  have hn := cell_mem hs (show negativePort source∈cellPorts source by simp [cellPorts])
  have h30 := magnitude_subset S (show 30∈RationalMagnitude.ids by decide)
  have h31 := magnitude_subset S (show 31∈RationalMagnitude.ids by decide)
  have hpg := positivePort_ge source
  have hng := negativePort_ge source
  simp [prepareInverse,NatAssign.Instruction.Valid,hp,hn,h30,h31]
  omega

theorem prepareInverse_values (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values (prepareInverse source) (dataValues v)=beforeInverse v source := by
  have hp := positivePort_ge source
  have hn := negativePort_ge source
  simp (disch := omega) [prepareInverse,beforeInverse,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem beforeInverse_inputs (v : ℕ→Parts) (source : ℕ) :
    beforeInverse v source 30=(v source).positive ∧
    beforeInverse v source 31=(v source).negative ∧ beforeInverse v source 34=0 := by
  simp [beforeInverse,dataValues]

theorem inverseTail_valid (S : Finset ℕ) (negative : Bool) (target source : ℕ)
    (ht : target∈S) (hs : source∈S) : ∀ a∈inverseTail negative target source, a.Valid (ids S) := by
  have hp := cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts])
  have hn := cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts])
  have hd := cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts])
  have hs' := cell_mem hs (show denominatorPort source∈cellPorts source by simp [cellPorts])
  have hmem (i : ℕ) (hi : i∈RationalMagnitude.ids) := magnitude_subset S hi
  have hdg := denominatorPort_ge target
  cases negative <;>
    simp [inverseTail,clearMagnitude,NatAssign.Instruction.Valid,hp,hn,hd,hs',
      hmem 30 (by decide),hmem 31 (by decide),hmem 32 (by decide),hmem 33 (by decide),
      hmem 34 (by decide),hmem 35 (by decide),hmem 36 (by decide)] <;> omega

theorem inverseTail_length (negative : Bool) (target source : ℕ) :
    (inverseTail negative target source).length=10 := by cases negative <;> rfl

theorem inverseTail_literalWidth (negative : Bool) (target source : ℕ) :
    ∀ a∈inverseTail negative target source, a.literalWidth=0 := by
  cases negative <;> simp [inverseTail,clearMagnitude,NatAssign.Instruction.literalWidth]

theorem afterInverseMagnitude_width (S : Finset ℕ) (v : ℕ→Parts) (source : ℕ)
    (hs : source∈S) (B : ℕ) (hw : ∀ i∈S, (v i).Width B) :
    ∀ i∈ids S, (afterInverseMagnitude v source i).bits.length≤B+1 := by
  intro i hi
  by_cases h34 : i=34
  · subst i
    simp only [afterInverseMagnitude,Function.update_self]
    exact (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le (hw source hs).1 (hw source hs).2.1) 1)
  · by_cases h31 : i=31
    · subst i
      simpa [afterInverseMagnitude,beforeInverse] using (hw source hs).2.1.trans (Nat.le_succ B)
    · by_cases h30 : i=30
      · subst i
        simpa [afterInverseMagnitude,beforeInverse] using (hw source hs).1.trans (Nat.le_succ B)
      · simpa only [afterInverseMagnitude,beforeInverse,Function.update_of_ne h34,
          Function.update_of_ne h31,Function.update_of_ne h30] using
          (dataValues_width S v B hw i hi).trans (Nat.le_succ B)

theorem inverseTail_values (v : ℕ→Parts) (target source : ℕ) :
    NatAssign.values (inverseTail (decide ((v source).positive<(v source).negative)) target source)
      (afterInverseMagnitude v source)=dataValues (Function.update v target (v source).inverse) := by
  rw [←writeParts_dataValues]
  have htp := positivePort_ge target
  have htn := negativePort_ge target
  have htd := denominatorPort_ge target
  have hsd := denominatorPort_ge source
  by_cases hneg : (v source).positive<(v source).negative
  all_goals
    simp only [hneg,decide_true,decide_false,inverseTail,ite_true]
    rw [values_append]
    ext i
    by_cases hi : i<1000
    · simp (disch := omega) [clearMagnitude,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,afterInverseMagnitude,beforeInverse,
        writeParts,Parts.inverse,hneg,Function.update_apply,dataValues_small v hi]
    · simp (disch := omega) [clearMagnitude,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,afterInverseMagnitude,beforeInverse,
        writeParts,Parts.inverse,hneg,Function.update_apply]
      <;> split_ifs <;> simp_all

#print axioms inverseTail_values

end Maxwell.Continuum.RationalDataflow
