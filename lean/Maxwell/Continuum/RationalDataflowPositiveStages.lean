import Maxwell.Continuum.RationalDataflowInverse

/-! Runtime strict positivity tests on unreduced signed rational registers. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def preparePositive (source : ℕ) : List NatAssign.Instruction :=
  [.copy (negativePort source) 30,.copy (positivePort source) 31]

def beforePositive (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (dataValues v) 30 (v source).negative) 31 (v source).positive

def afterPositiveMagnitude (v : ℕ→Parts) (source : ℕ) : ℕ→ℕ :=
  Function.update (beforePositive v source) 34
    (IntegerNormSquare.magnitude (v source).negative (v source).positive)

theorem Parts.value_pos_iff (x : Parts) (hx : x.Valid) : 0<x.value ↔ x.negative<x.positive := by
  have hd : (0:ℚ)<x.denominator := by exact_mod_cast hx
  rw [Parts.value,div_pos_iff_of_pos_right hd,sub_pos]
  exact_mod_cast Iff.rfl

theorem preparePositive_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀ a∈preparePositive source, a.Valid (ids S) := by
  have hp := cell_mem hs (show positivePort source∈cellPorts source by simp [cellPorts])
  have hn := cell_mem hs (show negativePort source∈cellPorts source by simp [cellPorts])
  have h30 := magnitude_subset S (show 30∈RationalMagnitude.ids by decide)
  have h31 := magnitude_subset S (show 31∈RationalMagnitude.ids by decide)
  have hpg := positivePort_ge source
  have hng := negativePort_ge source
  simp [preparePositive,NatAssign.Instruction.Valid,hp,hn,h30,h31]
  omega

theorem preparePositive_values (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values (preparePositive source) (dataValues v)=beforePositive v source := by
  have hp := positivePort_ge source
  have hn := negativePort_ge source
  simp (disch := omega) [preparePositive,beforePositive,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem beforePositive_inputs (v : ℕ→Parts) (source : ℕ) :
    beforePositive v source 30=(v source).negative ∧
    beforePositive v source 31=(v source).positive ∧ beforePositive v source 34=0 := by
  simp [beforePositive,dataValues]

theorem afterPositiveMagnitude_width (S : Finset ℕ) (v : ℕ→Parts) (source : ℕ)
    (hs : source∈S) (B : ℕ) (hw : ∀ i∈S, (v i).Width B) :
    ∀ i∈ids S, (afterPositiveMagnitude v source i).bits.length≤B+1 := by
  intro i hi
  by_cases h34 : i=34
  · subst i
    simp only [afterPositiveMagnitude,Function.update_self]
    exact (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le (hw source hs).2.1 (hw source hs).1) 1)
  · by_cases h31 : i=31
    · subst i
      simpa [afterPositiveMagnitude,beforePositive] using (hw source hs).1.trans (Nat.le_succ B)
    · by_cases h30 : i=30
      · subst i
        simpa [afterPositiveMagnitude,beforePositive] using (hw source hs).2.1.trans (Nat.le_succ B)
      · simpa only [afterPositiveMagnitude,beforePositive,Function.update_of_ne h34,
          Function.update_of_ne h31,Function.update_of_ne h30] using
          (dataValues_width S v B hw i hi).trans (Nat.le_succ B)

theorem clearMagnitude_valid (S : Finset ℕ) : ∀ a∈clearMagnitude, a.Valid (ids S) := by
  have hmem (i : ℕ) (hi : i∈RationalMagnitude.ids) := magnitude_subset S hi
  simp [clearMagnitude,NatAssign.Instruction.Valid,
    hmem 30 (by decide),hmem 31 (by decide),hmem 32 (by decide),hmem 33 (by decide),
    hmem 34 (by decide),hmem 35 (by decide),hmem 36 (by decide)]

theorem clearPositive_values (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values clearMagnitude (afterPositiveMagnitude v source)=dataValues v := by
  ext i
  by_cases hi : i<1000
  · simp (disch := omega) [clearMagnitude,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,afterPositiveMagnitude,beforePositive,
      Function.update_apply,dataValues_small v hi]
  · simp (disch := omega) [clearMagnitude,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,afterPositiveMagnitude,beforePositive]

def positivePrefix (source : ℕ) : Code :=
  .seq (NatAssign.code (preparePositive source)) RationalMagnitude.program

theorem positivePrefix_executes (S : Finset ℕ) (source : ℕ) (hs' : source∈S)
    (v : ℕ→Parts) (B : ℕ) (hw : ∀ i∈S, (v i).Width B) (hv : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (positivePrefix source) cost s t ∧
      cost≤stageCost B+300*(2*B+4) ∧
      NatAssign.Bank (ids S) (afterPositiveMagnitude v source) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val ∧
      t.val.registers 23=decide (0<(v source).value) := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := fixedStage_executes S (preparePositive source)
    (preparePositive_valid S source hs') (by simp [preparePositive]) (dataValues v) B
    (dataValues_width S v B hw)
    (by simp [preparePositive,NatAssign.Instruction.literalWidth]) input tape s hs.1 hs.2
  rw [preparePositive_values] at b0
  obtain ⟨c1,t,e1,h1,b1,z1,f1,sg⟩ := RationalMagnitude.executes (ids S) (magnitude_subset S)
    (ids_ge S) (beforePositive v source) (beforePositive_inputs v source).2.2 input tape s0 b0 z0
  have hb1 : NatAssign.Bank (ids S) (afterPositiveMagnitude v source) t.val := by
    simpa only [afterPositiveMagnitude,(beforePositive_inputs v source).1,(beforePositive_inputs v source).2.1] using b1
  have hc1 : c1≤300*(2*B+4) := by
    rw [(beforePositive_inputs v source).1,(beforePositive_inputs v source).2.1] at h1
    exact h1.trans (Nat.mul_le_mul_left 300 (by
      have hp := (hw source hs').1
      have hn := (hw source hs').2.1
      omega))
  have hsg : t.val.registers 23=decide (0<(v source).value) := by
    simpa only [(beforePositive_inputs v source).1,(beforePositive_inputs v source).2.1,magnitude_sign,
      (v source).value_pos_iff hv] using sg
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 hc1,hb1,z1,?_,hsg⟩
  exact f0.trans (f1.mono (by
    intro i hi
    rcases Finset.mem_union.mp hi with hz | hm
    · exact Finset.mem_union_left _ hz
    · exact Finset.mem_union_right _ (magnitude_subset S hm)))

theorem positiveCleanup_executes (S : Finset ℕ) (source : ℕ) (hs' : source∈S)
    (v : ℕ→Parts) (B : ℕ) (hw : ∀ i∈S, (v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank (ids S) (afterPositiveMagnitude v source) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code clearMagnitude) cost s t ∧
      cost≤stageCost (B+1) ∧ Ready S v t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hz',hf⟩ := fixedStage_executes S clearMagnitude (clearMagnitude_valid S)
    (by simp [clearMagnitude]) (afterPositiveMagnitude v source) (B+1)
    (afterPositiveMagnitude_width S v source hs' B hw)
    (by simp [clearMagnitude,NatAssign.Instruction.literalWidth]) input tape s hs hz
  rw [clearPositive_values] at hb
  exact ⟨cost,t,he,hc,⟨hb,hz'⟩,hf⟩

#print axioms positivePrefix_executes
#print axioms positiveCleanup_executes

end Maxwell.Continuum.RationalDataflow
