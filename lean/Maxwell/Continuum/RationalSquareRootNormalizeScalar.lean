import Maxwell.Continuum.RationalSquareRootStored
import Maxwell.Continuum.RationalSquareRootInverseStore
import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Cost.BankArray.Unique

/-! Execute a stored nonnegative rational norm, form its reciprocal, and
restore the rational register bank. All old square-root words are charged. -/
namespace Maxwell.Continuum.Calibration.RationalRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def normalizeScalarCode (source : ℕ) : Code := .seq (Stored.code source) (inverseStoreCode source)
def normalizeScalarWidth (N W : ℕ) : ℕ := outputWidth N (W+1)
def normalizeScalarCost (source N W : ℕ) : ℕ :=
  Stored.costBound source N W+100*(normalizeScalarWidth N W+1)
def normalizeScalarChanged (source : ℕ) : Finset ℕ := Stored.changed∪cellPorts source

theorem stored_parts_eq (S : Finset ℕ) (source : ℕ) (hs : source∈S)
    (n : ℕ→ℕ) (v : ℕ→Parts) (s : Store)
    (bank : NatAssign.Bank (Stored.ids source) n s.val) (raw : Ready S v s) :
    Stored.sourceParts source n=v source := by
  have agree (i : ℕ) (hi : i∈cellPorts source) : n i=dataValues v i := by
    have eq:=BankArray.word_unique
      (bank i (Finset.mem_union_left _ (Finset.mem_union_right _ hi))) (raw.1 i (cell_mem hs hi))
    simpa only [addressValue_bits] using congrArg addressValue eq
  have hp : n (positivePort source)=(v source).positive := by
    simpa only [dataValues_positive] using agree (positivePort source) (by simp [cellPorts])
  have hm : n (negativePort source)=(v source).negative := by
    simpa only [dataValues_negative] using agree (negativePort source) (by simp [cellPorts])
  have hd : n (denominatorPort source)=(v source).denominator := by
    simpa only [dataValues_denominator] using agree (denominatorPort source) (by simp [cellPorts])
  simp only [Stored.sourceParts,hp,hm,hd]

theorem normalizeScalar_executes (S : Finset ℕ) (source : ℕ) (hs : source∈S)
    (n : ℕ→ℕ) (v : ℕ→Parts) (W : ℕ)
    (width : ∀i∈Stored.ids source,(n i).bits.length≤W) (rawWidth : WidthBank S W v)
    (good : Good S v) (nonnegative : 0≤(v source).value)
    (positive : 0<sqrtRationalCenter (v source).value (n 700))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (Stored.ids source) n s.val) (raw : Ready S v s) :
    ∃cost t x,Executes input tape (normalizeScalarCode source) cost s t ∧
      cost≤normalizeScalarCost source (n 700) W ∧
      Ready S (Function.update v source x) t ∧ Good S (Function.update v source x) ∧
      WidthBank S (normalizeScalarWidth (n 700) W) (Function.update v source x) ∧
      x.value=(sqrtRationalCenter (v source).value (n 700))⁻¹ ∧
      (∀i∈({4,220,221,222,223}:Finset ℕ),Blank t.val i) ∧
      BinaryPrecision.Frame (normalizeScalarChanged source) s.val t.val := by
  have stored:=stored_parts_eq S source hs n v s bank raw
  obtain ⟨c0,u,num,den,e0,h0,wn,wd,denpos,value,rootBank,z0,f0⟩ := Stored.executes source n W width
    (stored.symm ▸ good source hs) (stored.symm ▸ nonnegative) input tape s bank raw.2
  rw [stored] at value rootBank
  have precision : (n 700).bits.length≤W := width 700 (by simp [Stored.ids])
  have mag := (IntegerNormSquare.magnitude_bits_length_le (v source).positive (v source).negative).trans
    (Nat.add_le_add_right (max_le (rawWidth source hs).1 (rawWidth source hs).2.1) 1)
  have rootWidth (i : ℕ) :
      (Raw.outputValues (IntegerNormSquare.magnitude (v source).positive (v source).negative)
        (v source).denominator (n 700) i).bits.length≤normalizeScalarWidth (n 700) W :=
    Raw.output_width _ _ _ (W+1) mag ((rawWidth source hs).2.2.trans (by omega))
      (precision.trans (by omega)) i
  have numWidth : num.bits.length≤normalizeScalarWidth (n 700) W := by
    rw [BankArray.word_unique wn (rootBank 32 (by decide))]
    exact rootWidth 32
  have denWidth : den.bits.length≤normalizeScalarWidth (n 700) W := by
    rw [BankArray.word_unique wd (rootBank 548 (by decide))]
    exact rootWidth 548
  have larger : W≤normalizeScalarWidth (n 700) W := by unfold normalizeScalarWidth outputWidth; omega
  have cells : Cells S v u.val := by
    apply (Cells.of_ready raw).transfer
    intro i hi
    apply f0.tapes
    simp only [Stored.changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    exact not_or_intro (by omega) (fun h=>by have := Stored.raw_ids_le i h;omega)
  have temporary : ∀i∈temporaryPorts,Blank u.val i := by
    intro i hi
    have out : i∉Stored.changed := by
      simp only [temporaryPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have low : i<1000 := by
      simp only [temporaryPorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    apply RationalAccumulator.blank_of_eq (f0.tapes i out)
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [dataValues_small v low] using raw.1 i
      (Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have comparison : WordCleanup.Bounded comparisonWords (normalizeScalarWidth (n 700) W) u.val := by
    intro i hi
    have member : i∈Raw.ids := by
      simp only [comparisonWords,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact ⟨_,rootWidth i,rootBank i member⟩
  obtain ⟨c1,t,e1,h1,rt,f1⟩ := inverseStore_executes S source hs v num den
    (normalizeScalarWidth (n 700) W) ((rawWidth source hs).mono larger) numWidth denWidth
    input tape u cells wn wd comparison temporary z0
  have numpos : 0<num := by
    have ratio : 0<(num:ℚ)/den := by rw [value];exact positive
    by_contra h
    have eq : num=0 := by omega
    simp only [eq,Nat.cast_zero,zero_div] at ratio
    exact (lt_irrefl 0 ratio)
  have newWidth : (inverseParts num den).Width (normalizeScalarWidth (n 700) W) :=
    ⟨denWidth,Nat.zero_le _,numWidth⟩
  refine ⟨c0+c1,t,inverseParts num den,e0.seq e1,Nat.add_le_add h0 h1,rt,
    good.update source numpos,(rawWidth.mono larger).update source newWidth,?_,?_,
    (f0.mono Finset.subset_union_left).trans (f1.mono ?_)⟩
  · rw [inverseParts_value,value]
  · intro i hi
    have zero : Raw.outputValues (IntegerNormSquare.magnitude (v source).positive (v source).negative)
        (v source).denominator (n 700) i=0 := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;>
        simp [Raw.outputValues,RationalCanonicalBank.outputValues,
          RationalCanonicalBank.inputValues,show 4∉RationalRoot.ids by decide,
          show 220∉RationalRoot.ids by decide,show 221∉RationalRoot.ids by decide,
          show 222∉RationalRoot.ids by decide,show 223∉RationalRoot.ids by decide]
    have member : i∈Raw.ids := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
    have old := rootBank i member
    rw [zero,RationalAccumulator.zero_word_iff_blank] at old
    apply RationalAccumulator.blank_of_eq (f1.tapes i _) old
    have hp:=positivePort_ge source
    have hm:=negativePort_ge source
    have hd:=denominatorPort_ge source
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [inverseStoreChanged,cellPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with cell|mag
    · exact Finset.mem_union_right _ cell
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((by decide : RationalMagnitude.ids⊆Raw.ids) mag))

#print axioms normalizeScalar_executes
end Maxwell.Continuum.Calibration.RationalRoot
