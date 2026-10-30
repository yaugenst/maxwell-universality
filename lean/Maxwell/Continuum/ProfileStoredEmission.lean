import Maxwell.Continuum.ProfileEncodedHandoff
import Maxwell.Continuum.StoredProfileEncoding
import Maxwell.Continuum.RationalDataflowBankPartition

/-! The actual computed and corrected profile table is serialized without
precomputed numerator words. Runtime descriptors and counts are copied by
charged code, then the temporary serializer words are cleared. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] profileDegree profileWorkBits encodedCoefficient

def emitTableCode : Code := .seq headerSwapCode (.seq (WordReplace.code 663 726)
  (.seq (WordReplace.code 661 201) (.seq StoredDyadic.arrayCode (WordReplace.code 201 726))))
def emitTableCost (N W : ℕ) : ℕ :=
  2^154*(profileDegree N+1)*(profileWorkBits N+encodedTableWidth (profileDegree N) W+6)^2

private theorem clean_copy {k : ℕ} {s t : Store} (h : DyadicFloor.Clean s.val)
    (hk : k=726 ∨ k=201) (f : WordReplace.Frame k s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 4 (by omega)) h.1,?_⟩
  intro i hi
  have hne : i≠k := by
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i hne) (h.2 i hi)

theorem EncodedTableResult.emit_executes {N W : ℕ} {a : Table (profileDegree N)} {s : Store}
    (r : EncodedTableResult N W a s)
    (hm : a.MetadataWidth (encodedTableWidth (profileDegree N) W))
    (hn : (profileDegree N).bits.length≤encodedTableWidth (profileDegree N) W)
    (hp : (profileWorkBits N).bits.length≤encodedTableWidth (profileDegree N) W)
    (input : List Bool) (tape : ℕ→Bool)
    (h726 : Blank s.val 726) (h727 : Blank s.val 727) (h728 : Blank s.val 728) :
    ∃cost t values,Executes input tape emitTableCode cost s t ∧ cost≤emitTableCost N W ∧
      Ready StoredInteger.slots values t ∧
      WidthBank StoredInteger.slots (StoredDyadic.registerWidth (profileWorkBits N)
        (encodedTableWidth (profileDegree N) W)) values ∧ r.table.Ready t ∧
      t.val.output=(profileBits N).reverse++s.val.output ∧
      Word t.val 144 (2^profileWorkBits N) ∧ DyadicFloor.Clean t.val ∧
      (∀i∈({201,726,727,728}:Finset ℕ),Blank t.val i) := by
  let D := profileDegree N
  let P := profileWorkBits N
  let B := encodedTableWidth D W
  obtain ⟨c0,s0,e0,hc0,r0,a0,_,_,count0,f0⟩ := r.input_executes hm input tape
  have ready0 : Ready StoredInteger.slots r.values s0 := r0.rational.restrict (by decide)
  have precision0 := RationalAccumulator.word_of_eq (f0.tapes 663 (by decide)) r.precisionWord
  have degree0 := RationalAccumulator.word_of_eq (f0.tapes 661 (by decide)) r.degreeWord
  have power0 := RationalAccumulator.word_of_eq (f0.tapes 144 (by decide)) r.powerWord
  have floor0 := floorClean_headerSwap r.floorClean f0
  have blank0 := RationalAccumulator.blank_of_eq (f0.tapes 726 (by decide)) h726
  obtain ⟨s1,e1,precision1,f1⟩ := WordReplace.executes 663 726 (by decide) input tape P.bits [] s0
    precision0 ((RationalAccumulator.zero_word_iff_blank _ _).mpr blank0)
  have ready1 := ready0.wordReplace_frame (outside_workspace _ 726 (by decide)) f1
  have a1 := a0.memory_frame f1.2.2.1 (fun i hi=>f1.2.2.2.2.2.1 i (by
    have hd : (726:ℕ)∉tablePorts := by decide
    intro he;subst i;exact hd hi)) ready1.2
  have degree1 := RationalAccumulator.word_of_eq (f1.2.2.2.2.2.1 661 (by decide)) degree0
  have count1 := BankArray.word_of_eq (f1.2.2.2.2.2.1 201 (by decide)) count0
  obtain ⟨s2,e2,count2,f2⟩ := WordReplace.executes 661 201 (by decide) input tape D.bits r.countWord s1 degree1 count1
  have ready2 := ready1.wordReplace_frame (outside_workspace _ 201 (by decide)) f2
  have a2 := a1.copy_frame (Or.inl rfl) f2
  have precision2 := RationalAccumulator.word_of_eq (f2.2.2.2.2.2.1 726 (by decide)) precision1
  have power2 := RationalAccumulator.word_of_eq ((f2.2.2.2.2.2.1 144 (by decide)).trans
    (f1.2.2.2.2.2.1 144 (by decide))) power0
  have clean2 := clean_copy (clean_copy floor0 (Or.inl rfl) f1) (Or.inr rfl) f2
  have blank2 (i : ℕ) (hi : i=727 ∨ i=728) (hb : Blank s.val i) : Blank s2.val i :=
    RationalAccumulator.blank_of_eq ((f2.2.2.2.2.2.1 i (by omega)).trans
      ((f1.2.2.2.2.2.1 i (by omega)).trans (f0.tapes i (by
        simp only [headerSlots,Finset.mem_insert,Finset.mem_singleton];omega)))) hb
  have width2 : WidthBank StoredInteger.slots (StoredDyadic.registerWidth P B) r.values := by
    intro i hi
    exact (r.width i (by
      have he : i=0 := by simpa only [StoredInteger.slots,Finset.mem_singleton] using hi
      subst i;decide)).mono (by
        change B≤StoredDyadic.registerWidth P B
        unfold StoredDyadic.registerWidth
        omega)
  obtain ⟨c3,s3,values,e3,hc3,ready3,width3,a3,out3,precision3,power3,clean3,blanks3⟩ :=
    StoredDyadic.array_executes r.table (encodedCoefficient N)
      (fun i=>⟨(r.correct i).1,(r.correct i).2.2⟩) B (tableMetadata_width r.metadata hm) hn hp
      r.values width2 input tape s2 ready2 a2 count2 precision2 power2 clean2
      (blank2 727 (Or.inl rfl) h727) (blank2 728 (Or.inr rfl) h728)
  obtain ⟨t,e4,zero4,f4⟩ := WordReplace.executes 201 726 (by decide) input tape [] P.bits s3
    ((RationalAccumulator.zero_word_iff_blank _ _).mpr (blanks3 201 (by decide))) precision3
  have ready4 := ready3.wordReplace_frame (outside_workspace _ 726 (by decide)) f4
  have a4 := a3.memory_frame f4.2.2.1 (fun i hi=>f4.2.2.2.2.2.1 i (by
    have hd : (726:ℕ)∉tablePorts := by decide
    intro he;subst i;exact hd hi)) ready4.2
  refine ⟨c0+((6*([].length)+15*P.bits.length+21)+
    ((6*r.countWord.length+15*D.bits.length+21)+(c3+(6*P.bits.length+15*([].length)+21)))),
    t,values,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,ready4,width3,a4,?_,
    RationalAccumulator.word_of_eq (f4.2.2.2.2.2.1 144 (by decide)) power3,
    clean_copy clean3 (Or.inl rfl) f4,?_⟩
  · rw [r.countLength]
    change c0≤256*(B+1) at hc0
    change D.bits.length≤B at hn
    change P.bits.length≤B at hp
    change c3≤2^152*(D+1)*(P+B+6)^2 at hc3
    change _≤2^154*(D+1)*(P+B+6)^2
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add]
    have hlin : B+1≤(P+B+6)^2 :=
      (show B+1≤P+B+6 by omega).trans (Nat.le_self_pow (by decide) _)
    have hprod : (P+B+6)^2≤(D+1)*(P+B+6)^2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith only [hc0,hc3,hn,hp,hlin,hprod]
  · rw [f4.2.2.2.2.1,out3,profile_arrayBits,f2.2.2.2.2.1,f1.2.2.2.2.1,f0.output]
  · intro i hi
    by_cases he : i=726
    · subst i;exact (RationalAccumulator.zero_word_iff_blank _ _).mp zero4
    · exact RationalAccumulator.blank_of_eq (f4.2.2.2.2.2.1 i he) (blanks3 i (by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢;tauto))

#print axioms EncodedTableResult.emit_executes
end Maxwell.Continuum.Profile.Runtime
