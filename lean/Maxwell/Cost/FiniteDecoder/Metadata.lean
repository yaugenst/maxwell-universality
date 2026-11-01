import Maxwell.Cost.DecoderParser.Target
import Maxwell.Cost.DecoderParser.Plan
import Maxwell.Cost.DecoderParser.Bounds

/-! A decoder-only finite wire format and its actual metadata parser. It reuses
the shared rational-row machine without wrapping a continuum field in a
discrete Maxwell target. Coordinates belong to the separately emitted tests. -/

namespace Maxwell.Cost.FiniteDecoder
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

abbrev headerShape : Shape := .pair .nat (.pair .nat (.pair .nat .nat))
abbrev descriptionShape : Shape := .pair headerShape (.list rowShape)

variable {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)

def headerData : Payload headerShape :=
  (n,D.format.integerBits,D.format.fractionalBits,D.sampleCount)

def rowData : List (Payload rowShape) := (List.finRange n).map fun i =>
  (rationalPayload (D.offset i),((D.support i).sort).map fun j =>
    (j.val,rationalPayload (D.weight i j)))

def descriptionData : Payload descriptionShape := (headerData D,rowData D)
def beforeRows : List Bool := wire headerShape (headerData D)
def description : List Bool := wire descriptionShape (descriptionData D)

theorem rowData_length : (rowData D).length=n := by simp [rowData]

theorem description_parts : description D=beforeRows D++Codec.list (wire rowShape) (rowData D) := rfl

theorem description_rows : description D=beforeRows D++(Codec.nat n++(rows D).flatMap rowWire) := by
  rw [description_parts]
  simp [Codec.list,rowData,rows,rowTerms,wire,rowWire,termWire,rationalPayload,Codec.rat,Codec.int,
    List.flatMap_map,List.append_assoc]

def retainedCode : Code := .seq (readNat 40 18) (.seq (readNat 41 18)
  (.seq (readNat 42 18) (.seq (readNat 43 18) (retainedList 44 0 (parser rowShape 1)))))

def retainedPrice : ℕ := (60*n.bits.length+57)+
  ((60*D.format.integerBits.bits.length+57)+((60*D.format.fractionalBits.bits.length+57)+
    ((60*D.sampleCount.bits.length+57)+retainedListPrice (price rowShape) (rowData D))))

structure Metadata (s : BitRAMState) : Prop where
  dimension : s.tapes 40=BitTape.ofList n.bits
  integerBits : s.tapes 41=BitTape.ofList D.format.integerBits.bits
  fractionalBits : s.tapes 42=BitTape.ofList D.format.fractionalBits.bits
  sampleCount : s.tapes 43=BitTape.ofList D.sampleCount.bits
  rowCount : s.tapes 44=BitTape.ofList n.bits

theorem retained_from (preceding suffix : List Bool) (randomTape : ℕ→Bool)
    (s0 : Store) (hh : s0.val.inputHead=preceding.length)
    (hz : ∀ i, s0.val.tapes i=BitTape.blank) :
    ∃ (cost : ℕ) (t : Store), Executes (preceding++(description D++suffix)) randomTape retainedCode cost
      s0 t ∧ cost≤retainedPrice D ∧
      t.val.inputHead=(preceding++description D).length ∧ t.val.tapes 18=BitTape.atEnd (description D) ∧
      Metadata D t.val ∧ Ready 0 t.val ∧
      Frame {18,40,41,42,43,44} s0.val t.val := by
  let b1 := Codec.nat n
  let b2 := Codec.nat D.format.integerBits
  let b3 := Codec.nat D.format.fractionalBits
  let b4 := Codec.nat D.sampleCount
  let b5 := Codec.list (wire rowShape) (rowData D)
  have r0 : Ready 0 s0.val := by simp [Ready,hz]
  have l0 : s0.val.tapes 18=BitTape.atEnd [] := by
    simp [hz,BitTape.atEnd_nil]
  obtain ⟨s1,e1,h1,l1,m1,r1,f1⟩ := retainedNat_steps 40 (by decide) n preceding
    (b2++(b3++(b4++(b5++suffix)))) [] randomTape s0 hh r0 (hz 40) l0
  have z41 : s1.val.tapes 41=BitTape.blank := (f1.tapes 41 (by decide)).trans (hz 41)
  obtain ⟨s2,e2,h2,l2,m2,r2,f2⟩ := retainedNat_steps 41 (by decide)
    D.format.integerBits (preceding++b1) (b3++(b4++(b5++suffix))) b1 randomTape s1
    (by simpa [hh,b1] using h1) r1 z41 (by simpa using l1)
  have z42 : s2.val.tapes 42=BitTape.blank :=
    (f2.tapes 42 (by decide)).trans ((f1.tapes 42 (by decide)).trans (hz 42))
  obtain ⟨s3,e3,h3,l3,m3,r3,f3⟩ := retainedNat_steps 42 (by decide)
    D.format.fractionalBits (preceding++b1++b2) (b4++(b5++suffix)) (b1++b2) randomTape s2
    (by simp [h2,h1,hh,b1,b2,add_assoc]) r2 z42 l2
  have z43 : s3.val.tapes 43=BitTape.blank :=
    (f3.tapes 43 (by decide)).trans ((f2.tapes 43 (by decide)).trans
      ((f1.tapes 43 (by decide)).trans (hz 43)))
  obtain ⟨s4,e4,h4,l4,m4,r4,f4⟩ := retainedNat_steps 43 (by decide) D.sampleCount
    (preceding++b1++b2++b3) (b5++suffix) (b1++b2++b3) randomTape s3
    (by simp [h3,h2,h1,hh,b1,b2,b3,add_assoc]) r3 z43 l3
  have z44 : s4.val.tapes 44=BitTape.blank :=
    (f4.tapes 44 (by decide)).trans ((f3.tapes 44 (by decide)).trans
      ((f2.tapes 44 (by decide)).trans ((f1.tapes 44 (by decide)).trans (hz 44))))
  obtain ⟨a5,s5,e5,c5,h5,l5,m5,f5⟩ := retainedList_steps 44 0 (by decide)
    rowShape (parser rowShape 1) (price rowShape) (parser_correct rowShape 1) (by decide)
    (rowData D) (preceding++b1++b2++b3++b4) suffix (b1++b2++b3++b4) randomTape s4
    (by simp [h4,h3,h2,h1,hh,b1,b2,b3,b4,add_assoc]) r4 z44 l4
  have r5 := r4.retained f5 (by decide) (by decide) (by decide)
  have input_eq : preceding++(description D++suffix)=preceding++(b1++(b2++(b3++(b4++(b5++suffix))))) := by
    simp only [description,descriptionData,headerData,wire,b1,b2,b3,b4,b5,List.append_assoc]
  simp only [List.append_assoc] at e1 e2 e3 e4 e5
  rw [← input_eq] at e1 e2 e3 e4 e5
  refine ⟨_,s5,e1.seq (e2.seq (e3.seq (e4.seq e5))),?_,?_,?_,?_,r5,?_⟩
  · dsimp [retainedPrice]
    omega
  · change s5.val.inputHead=(preceding++((b1++(b2++(b3++b4)))++b5)).length
    simp only [List.length_append,Nat.cast_add]
    dsimp only [b1,b2,b3,b4,b5]
    omega
  · simpa only [description,descriptionData,headerData,wire,b1,b2,b3,b4,b5,List.append_assoc] using l5
  · constructor
    · exact (f5.tapes 40 (by decide)).trans ((f4.tapes 40 (by decide)).trans
        ((f3.tapes 40 (by decide)).trans ((f2.tapes 40 (by decide)).trans m1)))
    · exact (f5.tapes 41 (by decide)).trans ((f4.tapes 41 (by decide)).trans
        ((f3.tapes 41 (by decide)).trans m2))
    · exact (f5.tapes 42 (by decide)).trans ((f4.tapes 42 (by decide)).trans m3)
    · exact (f5.tapes 43 (by decide)).trans m4
    · simpa [rowData] using m5
  · have f1' := f1.mono (show {18,40}⊆({18,40,41,42,43,44} : Finset ℕ) by decide)
    have f2' := f2.mono (show {18,41}⊆({18,40,41,42,43,44} : Finset ℕ) by decide)
    have f3' := f3.mono (show {18,42}⊆({18,40,41,42,43,44} : Finset ℕ) by decide)
    have f4' := f4.mono (show {18,43}⊆({18,40,41,42,43,44} : Finset ℕ) by decide)
    have f5' := f5.mono (show {18,44}⊆({18,40,41,42,43,44} : Finset ℕ) by decide)
    exact f1'.trans (f2'.trans (f3'.trans (f4'.trans f5')))

theorem retained_steps (suffix : List Bool) (randomTape : ℕ→Bool) :
    ∃ (cost : ℕ) (t : Store), Executes (description D++suffix) randomTape retainedCode cost
      (Store.ofState BitRAMState.initial) t ∧ cost≤retainedPrice D ∧
      t.val.inputHead=(description D).length ∧ t.val.tapes 18=BitTape.atEnd (description D) ∧
      Metadata D t.val ∧ Ready 0 t.val ∧
      Frame {18,40,41,42,43,44} BitRAMState.initial t.val := by
  obtain ⟨cost,t,he,hc,hh,ha,hm,hr,hf⟩ :=
    retained_from D [] suffix randomTape (Store.ofState BitRAMState.initial) rfl (fun _ => rfl)
  exact ⟨cost,t,by simpa only [List.nil_append] using he,hc,
    by simpa only [List.nil_append] using hh,ha,hm,hr,
    ⟨hf.address,hf.memory,hf.randomCursor,hf.output,hf.tapes⟩⟩

theorem retainedPrice_le : retainedPrice D≤2*price descriptionShape (descriptionData D) := by
  simp only [retainedPrice,descriptionData,headerData,price,retainedListPrice,listPrice]
  omega

theorem retainedPrice_bound (B : ℕ) (hB : WidthBound descriptionShape (descriptionData D) B) :
    retainedPrice D≤2*shapeConstant descriptionShape*(description D).length*(B+1) := by
  have h := price_le descriptionShape (descriptionData D) B hB
  exact (retainedPrice_le D).trans (by
    simpa only [description,Nat.mul_assoc] using Nat.mul_le_mul_left 2 h)

#print axioms retained_steps
#print axioms retainedPrice_bound

end Maxwell.Cost.FiniteDecoder
