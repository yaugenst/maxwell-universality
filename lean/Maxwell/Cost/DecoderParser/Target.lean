import Maxwell.Cost.DecoderParser.Metadata

namespace Maxwell.Cost.DecoderParser
open Structured

abbrev physicalPrefixShape : Shape := .pair .nat (.pair .nat (.pair .nat
  (.pair (.list rationalShape) (.pair (.list rationalShape) rationalShape))))

def physicalPrefix {n : ℕ} (I : Target.Instance n) : Payload physicalPrefixShape :=
  (I.box.nx,I.box.ny,I.box.nz,
    (Codec.cells I.box).map (fun c => rationalPayload (I.material.value c)),
    (Codec.edges I.box).map (fun e => rationalPayload (I.source e)),rationalPayload I.tolerance)

def coordinatePayload {B : Target.Box} {n : ℕ} (D : Target.WeightedDecoder B.Edge n) :
    List (Payload edgeShape) := (List.ofFn D.coordinate).map edgePayload

def rowPayload {B : Target.Box} {n : ℕ} (D : Target.WeightedDecoder B.Edge n) :
    List (Payload rowShape) := (List.finRange n).map fun i =>
      (rationalPayload (D.offset i), ((D.support i).sort).map fun j =>
        (j.val,rationalPayload (D.weight i j)))

theorem target_parts {n : ℕ} (I : Target.Instance n) :
    Codec.target I = Codec.nat n ++ (wire physicalPrefixShape (physicalPrefix I) ++
      (Codec.nat I.decoder.format.integerBits ++ (Codec.nat I.decoder.format.fractionalBits ++
        (Codec.list (wire edgeShape) (coordinatePayload I.decoder) ++
          Codec.list (wire rowShape) (rowPayload I.decoder))))) := by
  rw [←target_wire]
  simp [wire,targetPayload,physicalPrefix,decoderPayload,coordinatePayload,rowPayload,List.append_assoc]

/-- The fixed parser preserves the five scalar metadata words needed by
message loading and the single subsequent row-evaluation pass. -/
def retainedTargetCode : Code := .seq (readNat 40 18)
  (.seq (parser physicalPrefixShape 0) (.seq (readNat 41 18) (.seq (readNat 42 18)
    (.seq (retainedList 43 0 (parser edgeShape 1))
      (retainedList 44 0 (parser rowShape 1))))))

def retainedTargetPrice {n : ℕ} (I : Target.Instance n) : ℕ :=
  (60*n.bits.length+57) + (price physicalPrefixShape (physicalPrefix I) +
    ((60*I.decoder.format.integerBits.bits.length+57) +
      ((60*I.decoder.format.fractionalBits.bits.length+57) +
        (retainedListPrice (price edgeShape) (coordinatePayload I.decoder) +
          retainedListPrice (price rowShape) (rowPayload I.decoder)))))

structure DecoderMetadata {n : ℕ} (I : Target.Instance n) (s : BitRAMState) : Prop where
  dimension : s.tapes 40 = BitTape.ofList n.bits
  integerBits : s.tapes 41 = BitTape.ofList I.decoder.format.integerBits.bits
  fractionalBits : s.tapes 42 = BitTape.ofList I.decoder.format.fractionalBits.bits
  sampleCount : s.tapes 43 = BitTape.ofList I.decoder.sampleCount.bits
  rowCount : s.tapes 44 = BitTape.ofList n.bits

theorem retainedTarget_steps {n : ℕ} (I : Target.Instance n) (suffix : List Bool)
    (randomTape : ℕ → Bool) :
    ∃ (cost : ℕ) (t : Store),
      Executes (Codec.target I ++ suffix) randomTape retainedTargetCode cost
        (Store.ofState BitRAMState.initial) t ∧ cost ≤ retainedTargetPrice I ∧
      t.val.inputHead = (Codec.target I).length ∧
      t.val.tapes 18 = BitTape.atEnd (Codec.target I) ∧ DecoderMetadata I t.val ∧
      Ready 0 t.val ∧ Frame {18,40,41,42,43,44} BitRAMState.initial t.val := by
  let b1 := Codec.nat n
  let b2 := wire physicalPrefixShape (physicalPrefix I)
  let b3 := Codec.nat I.decoder.format.integerBits
  let b4 := Codec.nat I.decoder.format.fractionalBits
  let b5 := Codec.list (wire edgeShape) (coordinatePayload I.decoder)
  let b6 := Codec.list (wire rowShape) (rowPayload I.decoder)
  let s0 := Store.ofState BitRAMState.initial
  have r0 : Ready 0 s0.val := by simp [s0,Store.ofState,BitRAMState.initial,Ready]
  have l0 : s0.val.tapes 18 = BitTape.atEnd [] := by
    simp [s0,Store.ofState,BitRAMState.initial,BitTape.atEnd_nil]
  obtain ⟨s1,e1,h1,l1,m1,r1,f1⟩ := retainedNat_steps 40 (by decide) n []
    (b2++(b3++(b4++(b5++(b6++suffix))))) [] randomTape s0 rfl r0 rfl l0
  obtain ⟨a2,s2,e2,c2,h2,l2,f2⟩ := parser_correct physicalPrefixShape 0 (by decide) (physicalPrefix I)
    b1 (b3++(b4++(b5++(b6++suffix)))) b1 randomTape s1
    (by simpa [s0,Store.ofState,BitRAMState.initial,b1] using h1) r1 (by simpa using l1)
  have r2 := r1.frame f2
  have z41 : s2.val.tapes 41 = BitTape.blank :=
    (f2.tapes 41 (by decide)).trans ((f1.tapes 41 (by decide)).trans rfl)
  obtain ⟨s3,e3,h3,l3,m3,r3,f3⟩ := retainedNat_steps 41 (by decide)
    I.decoder.format.integerBits (b1++b2) (b4++(b5++(b6++suffix))) (b1++b2)
    randomTape s2 (by simp [h2,h1,s0,Store.ofState,BitRAMState.initial,b1,b2]) r2 z41 l2
  have z42 : s3.val.tapes 42 = BitTape.blank :=
    (f3.tapes 42 (by decide)).trans ((f2.tapes 42 (by decide)).trans
      ((f1.tapes 42 (by decide)).trans rfl))
  obtain ⟨s4,e4,h4,l4,m4,r4,f4⟩ := retainedNat_steps 42 (by decide)
    I.decoder.format.fractionalBits (b1++b2++b3) (b5++(b6++suffix)) (b1++b2++b3)
    randomTape s3 (by simp [h3,h2,h1,s0,Store.ofState,BitRAMState.initial,b1,b2,b3,add_assoc]) r3 z42 l3
  have z43 : s4.val.tapes 43 = BitTape.blank :=
    (f4.tapes 43 (by decide)).trans ((f3.tapes 43 (by decide)).trans
      ((f2.tapes 43 (by decide)).trans ((f1.tapes 43 (by decide)).trans rfl)))
  obtain ⟨a5,s5,e5,c5,h5,l5,m5,f5⟩ := retainedList_steps 43 0 (by decide)
    edgeShape (parser edgeShape 1) (price edgeShape) (parser_correct edgeShape 1) (by decide)
    (coordinatePayload I.decoder) (b1++b2++b3++b4) (b6++suffix) (b1++b2++b3++b4)
    randomTape s4 (by simp [h4,h3,h2,h1,s0,Store.ofState,BitRAMState.initial,b1,b2,b3,b4,add_assoc])
    r4 z43 l4
  have r5 := r4.retained f5 (by decide) (by decide) (by decide)
  have z44 : s5.val.tapes 44 = BitTape.blank :=
    (f5.tapes 44 (by decide)).trans ((f4.tapes 44 (by decide)).trans
      ((f3.tapes 44 (by decide)).trans ((f2.tapes 44 (by decide)).trans
        ((f1.tapes 44 (by decide)).trans rfl))))
  obtain ⟨a6,s6,e6,c6,h6,l6,m6,f6⟩ := retainedList_steps 44 0 (by decide)
    rowShape (parser rowShape 1) (price rowShape) (parser_correct rowShape 1) (by decide)
    (rowPayload I.decoder) (b1++b2++b3++b4++b5) suffix (b1++b2++b3++b4++b5)
    randomTape s5
    (by simp [h5,h4,h3,h2,h1,s0,Store.ofState,BitRAMState.initial,b1,b2,b3,b4,b5,add_assoc])
    r5 z44 l5
  have r6 := r5.retained f6 (by decide) (by decide) (by decide)
  have input_eq : Codec.target I ++ suffix = b1++(b2++(b3++(b4++(b5++(b6++suffix))))) := by
    simp [target_parts,b1,b2,b3,b4,b5,b6,List.append_assoc]
  simp only [List.nil_append,List.append_assoc] at e1 e2 e3 e4 e5 e6
  rw [←input_eq] at e1 e2 e3 e4 e5 e6
  refine ⟨_,s6,e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6)))),?_,?_,?_,?_,r6,?_⟩
  · dsimp [retainedTargetPrice];omega
  · rw [target_parts]
    simp only [List.length_append,Nat.cast_add]
    have hz : s0.val.inputHead=0 := rfl
    omega
  · simpa [target_parts,b1,b2,b3,b4,b5,b6,List.append_assoc] using l6
  · constructor
    · exact (f6.tapes 40 (by decide)).trans ((f5.tapes 40 (by decide)).trans ((f4.tapes 40 (by decide)).trans ((f3.tapes 40 (by decide)).trans ((f2.tapes 40 (by decide)).trans (m1)))))
    · exact (f6.tapes 41 (by decide)).trans ((f5.tapes 41 (by decide)).trans ((f4.tapes 41 (by decide)).trans (m3)))
    · exact (f6.tapes 42 (by decide)).trans ((f5.tapes 42 (by decide)).trans (m4))
    · simpa [coordinatePayload,rowPayload] using (f6.tapes 43 (by decide)).trans (m5)
    · simpa [coordinatePayload,rowPayload] using m6
  · have f1' := f1.mono (show {18,40} ⊆ ({18,40,41,42,43,44}:Finset ℕ) by decide)
    have f2' := f2.mono (show {18} ⊆ ({18,40,41,42,43,44}:Finset ℕ) by decide)
    have f3' := f3.mono (show {18,41} ⊆ ({18,40,41,42,43,44}:Finset ℕ) by decide)
    have f4' := f4.mono (show {18,42} ⊆ ({18,40,41,42,43,44}:Finset ℕ) by decide)
    have f5' := f5.mono (show {18,43} ⊆ ({18,40,41,42,43,44}:Finset ℕ) by decide)
    have f6' := f6.mono (show {18,44} ⊆ ({18,40,41,42,43,44}:Finset ℕ) by decide)
    exact f1'.trans (f2'.trans (f3'.trans (f4'.trans (f5'.trans f6'))))

end Maxwell.Cost.DecoderParser
