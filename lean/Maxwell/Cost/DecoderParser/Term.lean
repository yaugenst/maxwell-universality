import Maxwell.Cost.DecoderParser.EvaluatorState

namespace Maxwell.Cost.DecoderParser
open Structured
open RationalAccumulator (Bank Scratch Word Blank bankValue)
set_option maxRecDepth 4096

def termCode : Code := .seq (readNatural 45)
  (.seq readRational (.seq DecoderFetch.code accumulateCode))

def termPrice (F : Target.FixedPointFormat) (j : ℕ) (q : ℚ) (sample : List Bool) (A : ℕ) : ℕ :=
  21*j.bits.length+16+(17*(q.num.natAbs.bits.length+q.den.bits.length)+23+
    (DecoderFetch.costCap F.width.bits j.bits (2^(F.integerBits+F.fractionalBits)).bits+
      20000*(A+termWidth F q sample+2)^2))

/-- The finite term program parses its index and weight, reads the exact
message from binary memory, and performs the exact weighted rational update. -/
theorem term_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) (w : D.Messages)
    (j : Fin D.sampleCount) (q : ℚ) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (v : ℕ → ℕ) (A : ℕ) (hd : 0 < v 32) (hv : Algebra.CoreShort A v)
    (h33 : v 33=0) (h34 : v 34=0) (h35 : v 35=0) (h36 : v 36=0) (s : Store)
    (hh : s.val.inputHead=preceding.length) (hr : EvalReady D.format s.val) (hb : Bank s.val v)
    (hm : BitArray.Represents s.val.memory 0 D.format.width (messageWords D w)) :
    ∃ cost, ∃ t : Store, ∃ v' : ℕ → ℕ,
      cost ≤ termPrice D.format j.val q (Codec.word D.format (w j)) A ∧
      Executes (preceding++(Codec.nat j.val++(Codec.rat q++suffix))) randomTape termCode cost s t ∧
      t.val.inputHead=s.val.inputHead+(Codec.nat j.val++Codec.rat q).length ∧
      Bank t.val v' ∧ EvalReady D.format t.val ∧
      bankValue v'=bankValue v+q*D.format.value (w j) ∧
      0 < v' 32 ∧ Algebra.CoreShort (A+termWidth D.format q (Codec.word D.format (w j))+1) v' ∧
      v' 33=0 ∧ v' 34=0 ∧ v' 35=0 ∧ v' 36=0 ∧ EvalFrame termWork s.val t.val := by
  let input := preceding++(Codec.nat j.val++(Codec.rat q++suffix))
  obtain ⟨u,eu,huh,hu45,hu10,huf⟩ := readNatural_steps 45 (by decide) j.val preceding
    (Codec.rat q++suffix) randomTape s hh (hr.parser 10 (by decide)) (hr.parser 45 (by decide))
  obtain ⟨a,ea,hah,ha10,ha12,ha13,has,haf⟩ := readRational_steps q
    (preceding++Codec.nat j.val) suffix randomTape u (by simp [huh,hh]) hu10
    ((huf.tapes 12 (by decide)).trans (hr.parser 12 (by decide)))
    ((huf.tapes 13 (by decide)).trans (hr.parser 13 (by decide)))
  have hieq : (preceding++Codec.nat j.val)++(Codec.rat q++suffix)=input := by simp [input,List.append_assoc]
  rw [hieq] at ea
  have hap : Frame {45,12,13} s.val a.val :=
    (huf.mono (by simp)).trans (haf.mono (by simp))
  have ha45 : a.val.tapes 45=BitTape.ofList j.val.bits := (haf.tapes 45 (by decide)).trans hu45
  have har : Scratch a.val 0 := hap.scratch (by intro i hi;simp;omega) hr.arithmetic
  have hab : Bank a.val v := hap.bank (by intro i hi hi';simp;omega) hb
  have haextra (i : ℕ) (hi : i ∈ ({5,6,7,8,9,65} : Finset ℕ)) : Blank a.val i :=
    RationalAccumulator.blank_of_eq (hap.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢;omega))
      (hr.blank i hi)
  obtain ⟨wo,hwo⟩ := hr.width
  obtain ⟨co,hco⟩ := hr.center
  obtain ⟨oo,hoo⟩ := haextra 7 (by decide)
  have hascratch : DecoderFetch.Scratch a.val :=
    ⟨har.1,(RationalAccumulator.zero_word_iff_blank _ _).mp har.2.1,har.2.2.1,har.2.2.2,
      haextra 5 (by decide),haextra 6 (by decide),haextra 8 (by decide),haextra 9 (by decide)⟩
  have hwidth : 0 < D.format.width.bits.length := RationalAccumulator.bits_nonempty
    (by simp [Target.FixedPointFormat.width])
  have hclock : (2^(D.format.integerBits+D.format.fractionalBits)).bits.length=addressValue D.format.width.bits := by
    rw [RationalAccumulator.address_bits,Nat.size_eq_bits_len,Nat.size_pow]
    simp [Target.FixedPointFormat.width,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  obtain ⟨fc,f,hfc,ef,hf7,hfr,hf45,hfm,hff,hf45exact⟩ := DecoderFetch.executes_reset input randomTape
    D.format.width.bits j.val.bits (2^(D.format.integerBits+D.format.fractionalBits)).bits
    (messageWords D w) j wo 0 co oo hwidth (RationalAccumulator.address_bits j.val) hclock a
    hascratch ((hap.tapes 64 (by decide)).trans hwo)
    (by simpa [BitTape.shifted,BitTape.ofList] using ha45)
    ((hap.tapes 66 (by decide)).trans hco)
    (by simpa [RationalAccumulator.address_bits,hap.memory] using hm) hoo
  have fkeep (i : ℕ) (hi : 10 ≤ i) (h45 : i ≠ 45) := hff.2 i (Or.inr (Or.inr hi)) h45
  have hfb : Bank f.val v := by
    intro i hi hi'
    exact RationalAccumulator.word_of_eq (fkeep i (by omega) (by omega)) (hab i hi hi')
  have hfar : Scratch f.val 0 :=
    ⟨hfr.1,(RationalAccumulator.zero_word_iff_blank _ _).mpr hfr.2.1,hfr.2.2.1,hfr.2.2.2.1⟩
  have hfsign : f.val.registers 23=decide (q.num<0) :=
    (hff.1.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans has
  obtain ⟨ac,t,v',hac,et,htb,htr,htval,htd,htbits,ht33,ht34,ht35,ht36,ht7,ht65,ht12,ht13,htf⟩ :=
    accumulate_steps input randomTape D.format (w j) q (Codec.word D.format (w j))
      (messageWord_value _ _) oo v A hd hv h33 h34 h35 h36 f
      (by simpa using hf7) ((fkeep 12 (by decide) (by decide)).trans ha12)
      ((fkeep 13 (by decide) (by decide)).trans ha13) hfsign
      (RationalAccumulator.word_of_eq ((fkeep 66 (by decide) (by decide)).trans (hap.tapes 66 (by decide))) hr.center)
      (RationalAccumulator.word_of_eq ((fkeep 67 (by decide) (by decide)).trans (hap.tapes 67 (by decide))) hr.scale)
      hfb hfar (RationalAccumulator.blank_of_eq (fkeep 65 (by decide) (by decide)) (haextra 65 (by decide)))
  have fullframe : EvalFrame termWork s.val t.val :=
    (hap.eval.mono (by intro i hi;simp only [Finset.mem_insert,Finset.mem_singleton] at hi;rcases hi with rfl|rfl|rfl <;> decide)).trans ((fetch_eval hff).trans htf.eval)
  have atape (i : ℕ) (hi : 4 ≤ i) (h7 : i ≠ 7) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (hb : i < 30 ∨ 36 < i) (h65 : i ≠ 65) := htf.2.2.2.2.2 i hi h7 h12 h13 hb h65
  refine ⟨_,t,v',?_,eu.seq (ea.seq (ef.seq et)),?_,htb,?_,htval,htd,htbits,ht33,ht34,ht35,ht36,fullframe⟩
  · dsimp [termPrice];omega
  · have hi1 := hff.1.1
    have hi2 := htf.2.1
    simp only [List.length_append]
    omega
  · refine ⟨htr,?_,?_,?_,?_,?_⟩
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
      · exact RationalAccumulator.blank_of_eq (atape 5 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide)) hfr.2.2.2.2.1
      · exact RationalAccumulator.blank_of_eq (atape 6 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide)) hfr.2.2.2.2.2.1
      · exact ht7
      · exact RationalAccumulator.blank_of_eq (atape 8 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide)) hfr.2.2.2.2.2.2.1
      · exact RationalAccumulator.blank_of_eq (atape 9 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)) (by decide)) hfr.2.2.2.2.2.2.2
      · exact ht65
    · intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl
      · exact (fullframe.tapes 10 (by decide)).trans (hr.parser 10 (by decide))
      · exact ht12
      · exact ht13
      · exact (atape 45 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) (by decide)).trans
          (by simpa [BitTape.blank] using hf45exact)
    · exact RationalAccumulator.word_of_eq (fullframe.tapes 64 (by decide)) hr.width
    · exact RationalAccumulator.word_of_eq (fullframe.tapes 66 (by decide)) hr.center
    · exact RationalAccumulator.word_of_eq (fullframe.tapes 67 (by decide)) hr.scale

end Maxwell.Cost.DecoderParser
