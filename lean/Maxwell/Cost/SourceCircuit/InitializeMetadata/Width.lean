import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.SourceCircuit.InitializeMetadata
open Structured RationalAccumulator
abbrev Frame := BinaryPrecision.Frame

def exponent (m p : ℕ) : ℕ := 4+m.size+p.size
def width (m p : ℕ) : ℕ := exponent m p+1

/-- Every allocated copy, dyadic term and row sum fits in this measured
word width. The width depends only logarithmically on the stored values. -/
theorem width_room (n m p : ℕ) (hn : n ≤ m) (hp : 1 ≤ p) :
    2*n+m*(4*p+3) < 2^width m p := by
  have hm := Nat.lt_size_self m
  have hp' := Nat.lt_size_self p
  have hprod : m*p < 2^m.size*2^p.size := by
    have hpow : 0 < 2^m.size := by positivity
    nlinarith
  have hsmall : 2*n+m*(4*p+3) ≤ 9*(m*p) := by nlinarith
  have hpos : 0 < 2^m.size*2^p.size := by positivity
  simp only [width, exponent, pow_add]
  norm_num
  nlinarith only [hprod, hsmall, hpos]

theorem width_pos (m p : ℕ) : 0 < width m p := by simp [width]

def exponentWork : Finset ℕ := {0,1,2,3,90,107,108}
def exponentCode : Code := .seq (WordLength.code 79 90)
  (.seq (WordLength.code 84 107) (.seq (DecoderConstants.addCode 107 90)
    (.seq (BinaryPrecision.literalCode 108 4) (DecoderConstants.addCode 108 90))))

private theorem stored_frame {s t : BitRAMState}
    (h : StoredProduct.Frame 90 s t) : Frame exponentWork s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  simp only [exponentWork, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact h.2.2.2.2.2.1 i (by omega) (by omega)

theorem wordLength (source target n : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Word s.val source n) (ht : Blank s.val target) :
    ∃ cost t, Executes input tape (WordLength.code source target) cost s t ∧
      cost ≤ 48*(n.size+1)^2+1 ∧ Word t.val target n.size ∧ Frame {target} s.val t.val := by
  obtain ⟨so, hso⟩ := hs
  obtain ⟨dest, hd⟩ := ht
  obtain ⟨cost,t,he,hcost,hs',ht',hf⟩ := WordLength.executes source target hne input tape
    n.bits so dest s hso hd
  refine ⟨cost,t,he,by simpa only [Nat.size_eq_bits_len] using hcost,
    ⟨dest,by simpa only [Nat.size_eq_bits_len] using ht'⟩,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  have hit : i ≠ target := by simpa using hi
  by_cases his : i = source
  · subst i; exact hs'.trans hso.symm
  · exact hf.2.2.2.2.2.1 i his hit

/-- The code measures both binary input words before adding the fixed
margin. No gate bound or word width is provided as a host-computed input. -/
theorem exponent_executes (input : List Bool) (tape : ℕ → Bool) (m p : ℕ) (s : Store)
    (hm : Word s.val 79 m) (hp : Word s.val 84 p)
    (hb : ∀ i ∈ exponentWork, Blank s.val i) :
    ∃ cost t, Executes input tape exponentCode cost s t ∧
      cost ≤ 10000*(m.size+p.size+5)^2 ∧ Word t.val 90 (exponent m p) ∧
      Word t.val 107 p.size ∧ Word t.val 108 4 ∧
      (∀ i, i < 4 → Blank t.val i) ∧ Frame exponentWork s.val t.val := by
  obtain ⟨ac,a,ea,hac,ha90,fa⟩ := wordLength 79 90 m (by decide) input tape s hm (hb 90 (by decide))
  obtain ⟨bc,b,eb,hbc,hb107,fb⟩ := wordLength 84 107 p (by decide) input tape a
    (word_of_eq (fa.tapes 84 (by decide)) hp)
    (blank_of_eq (fa.tapes 107 (by decide)) (hb 107 (by decide)))
  have fab : Frame exponentWork s.val b.val :=
    (fa.mono (by decide)).trans (fb.mono (by decide))
  have bb (i : ℕ) (hi : i < 4) : Blank b.val i :=
    blank_of_eq ((fb.tapes i (by simp; omega)).trans (fa.tapes i (by simp; omega)))
      (hb i (by interval_cases i <;> decide))
  obtain ⟨cc,c,hcc,ec,hc90,cb,fc⟩ := DecoderConstants.add 107 90 (by decide) (by decide)
    (by decide) input tape p.size m.size b hb107
    (word_of_eq (fb.tapes 90 (by decide)) ha90) bb
  have fac : Frame exponentWork s.val c.val := fab.trans (stored_frame fc)
  have hc108 : Blank c.val 108 :=
    blank_of_eq ((fc.2.2.2.2.2.1 108 (by decide) (by decide)).trans
      ((fb.tapes 108 (by decide)).trans (fa.tapes 108 (by decide)))) (hb 108 (by decide))
  obtain ⟨d,ed,hd108,fd⟩ := BinaryPrecision.literal 108 4 input tape c hc108
  obtain ⟨ecost,t,hecost,et,ht90,tb,ft⟩ := DecoderConstants.add 108 90 (by decide) (by decide)
    (by decide) input tape 4 (p.size+m.size) d hd108
    (word_of_eq (fd.tapes 90 (by decide)) hc90)
    (fun i hi => blank_of_eq (fd.tapes i (by simp; omega)) (cb i hi))
  refine ⟨_,t,ea.seq (eb.seq (ec.seq (ed.seq et))),?_,?_,?_,?_,tb,
    (fac.trans (fd.mono (by decide))).trans (stored_frame ft)⟩
  · have hms : m.size.bits.length ≤ m.size := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length m.size
    have hps : p.size.bits.length ≤ p.size := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length p.size
    have hsum : (p.size+m.size).bits.length ≤ p.size+m.size := by
      simpa only [WordLength.countBits_eq] using WordLength.countBits_length (p.size+m.size)
    have hfour : (Nat.bits 4).length = 3 := by decide
    rw [hfour] at hecost ⊢
    nlinarith only [hac,hbc,hcc,hecost,hms,hps,hsum]
  · simpa [exponent, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht90
  · exact word_of_eq ((ft.2.2.2.2.2.1 107 (by decide) (by decide)).trans
      ((fd.tapes 107 (by decide)).trans (fc.2.2.2.2.2.1 107 (by decide) (by decide)))) hb107
  · exact word_of_eq (ft.2.2.2.2.2.1 108 (by decide) (by decide)) hd108

end Maxwell.Cost.SourceCircuit.InitializeMetadata
