import Maxwell.Cost.RationalCanonical
import Maxwell.Continuum.NatAssignOutputWidth

/-! Canonical reduction is an executed GCD and two exact divisions. This
wrapper exposes their actual output words to subsequent arithmetic stages. -/

namespace Maxwell.Continuum.RationalCanonicalBank

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2200000

def ids : Finset ℕ := {4,220,221,222,223,228,229,230,231}
def changed : Finset ℕ := {0,1,2,3}∪ids
def inputValues (a b : ℕ) (i : ℕ) : ℕ := if i=228 then a else if i=229 then b else 0
def outputValues (a b : ℕ) (i : ℕ) : ℕ :=
  if i=230 then a/Nat.gcd a b else if i=231 then b/Nat.gcd a b else inputValues a b i
def code : Code := RationalCanonical.normalizeCode
def costBound (W : ℕ) : ℕ := 2^24*(W+2)^3

theorem output_width (a b W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (outputValues a b i).bits.length≤W := by
  have hc := RationalCanonical.canonical_width a b W
    (by simpa only [Nat.size_eq_bits_len] using ha)
    (by simpa only [Nat.size_eq_bits_len] using hb)
  rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at hc
  have hz : (0:ℕ).bits.length=0 := rfl
  simp only [outputValues,inputValues]
  split_ifs <;> omega

theorem executes (a b W : ℕ) (hb : 0<b) (haW : a.bits.length≤W) (hbW : b.bits.length≤W)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues a b) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound W ∧
      NatAssign.Bank ids (outputValues a b) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  have workzero (i : ℕ) (hi : i∈({4,220,221,222,223,230,231}:Finset ℕ)) : Blank s.val i := by
    have hi' : i∈ids := (by decide : ({4,220,221,222,223,230,231}:Finset ℕ)⊆ids) hi
    have h228 : i≠228 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
    have h229 : i≠229 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp
      (by simpa [inputValues,h228,h229] using hs i hi')
  have ready : RationalCanonical.NormalizeReady s.val a b :=
    ⟨by simpa [inputValues] using hs 228 (by decide),
     by simpa [inputValues] using hs 229 (by decide),
     ⟨(RationalAccumulator.zero_word_iff_blank _ _).mpr (workzero 220 (by decide)),
      (RationalAccumulator.zero_word_iff_blank _ _).mpr (workzero 221 (by decide)),
      workzero 222 (by decide),workzero 223 (by decide),fun i hi => by
        by_cases h4 : i=4
        · exact h4 ▸ workzero 4 (by decide)
        · exact hz i (by omega)⟩,
     workzero 230 (by decide),workzero 231 (by decide)⟩
  obtain ⟨cost,t,hcost,run,num,den,done,frame⟩ := RationalCanonical.normalize input tape a b hb s ready
  have costpoly : cost≤costBound W := by
    have hbase : RationalCanonical.normalizeBudget a b≤RationalCanonical.costBound a b := by
      unfold RationalCanonical.costBound
      omega
    have hp := RationalCanonical.costBound_polynomial a b
    have hb' : a.size+b.size+2≤2*W+2 := by
      rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len]
      omega
    have hpow := Nat.pow_le_pow_left hb' 3
    apply (hcost.trans (hbase.trans hp)).trans
    apply (Nat.mul_le_mul_left _ hpow).trans
    unfold costBound
    ring_nf
    omega
  have bank : NatAssign.Bank ids (outputValues a b) t.val := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [outputValues,inputValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr
        (done.work.scratch 4 (by decide))
    · simpa [outputValues,inputValues] using done.work.first
    · simpa [outputValues,inputValues] using done.work.second
    · simpa [outputValues,inputValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr done.work.quotient
    · simpa [outputValues,inputValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr done.work.remainder
    · simpa [outputValues,inputValues] using done.numerator
    · simpa [outputValues,inputValues] using done.denominator
    · simpa [outputValues] using num
    · simpa [outputValues] using den
  exact ⟨cost,t,run,costpoly,bank,fun i hi => done.work.scratch i (by omega),
    ⟨frame.address,frame.inputHead,frame.memory,frame.randomCursor,frame.output,
      fun i hi => frame.tapes i (by
        simp only [changed,ids,Finset.mem_union,Finset.mem_insert,
          Finset.mem_singleton,not_or] at hi ⊢
        tauto)⟩⟩

#print axioms executes

end Maxwell.Continuum.RationalCanonicalBank
