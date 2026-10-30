import Maxwell.Continuum.RationalSquareRootMachine
import Maxwell.Continuum.RationalCanonicalNaturalBank

/-! Square-root evaluation from an unreduced stored fraction. The GCD
reduction is part of the fixed program, so the result equals the existing
literal evaluator even when the input fraction has a common factor. -/

namespace Maxwell.Continuum.Calibration.RationalRoot.Raw

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def ids : Finset ℕ := RationalRoot.ids∪RationalCanonicalBank.ids
def changed : Finset ℕ := RationalRoot.changed∪RationalCanonicalBank.changed∪{542,543}
def inputValues (a b N : ℕ) (i : ℕ) : ℕ :=
  if i=544 then N else RationalCanonicalBank.inputValues a b i
def canonicalValues (a b N : ℕ) (i : ℕ) : ℕ :=
  if i=544 then N else RationalCanonicalBank.outputValues a b i
def loadPlan : List NatAssign.Instruction := [.copy 230 542,.copy 231 543]
def code : Code := .seq RationalCanonicalBank.code
  (.seq (NatAssign.code loadPlan) RationalRoot.code)
def costBound (N W : ℕ) : ℕ := 2^110*(N+W+10)^7

theorem ids_ge : ∀ i∈ids, 4 ≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with h|h
  · exact RationalRoot.ids_ge i h
  · simp only [RationalCanonicalBank.ids,Finset.mem_insert,Finset.mem_singleton] at h
    omega

theorem loadPlan_valid : ∀ a∈loadPlan, a.Valid ids := by
  simp [loadPlan,NatAssign.Instruction.Valid,ids,RationalRoot.ids,RationalCanonicalBank.ids]

theorem canonical_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (i : ℕ) : (canonicalValues a b N i).bits.length≤W := by
  have h := RationalCanonicalBank.output_width a b W ha hb i
  simp only [canonicalValues]
  split_ifs <;> assumption

theorem loaded_root_values (a b N : ℕ) (i : ℕ) (hi : i∈RationalRoot.ids) :
    NatAssign.values loadPlan (canonicalValues a b N) i=
      RationalRoot.inputValues (a/Nat.gcd a b) (b/Nat.gcd a b) N i := by
  have hn : i≠228 ∧ i≠229 ∧ i≠230 ∧ i≠231 := by
    simp only [RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
    omega
  by_cases h542 : i=542
  · subst i
    simp [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,canonicalValues,RationalCanonicalBank.outputValues,
      RationalRoot.inputValues]
  by_cases h543 : i=543
  · subst i
    simp [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,canonicalValues,RationalCanonicalBank.outputValues,
      RationalRoot.inputValues]
  simp [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,canonicalValues,RationalCanonicalBank.outputValues,
    RationalCanonicalBank.inputValues,RationalRoot.inputValues,h542,h543,hn]

theorem executes (a b N W : ℕ) (hb : 0<b) (haW : a.bits.length≤W) (hbW : b.bits.length≤W)
    (hN : N.bits.length≤W) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, ∃ numerator denominator : ℕ,
      Executes input tape code cost s t ∧ cost≤costBound N W ∧
      Word t.val 32 numerator ∧ Word t.val 548 denominator ∧ 0<denominator ∧
      (numerator:ℚ)/denominator=sqrtRationalCenter ((a:ℚ)/b) N ∧
      denominator.bits.length≤W+2*N+1 ∧
      NatAssign.Bank NaturalRoot.fullIds
        (NaturalRoot.doneValues (radicand (a/Nat.gcd a b) (b/Nat.gcd a b) N)) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  have cb : NatAssign.Bank RationalCanonicalBank.ids (RationalCanonicalBank.inputValues a b) s.val := by
    intro i hi
    have h544 : i≠544 := by
      simp only [RationalCanonicalBank.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    simpa only [inputValues,ite_eq_right h544] using hs i (Finset.mem_union_right _ hi)
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := RationalCanonicalBank.executes a b W hb haW hbW input tape s cb hz
  have fullBank : NatAssign.Bank ids (canonicalValues a b N) u.val := by
    intro i hi
    by_cases hcan : i∈RationalCanonicalBank.ids
    · have h544 : i≠544 := by
        simp only [RationalCanonicalBank.ids,Finset.mem_insert,Finset.mem_singleton] at hcan
        omega
      simpa only [canonicalValues,ite_eq_right h544] using b0 i hcan
    · have hout : i∉RationalCanonicalBank.changed := by
        have hlo := ids_ge i hi
        simp only [RationalCanonicalBank.changed,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hcan
      have h230 : i≠230 := by intro hh; subst i; exact hcan (by decide)
      have h231 : i≠231 := by intro hh; subst i; exact hcan (by decide)
      simpa only [canonicalValues,RationalCanonicalBank.outputValues,ite_eq_right h230,
        ite_eq_right h231,inputValues] using RationalAccumulator.word_of_eq (f0.tapes i hout) (hs i hi)
  obtain ⟨c1,v,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ids ids_ge loadPlan loadPlan_valid
    (canonicalValues a b N) input tape u fullBank z0
  have price := NatAssign.price_bound ids loadPlan loadPlan_valid (canonicalValues a b N) W
    (fun i _ => canonical_width a b N W haW hbW hN i)
    (by simp [loadPlan,NatAssign.Instruction.literalWidth])
  have cost1 : c1≤3000*8^2*(W+2)^2 := by
    simpa only [loadPlan,List.length_cons,List.length_nil] using hc1.trans price
  have rootBank : NatAssign.Bank RationalRoot.ids
      (RationalRoot.inputValues (a/Nat.gcd a b) (b/Nat.gcd a b) N) v.val := by
    intro i hi
    simpa only [loaded_root_values a b N i hi] using b1 i (Finset.mem_union_left _ hi)
  have canonwidth := RationalCanonical.canonical_width a b W
    (by simpa only [Nat.size_eq_bits_len] using haW) (by simpa only [Nat.size_eq_bits_len] using hbW)
  obtain ⟨c2,t,e2,hc2,num,den,_,_,_,rootBankOut,z2,f2⟩ := RationalRoot.executes
    (a/Nat.gcd a b) (b/Nat.gcd a b) N W
      (by simpa only [Nat.size_eq_bits_len] using canonwidth.1)
      (by simpa only [Nat.size_eq_bits_len] using canonwidth.2) hN input tape v rootBank z1
  refine ⟨c0+(c1+c2),t,Nat.sqrt (radicand (a/Nat.gcd a b) (b/Nat.gcd a b) N),
    (b/Nat.gcd a b)*2^N,e0.seq (e1.seq e2),?_,num,den,?_,?_,?_,rootBankOut,z2,
      (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  · apply (Nat.add_le_add hc0 (Nat.add_le_add cost1 hc2)).trans
    unfold RationalCanonicalBank.costBound RationalRoot.costBound costBound
    ring_nf
    omega
  · exact Nat.mul_pos (RationalCanonical.canonical_denominator_pos a b hb) (by positivity)
  · have hn := RationalCanonical.value_num_natAbs false a b hb
    have hd := RationalCanonical.value_den false a b hb
    simp only [RationalCanonical.value,Bool.false_eq_true,↓reduceIte] at hn hd
    rw [←hn,←hd]
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using literal_value ((a:ℚ)/b) N
  · have hq : (b/Nat.gcd a b).bits.length≤W := by
      simpa only [Nat.size_eq_bits_len] using canonwidth.2
    have hp := SelectedParameters.Geometric.power_bits 2 N
    change (2^N).bits.length≤N*2+1 at hp
    have hm := RationalAccumulator.bits_mul_le (b/Nat.gcd a b) (2^N)
    omega

#print axioms executes

end Maxwell.Continuum.Calibration.RationalRoot.Raw
