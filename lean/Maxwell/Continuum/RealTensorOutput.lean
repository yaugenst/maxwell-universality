import Maxwell.Continuum.CompactTemplateReal
import Maxwell.Continuum.FourierTensorResources
import Maxwell.Continuum.ProfileCoefficientBits

/-! Literal real tensor output: one radial profile and three real dyadic
coefficient arrays. The Boolean lengths concern these emitted words. -/

namespace Maxwell.Continuum.Profile

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable {ι : Type*} {B : ℕ}

def realFinalVectorData (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :=
  (finalVectorData s q a Q N).map Prod.fst

theorem realFinalVectorData_formula (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :
    realFinalVectorData s q a Q N=
      (List.finRange 3).flatMap fun c =>
        (List.finRange (waveDegree (8*Q) N)).flatMap fun i =>
          (List.finRange (waveDegree (8*Q) N)).flatMap fun j =>
            (List.finRange (waveDegree (8*Q) N)).map fun k =>
              realFourierTensorCoefficient s q (a c) Q N ![i,j,k] := by
  simp only [realFinalVectorData,finalVectorData,finalData,List.map_flatMap,List.map_map,
    Function.comp_def,realFourierTensorCoefficient]

theorem realFinalVectorData_length (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :
    (realFinalVectorData s q a Q N).length=3*(waveDegree (8*Q) N)^3 := by
  rw [realFinalVectorData,List.length_map,finalVectorData_length]

theorem realFinalVectorCoefficient_bits (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N A : ℕ) (hq : ∀ν∈s,∀i,|q ν i|≤Q)
    (ha : ∀c,(∑ν∈s,‖complexDyadicValue (a c ν)‖)≤(2 : ℝ)^A)
    (c : Fin 3) (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    (realFourierTensorCoefficient s q (a c) Q N j).numeratorBits≤
      B+3*waveWorkBits (8*Q) N+A+16 :=
  (fourierTensorCoefficient_bits s q (a c) Q N A hq (ha c) j).1

def realFinalVectorBits (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) : List Bool :=
  Codec.nat (B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N)) ++
    Codec.list (fun d => Codec.int d.numerator) (realFinalVectorData s q a Q N)

private theorem real_flatMap_length {P : ℕ} (xs : List (ComplexDyadic P)) :
    ((xs.map Prod.fst).flatMap (fun d => Codec.int d.numerator)).length≤
      (xs.flatMap complexDyadicBits).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.flatMap_cons,List.length_append,complexDyadicBits]
    omega

theorem realFinalVectorBits_le (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :
    (realFinalVectorBits s q a Q N).length≤(finalVectorBits s q a Q N).length := by
  have h := real_flatMap_length (finalVectorData s q a Q N)
  simp only [realFinalVectorBits,finalVectorBits,realFinalVectorData,
    complexDyadicDataBits,Codec.list,List.length_append,List.length_map]
  omega

theorem realFinalVectorBits_length (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N A : ℕ) (hq : ∀ν∈s,∀i,|q ν i|≤Q)
    (ha : ∀c,(∑ν∈s,‖complexDyadicValue (a c ν)‖)≤(2 : ℝ)^A) :
    (realFinalVectorBits s q a Q N).length≤
      8*(3*(waveDegree (8*Q) N)^3+1)*(B+3*waveWorkBits (8*Q) N+A+17) :=
  (realFinalVectorBits_le s q a Q N).trans (finalVectorBits_length s q a Q N A hq ha)

theorem realFinalVectorBits_polylog (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) {Q N A C ℓ : ℕ} (hq : ∀ν∈s,∀i,|q ν i|≤Q)
    (ha : ∀c,(∑ν∈s,‖complexDyadicValue (a c ν)‖)≤(2 : ℝ)^A)
    (hℓ : 0<ℓ) (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) (hB : B≤C*ℓ) (hA : A≤C*ℓ) :
    (realFinalVectorBits s q a Q N).length≤finalVectorBitsCoefficient C*ℓ^25 :=
  (realFinalVectorBits_le s q a Q N).trans
    (finalVectorBits_polylog s q a hq ha hℓ hQ hN hB hA)

/-- The degree, shared radial profile, and the three literal real arrays.
The physical center and scale belong to the separately stored placement. -/
def realCompactBits (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) : List Bool :=
  Codec.nat (waveDegree (8*Q) N) ++ profileBits N ++ realFinalVectorBits s q a Q N

def realCompactBitsCoefficient (C : ℕ) : ℕ :=
  2*waveDegreeCoefficient C+1+2^41*(C+1)^3+finalVectorBitsCoefficient C

theorem realCompactBits_polylog (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) {Q N A C ℓ : ℕ} (hq : ∀ν∈s,∀i,|q ν i|≤Q)
    (ha : ∀c,(∑ν∈s,‖complexDyadicValue (a c ν)‖)≤(2 : ℝ)^A)
    (hℓ : 0<ℓ) (hQ : Q≤C*ℓ^8) (hN : N≤C*ℓ) (hB : B≤C*ℓ) (hA : A≤C*ℓ) :
    (realCompactBits s q a Q N).length≤realCompactBitsCoefficient C*ℓ^25 := by
  have ht := realFinalVectorBits_polylog s q a hq ha hℓ hQ hN hB hA
  have hp := profileBits_length N
  have hd := waveDegree_polylog hℓ hQ hN
  have hu : unsignedBitLength (waveDegree (8*Q) N)≤waveDegree (8*Q) N := by
    rw [Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := waveDegree (8*Q) N))
  have h1 : 1≤ℓ^25 := one_le_pow₀ (by omega)
  have h8 : ℓ^8≤ℓ^25 := Nat.pow_le_pow_right hℓ (by decide)
  have h3 : ℓ^3≤ℓ^25 := Nat.pow_le_pow_right hℓ (by decide)
  have hn : N+1≤(C+1)*ℓ := by nlinarith only [hN,hℓ]
  have hn3 := Nat.pow_le_pow_left hn 3
  have hpn : (N+1)^3≤(C+1)^3*ℓ^25 := by
    calc
      _ ≤ ((C+1)*ℓ)^3 := hn3
      _ = (C+1)^3*ℓ^3 := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  have hdn := hd.trans (Nat.mul_le_mul_left _ h8)
  have hpp := hp.trans (Nat.mul_le_mul_left _ hpn)
  simp only [realCompactBits,List.length_append,Codec.nat_length]
  unfold realCompactBitsCoefficient
  nlinarith only [ht,hu,h1,hdn,hpp]

#print axioms realFinalVectorData_formula
#print axioms realCompactBits_polylog

end Maxwell.Continuum.Profile
