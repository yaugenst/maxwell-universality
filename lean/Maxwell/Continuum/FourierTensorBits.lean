import Maxwell.Continuum.FourierTensorEncoding
import Maxwell.Continuum.DyadicMagnitudeBits

/-! Literal final coefficient arrays for a finite Fourier sum and a three-component field. -/

namespace Maxwell.Continuum.Profile
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] fourierTensorCoefficient waveWorkBits waveDegree

variable {ι : Type*} {B : ℕ}

/-- The final scalar tensor array, with one summed coefficient at every grid index. -/
def finalData (s : Finset ι) (q : ι→Fin 3→ℚ) (a : ι→ComplexDyadic B) (Q N : ℕ) :
    List (ComplexDyadic (B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N))) :=
  (List.finRange (waveDegree (8*Q) N)).flatMap fun i =>
    (List.finRange (waveDegree (8*Q) N)).flatMap fun j =>
      (List.finRange (waveDegree (8*Q) N)).map fun k => fourierTensorCoefficient s q a Q N ![i,j,k]

private theorem flatMap_length_const {α β : Type*} (xs : List α) (f : α→List β) (n : ℕ)
    (hf : ∀ x, (f x).length=n) : (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,hf,ih,List.length_cons]; ring

theorem finalData_length (s : Finset ι) (q : ι→Fin 3→ℚ) (a : ι→ComplexDyadic B) (Q N : ℕ) :
    (finalData s q a Q N).length=(waveDegree (8*Q) N)^3 := by
  unfold finalData
  rw [flatMap_length_const _ _ ((waveDegree (8*Q) N)^2)]
  · simp only [List.length_finRange]
    ring
  · intro i
    rw [flatMap_length_const _ _ (waveDegree (8*Q) N)]
    · simp only [List.length_finRange]
      ring
    · intro j
      simp

theorem fourierTensorCoefficient_mem_finalData (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : ι→ComplexDyadic B) (Q N : ℕ) (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    fourierTensorCoefficient s q a Q N j∈finalData s q a Q N := by
  have he : ![j 0,j 1,j 2]=j := by ext i; fin_cases i <;> rfl
  simp only [finalData,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  exact ⟨j 0,j 1,j 2,congrArg (fourierTensorCoefficient s q a Q N) he⟩

theorem fourierTensorCoefficient_power_bound (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : ι→ComplexDyadic B) (Q N A : ℕ) (hq : ∀ ν∈s, ∀ i, |q ν i|≤Q)
    (ha : (∑ ν∈s, ‖complexDyadicValue (a ν)‖)≤(2:ℝ)^A)
    (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    ‖complexDyadicValue (fourierTensorCoefficient s q a Q N j)‖≤(2:ℝ)^(A+14) := by
  calc
    _ ≤ (∑ ν∈s, ‖complexDyadicValue (a ν)‖)*22^3 := fourierTensorCoefficient_norm s q a Q N hq j
    _ ≤ (2:ℝ)^A*2^14 := mul_le_mul ha (by norm_num) (by positivity) (by positivity)
    _ = _ := (pow_add _ _ _).symm

theorem fourierTensorCoefficient_bits (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : ι→ComplexDyadic B) (Q N A : ℕ) (hq : ∀ ν∈s, ∀ i, |q ν i|≤Q)
    (ha : (∑ ν∈s, ‖complexDyadicValue (a ν)‖)≤(2:ℝ)^A)
    (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    (fourierTensorCoefficient s q a Q N j).1.numeratorBits≤B+3*waveWorkBits (8*Q) N+A+16 ∧
    (fourierTensorCoefficient s q a Q N j).2.numeratorBits≤B+3*waveWorkBits (8*Q) N+A+16 := by
  have hn := fourierTensorCoefficient_power_bound s q a Q N A hq ha j
  have hc := complexDyadicValue_coordinate_bounds (fourierTensorCoefficient s q a Q N j)
    (B := (2:ℚ)^(A+14)) (by simpa using hn)
  have h1 := dyadic_numerator_bits_of_bound _ hc.1
  have h2 := dyadic_numerator_bits_of_bound _ hc.2
  constructor <;> omega

def finalBits (s : Finset ι) (q : ι→Fin 3→ℚ) (a : ι→ComplexDyadic B) (Q N : ℕ) : List Bool :=
  complexDyadicDataBits (finalData s q a Q N)

theorem finalBits_length (s : Finset ι) (q : ι→Fin 3→ℚ) (a : ι→ComplexDyadic B)
    (Q N A : ℕ) (hq : ∀ ν∈s, ∀ i, |q ν i|≤Q)
    (ha : (∑ ν∈s, ‖complexDyadicValue (a ν)‖)≤(2:ℝ)^A) :
    (finalBits s q a Q N).length≤8*((waveDegree (8*Q) N)^3+1)*(B+3*waveWorkBits (8*Q) N+A+17) := by
  have hh := complexDyadicDataBits_length (B := A+14) (finalData s q a Q N) (by
    intro d hd
    simp only [finalData,List.mem_flatMap,List.mem_map] at hd
    obtain ⟨i,_,j,_,k,_,rfl⟩ := hd
    exact fourierTensorCoefficient_power_bound s q a Q N A hq ha ![i,j,k])
  rw [finalData_length] at hh
  have he : B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N)+(A+14)+3=
      B+3*waveWorkBits (8*Q) N+A+17 := by omega
  simpa only [finalBits,he] using hh

/-- Three component arrays, stored in coordinate order with one shared precision. -/
def finalVectorData (s : Finset ι) (q : ι→Fin 3→ℚ) (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :
    List (ComplexDyadic (B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N))) :=
  (List.finRange 3).flatMap fun c => finalData s q (a c) Q N

theorem finalVectorData_length (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N : ℕ) :
    (finalVectorData s q a Q N).length=3*(waveDegree (8*Q) N)^3 := by
  unfold finalVectorData
  rw [flatMap_length_const _ _ ((waveDegree (8*Q) N)^3) (fun _ => finalData_length _ _ _ _ _)]
  simp

def finalVectorBits (s : Finset ι) (q : ι→Fin 3→ℚ) (a : Fin 3→ι→ComplexDyadic B)
    (Q N : ℕ) : List Bool := complexDyadicDataBits (finalVectorData s q a Q N)

theorem finalVectorBits_length (s : Finset ι) (q : ι→Fin 3→ℚ)
    (a : Fin 3→ι→ComplexDyadic B) (Q N A : ℕ) (hq : ∀ ν∈s, ∀ i, |q ν i|≤Q)
    (ha : ∀ c, (∑ ν∈s, ‖complexDyadicValue (a c ν)‖)≤(2:ℝ)^A) :
    (finalVectorBits s q a Q N).length≤8*(3*(waveDegree (8*Q) N)^3+1)*
      (B+3*waveWorkBits (8*Q) N+A+17) := by
  have hh := complexDyadicDataBits_length (B := A+14) (finalVectorData s q a Q N) (by
    intro d hd
    simp only [finalVectorData,finalData,List.mem_flatMap,List.mem_map] at hd
    obtain ⟨c,_,i,_,j,_,k,_,rfl⟩ := hd
    exact fourierTensorCoefficient_power_bound s q (a c) Q N A hq (ha c) ![i,j,k])
  rw [finalVectorData_length] at hh
  have he : B+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N)+(A+14)+3=
      B+3*waveWorkBits (8*Q) N+A+17 := by omega
  simpa only [finalVectorBits,he] using hh

#print axioms finalData_length
#print axioms fourierTensorCoefficient_bits
#print axioms finalVectorBits_length

end Maxwell.Continuum.Profile
