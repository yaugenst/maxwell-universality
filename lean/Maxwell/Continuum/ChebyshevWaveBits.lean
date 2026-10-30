import Maxwell.Continuum.TensorChebyshev
import Maxwell.Continuum.DyadicMagnitudeBits

/-! Actual plane-wave and tensor coefficient words and their serialization sizes. -/

namespace Maxwell.Continuum.Profile
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] waveRoundedCoefficient tensorWaveCoefficient waveWorkBits waveDegree

theorem waveRoundedCoefficient_bits (q : ℚ) (Q N j : ℕ) (hq : |q|≤Q)
    (hj : j≤waveDegree (8*Q) N) :
    (waveRoundedCoefficient q Q N j).1.numeratorBits≤waveWorkBits (8*Q) N+7 ∧
    (waveRoundedCoefficient q Q N j).2.numeratorBits≤waveWorkBits (8*Q) N+7 := by
  have hn := waveRoundedCoefficient_bound q Q N j hq hj
  have hc := complexDyadicValue_coordinate_bounds (waveRoundedCoefficient q Q N j)
    (B := 22) (by simpa using hn)
  exact ⟨dyadic_numerator_bits_of_bound _ (hc.1.trans (by norm_num : (22:ℚ)≤2^5)),
    dyadic_numerator_bits_of_bound _ (hc.2.trans (by norm_num : (22:ℚ)≤2^5))⟩

def waveBits (q : ℚ) (Q N : ℕ) : List Bool := complexDyadicDataBits (waveData q Q N)

theorem waveBits_length (q : ℚ) (Q N : ℕ) (hq : |q|≤Q) :
    (waveBits q Q N).length≤8*(waveDegree (8*Q) N+1)*(waveWorkBits (8*Q) N+8) := by
  have hh := complexDyadicDataBits_length (B := 5) (waveData q Q N) (by
    intro d hd
    simp only [waveData,List.mem_map,List.mem_range] at hd
    obtain ⟨j,hj,rfl⟩ := hd
    exact (waveRoundedCoefficient_bound q Q N j hq hj.le).trans (by norm_num))
  simpa only [waveBits,waveData_length,Nat.reduceAdd] using hh

/-- One canonical executable tensor array, in lexicographic coordinate order. -/
def tensorData (q : Fin 3→ℚ) (Q N : ℕ) :
    List (ComplexDyadic (waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N)) :=
  (List.finRange (waveDegree (8*Q) N)).flatMap fun i =>
    (List.finRange (waveDegree (8*Q) N)).flatMap fun j =>
      (List.finRange (waveDegree (8*Q) N)).map fun k => tensorWaveCoefficient q Q N ![i,j,k]

private theorem flatMap_length_const {α β : Type*} (xs : List α) (f : α→List β) (n : ℕ)
    (hf : ∀ x, (f x).length=n) : (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.length_append,hf,ih,List.length_cons]; ring

theorem tensorData_length (q : Fin 3→ℚ) (Q N : ℕ) :
    (tensorData q Q N).length=(waveDegree (8*Q) N)^3 := by
  unfold tensorData
  rw [flatMap_length_const _ _ ((waveDegree (8*Q) N)^2)]
  · simp only [List.length_finRange]
    ring
  · intro i
    rw [flatMap_length_const _ _ (waveDegree (8*Q) N)]
    · simp only [List.length_finRange]
      ring
    · intro j
      simp

theorem tensorWaveCoefficient_bits (q : Fin 3→ℚ) (Q N : ℕ) (hq : ∀ i, |q i|≤Q)
    (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    (tensorWaveCoefficient q Q N j).1.numeratorBits≤3*waveWorkBits (8*Q) N+16 ∧
    (tensorWaveCoefficient q Q N j).2.numeratorBits≤3*waveWorkBits (8*Q) N+16 := by
  have hn := tensorWaveCoefficient_norm q Q N hq j
  have hc := complexDyadicValue_coordinate_bounds (tensorWaveCoefficient q Q N j)
    (B := 22^3) (by simpa using hn)
  have h1 := dyadic_numerator_bits_of_bound _ (hc.1.trans (by norm_num : (22:ℚ)^3≤2^14))
  have h2 := dyadic_numerator_bits_of_bound _ (hc.2.trans (by norm_num : (22:ℚ)^3≤2^14))
  constructor <;> omega

def tensorBits (q : Fin 3→ℚ) (Q N : ℕ) : List Bool := complexDyadicDataBits (tensorData q Q N)

theorem tensorBits_length (q : Fin 3→ℚ) (Q N : ℕ) (hq : ∀ i, |q i|≤Q) :
    (tensorBits q Q N).length≤8*((waveDegree (8*Q) N)^3+1)*(3*waveWorkBits (8*Q) N+17) := by
  have hh := complexDyadicDataBits_length (B := 14) (tensorData q Q N) (by
    intro d hd
    simp only [tensorData,List.mem_flatMap,List.mem_map] at hd
    obtain ⟨i,_,j,_,k,_,rfl⟩ := hd
    exact (tensorWaveCoefficient_norm q Q N hq ![i,j,k]).trans (by norm_num))
  rw [tensorData_length] at hh
  have he : waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+14+3=
      3*waveWorkBits (8*Q) N+17 := by omega
  simpa only [tensorBits,he] using hh

#print axioms waveBits_length
#print axioms tensorData_length
#print axioms tensorBits_length

end Maxwell.Continuum.Profile
