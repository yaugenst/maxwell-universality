import Maxwell.Continuum.CutoffRawEvaluation

/-! Exact finite antiderivative coefficients for repeated cutoff queries.
The coefficients are raw numerator/denominator words, with no normalization. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow Profile Polynomial
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
attribute [local irreducible] encodedCoefficient profileDegree chebyshevRow

def monomialCoefficient (N : ℕ) (k : Fin (profileDegree N)) : Parts :=
  sum (fun j => (coefficient N j).mul
    (Parts.literal ((chebyshevRow (profileDegree N) j).get k : ℚ))) (profileDegree N)

def antiderivativeCoefficient (N : ℕ) (k : Fin (profileDegree N)) : Parts :=
  ((monomialCoefficient N k).mul (power (Parts.literal 4) k.val)).mul
    (Parts.literal (2*(k.val:ℚ)+1)).inverse

def antiderivativeData (N : ℕ) : Vector Parts (profileDegree N) :=
  Vector.ofFn (antiderivativeCoefficient N)

theorem monomialCoefficient_valid (N : ℕ) (k : Fin (profileDegree N)) :
    (monomialCoefficient N k).Valid :=
  sum_valid _ _ (fun j _ => Parts.mul_valid (coefficient_valid N j) (Parts.literal_valid _))

theorem antiderivativeCoefficient_valid (N : ℕ) (k : Fin (profileDegree N)) :
    (antiderivativeCoefficient N k).Valid :=
  Parts.mul_valid (Parts.mul_valid (monomialCoefficient_valid N k)
    (power_valid _ (Parts.literal_valid _) _))
    (Parts.inverse_valid (by rw [Parts.literal_value]; positivity))

theorem monomialCoefficient_value (N : ℕ) (k : Fin (profileDegree N)) :
    (monomialCoefficient N k).value=
      ∑ j∈Finset.range (profileDegree N),
        (encodedCoefficient N j).value*((chebyshevRow (profileDegree N) j).get k : ℚ) := by
  rw [monomialCoefficient,sum_value _ _
    (fun j _ => Parts.mul_valid (coefficient_valid N j) (Parts.literal_valid _))]
  simp only [Parts.mul_value,coefficient_value,Parts.literal_value]

theorem antiderivativeCoefficient_value (N : ℕ) (k : Fin (profileDegree N)) :
    (antiderivativeCoefficient N k).value=
      (∑ j∈Finset.range (profileDegree N),
        (encodedCoefficient N j).value*((chebyshevRow (profileDegree N) j).get k : ℚ))*
        (4:ℚ)^k.val/(2*(k.val:ℚ)+1) := by
  unfold antiderivativeCoefficient
  rw [Parts.mul_value,Parts.mul_value,monomialCoefficient_value,power_value,
    Parts.inverse_value _ (Parts.literal_valid _) (by rw [Parts.literal_value]; positivity)]
  simp only [Parts.literal_value]
  rfl

theorem antiderivativeCoefficient_width (N : ℕ) (k : Fin (profileDegree N)) :
    (antiderivativeCoefficient N k).Width
      (profileDegree N*(272*(N+1)+2*profileDegree N+4)+6*profileDegree N+6) := by
  have hs : (monomialCoefficient N k).Width
      (profileDegree N*(272*(N+1)+2*profileDegree N+3)+1) := by
    apply sum_width
    intro j hj
    apply ((coefficient_width N j hj).mul (Parts.literal_width
      (chebyshevRow_width (profileDegree N) j k))).mono
    omega
  have h4 : (Parts.literal (4:ℚ)).Width 3 :=
    Parts.literal_width (by constructor <;> decide)
  have hd : (Parts.literal (2*(k.val:ℚ)+1)).Width (2*k.val+2) := by
    apply Parts.literal_width
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      RationalWords.width_nat (2*k.val+1)
  apply ((hs.mul (power_width h4 k.val)).mul hd.inverse).mono
  have hk := k.isLt
  nlinarith

theorem antiderivativeCoefficient_width_polynomial (N : ℕ) (k : Fin (profileDegree N)) :
    (antiderivativeCoefficient N k).Width (2^65*(N+1)^4) := by
  apply (antiderivativeCoefficient_width N k).mono
  have hd := profileDegree_bound N
  have h1 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hN : N+1≤(N+1)^2 := le_self_pow₀ (by omega) (by decide : (2:ℕ)≠0)
  have hin : 272*(N+1)+2*profileDegree N+4≤2^32*(N+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul hd hin
  have hd4 : (N+1)^2≤(N+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith only [hm,hd,hd4,h1]

theorem squareIntegral_full (D j : ℕ) (hj : j<D) (a b : ℚ) :
    chebyshevSquareIntegral j a b=
      ∑ k : Fin D, ((chebyshevRow D j).get k:ℚ)*4^k.val*
        (b^(2*k.val+1)-a^(2*k.val+1))/(2*(k.val:ℚ)+1) := by
  let f : ℕ→ℚ := fun k => (Chebyshev.T ℚ (j:ℤ)).coeff k*4^k*
    (b^(2*k+1)-a^(2*k+1))/(2*(k:ℚ)+1)
  have left : chebyshevSquareIntegral j a b=∑ k∈Finset.range (j+1), f k := by
    unfold chebyshevSquareIntegral
    simp only [chebyshevRow_coeff_rat]
    exact Fin.sum_univ_eq_sum_range f (j+1)
  have right : (∑ k : Fin D, ((chebyshevRow D j).get k:ℚ)*4^k.val*
        (b^(2*k.val+1)-a^(2*k.val+1))/(2*(k.val:ℚ)+1))=
        ∑ k∈Finset.range D, f k := by
    simp only [chebyshevRow_coeff_rat]
    exact Fin.sum_univ_eq_sum_range f D
  rw [left,right]
  apply Finset.sum_subset (Finset.range_mono (by omega : j+1≤D))
  intro k _ hk
  have hjk : j<k := by
    have hn : ¬k<j+1 := fun h => hk (Finset.mem_range.mpr h)
    omega
  have hz : (Chebyshev.T ℚ (j:ℤ)).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (by simpa only [Chebyshev.natDegree_T,Int.natAbs_natCast] using hjk)
  simp only [f,hz,zero_mul,zero_div]

theorem antiderivative_difference (N : ℕ) (a b : ℚ) :
    b*(∑ k : Fin (profileDegree N), (antiderivativeCoefficient N k).value*(b*b)^k.val)-
      a*(∑ k : Fin (profileDegree N), (antiderivativeCoefficient N k).value*(a*a)^k.val)=
      cutoffIntegralApprox N a b := by
  simp only [antiderivativeCoefficient_value,cutoffIntegralApprox]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul,Finset.sum_div]
  have one (k : Fin (profileDegree N)) :
      b*(∑ j∈Finset.range (profileDegree N),
        (encodedCoefficient N j).value*((chebyshevRow (profileDegree N) j).get k:ℚ)*
        (4:ℚ)^k.val/(2*(k.val:ℚ)+1))*(b*b)^k.val-
      a*(∑ j∈Finset.range (profileDegree N),
        (encodedCoefficient N j).value*((chebyshevRow (profileDegree N) j).get k:ℚ)*
        (4:ℚ)^k.val/(2*(k.val:ℚ)+1))*(a*a)^k.val=
      ∑ j∈Finset.range (profileDegree N), (encodedCoefficient N j).value*
        (((chebyshevRow (profileDegree N) j).get k:ℚ)*(4:ℚ)^k.val*
          (b^(2*k.val+1)-a^(2*k.val+1))/(2*(k.val:ℚ)+1)) := by
    rw [Finset.mul_sum,Finset.sum_mul,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show b*b=b^2 by ring,show a*a=a^2 by ring,← pow_mul,← pow_mul,pow_succ,pow_succ]
    ring
  simp_rw [← mul_assoc,one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [squareIntegral_full _ _ (Finset.mem_range.mp hj),Finset.mul_sum]

#print axioms antiderivative_difference
#print axioms antiderivativeCoefficient_width_polynomial
end Maxwell.Continuum.Calibration.RawCutoff
