import Maxwell.Continuum.ComplexDyadic
import Mathlib.Algebra.BigOperators.Fin

/-! Exact arithmetic on the actual stored complex fixed-point words. -/

namespace Maxwell.Continuum

def complexDyadicMul {P R : ℕ} (a : ComplexDyadic P) (b : ComplexDyadic R) : ComplexDyadic (P+R) :=
  (⟨a.1.numerator*b.1.numerator-a.2.numerator*b.2.numerator⟩,
   ⟨a.1.numerator*b.2.numerator+a.2.numerator*b.1.numerator⟩)

theorem complexDyadicMul_value {P R : ℕ} (a : ComplexDyadic P) (b : ComplexDyadic R) :
    complexDyadicValue (complexDyadicMul a b)=complexDyadicValue a*complexDyadicValue b := by
  simp only [complexDyadicValue, complexDyadicMul, Dyadic.value]
  push_cast
  rw [pow_add]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

def complexDyadicSum {P : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ComplexDyadic P) : ComplexDyadic P :=
  (⟨∑ i ∈ s, (f i).1.numerator⟩, ⟨∑ i ∈ s, (f i).2.numerator⟩)

theorem complexDyadicSum_value {P : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ComplexDyadic P) :
    complexDyadicValue (complexDyadicSum s f)=∑ i ∈ s, complexDyadicValue (f i) := by
  simp only [complexDyadicValue, complexDyadicSum, Dyadic.value]
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]

def complexDyadicTriple {P : ℕ} (a : Fin 3 → ComplexDyadic P) : ComplexDyadic (P+P+P) :=
  complexDyadicMul (complexDyadicMul (a 0) (a 1)) (a 2)

theorem complexDyadicTriple_value {P : ℕ} (a : Fin 3 → ComplexDyadic P) :
    complexDyadicValue (complexDyadicTriple a)=∏ i, complexDyadicValue (a i) := by
  simp only [complexDyadicTriple, complexDyadicMul_value, Fin.prod_univ_three]

#print axioms complexDyadicMul_value
#print axioms complexDyadicTriple_value

end Maxwell.Continuum
