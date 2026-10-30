import Maxwell.Continuum.CalibrationFiniteData

/-! Exact rational inner products of the computed Fourier arrays.
The finite sum is identified with the inner product on the complete
alias Hilbert space, including every coefficient of the second vector. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber PeriodicSampling

def rationalComplexInner (a b : RationalComplex) : RationalComplex :=
  (a.1*b.1+a.2*b.2,a.1*b.2-a.2*b.1)

theorem rationalComplexInner_value (a b : RationalComplex) :
    rationalComplexValue (rationalComplexInner a b) =
      inner ℂ (rationalComplexValue a) (rationalComplexValue b) := by
  apply Complex.ext <;>
    simp [rationalComplexInner,rationalComplexValue_eq,RCLike.inner_apply,
      Complex.mul_re,Complex.mul_im] <;> ring

def rationalInner (f g : RationalAliasField) (R : ℕ) : RationalComplex :=
  ∑ ν ∈ Product.frequencyCube R, ∑ j : Fin 3, rationalComplexInner (f ν j) (g ν j)

theorem rationalInner_eq {f g : RationalAliasField} {u v : FiberSpace} {R : ℕ}
    (hf : RationalSupported f R) (hu : Represents f u) (hv : Represents g v) :
    rationalComplexValue (rationalInner f g R) = inner ℂ u v := by
  have hzero : ∀ ν, ν ∉ Product.frequencyCube R → u ν = 0 := by
    intro ν hν
    have he := represents_unique hu (representedFiber_represents f hf)
    rw [he]
    exact fieldValue_zero hf ν hν
  rw [lp.inner_eq_tsum]
  have ht : (∑' ν : Alias, inner ℂ (u ν) (v ν)) =
      ∑ ν ∈ Product.frequencyCube R, inner ℂ (u ν) (v ν) := by
    apply tsum_eq_sum
    intro ν hν
    rw [hzero ν hν,inner_zero_left]
  rw [ht]
  change rationalComplexLinear (∑ ν ∈ Product.frequencyCube R,
    ∑ j : Fin 3, rationalComplexInner (f ν j) (g ν j)) = _
  simp only [map_sum,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro j _
  exact (rationalComplexInner_value (f ν j) (g ν j)).trans (by rw [hu,hv])

namespace FourierData

def innerPair (v w : FourierData) : RationalComplex := rationalInner v.field w.field v.radius

theorem innerPair_value (v w : FourierData) :
    rationalComplexValue (innerPair v w) = inner ℂ v.value w.value :=
  rationalInner_eq v.supported v.represents w.represents

def realInner (v w : FourierData) : ℚ := (innerPair v w).1

theorem realInner_eq (v w : FourierData) :
    (realInner v w : ℝ) = (inner ℂ v.value w.value).re := by
  rw [← innerPair_value]
  simp only [rationalComplexValue_eq,Complex.add_re,Complex.ratCast_re,
    Complex.mul_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,realInner]

def rayleigh (v w : FourierData) : ℚ := v.realInner w/v.normSq

theorem rayleigh_eq (v w : FourierData) :
    (rayleigh v w : ℝ) = (inner ℂ v.value w.value).re/‖v.value‖^2 := by
  rw [rayleigh,Rat.cast_div,realInner_eq,normSq_eq]

#print axioms innerPair_value
#print axioms rayleigh_eq

end FourierData
end Maxwell.Continuum.Calibration
