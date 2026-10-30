import Maxwell.Continuum.CalibrationRationalConvolution
import Maxwell.Continuum.CalibrationSupercellUnitary

/-! Finite rational Fourier vectors as actual vectors in the complete
Hilbert space. Their exact norm is a computed finite rational sum. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber PeriodicSampling

def rationalNormSq (f : RationalAliasField) (R : ℕ) : ℚ :=
  ∑ ν ∈ Product.frequencyCube R, ∑ j : Fin 3, ((f ν j).1^2+(f ν j).2^2)

theorem rationalNormSq_nonneg (f : RationalAliasField) (R : ℕ) : 0 ≤ rationalNormSq f R := by
  unfold rationalNormSq
  positivity

noncomputable section
set_option backward.isDefEq.respectTransparency false

def fieldValue (f : RationalAliasField) : Alias → Polarization :=
  fun ν => WithLp.toLp 2 (fun j => rationalComplexValue (f ν j))

theorem fieldValue_zero {f : RationalAliasField} {R : ℕ} (hf : RationalSupported f R)
    (ν : Alias) (hν : ν ∉ Product.frequencyCube R) : fieldValue f ν = 0 := by
  have hout : ∃ j, (R : ℤ) < |ν j| := by
    simpa only [Product.mem_frequencyCube,not_forall,not_le] using hν
  apply PiLp.ext
  intro j
  change rationalComplexValue (f ν j) = 0
  rw [hf ν hout j]
  exact map_zero rationalComplexLinear

theorem fieldValue_mem {f : RationalAliasField} {R : ℕ} (hf : RationalSupported f R) :
    Memℓp (fieldValue f) 2 := by
  apply Memℓp.of_exponent_ge (q := 0) _ (by positivity)
  apply memℓp_zero
  apply (Product.frequencyCube R).finite_toSet.subset
  intro ν hν
  by_contra hn
  exact hν (fieldValue_zero hf ν hn)

def representedFiber (f : RationalAliasField) {R : ℕ} (hf : RationalSupported f R) : FiberSpace :=
  ⟨fieldValue f,fieldValue_mem hf⟩

theorem representedFiber_represents (f : RationalAliasField) {R : ℕ} (hf : RationalSupported f R) :
    Represents f (representedFiber f hf) := fun _ _ => rfl

theorem representedFiber_supported (f : RationalAliasField) {R : ℕ} (hf : RationalSupported f R) :
    AliasSupported (representedFiber f hf) R := by
  intro ν hν
  apply PiLp.ext
  intro j
  change rationalComplexValue (f ν j) = 0
  rw [hf ν hν j]
  exact map_zero rationalComplexLinear

theorem represents_unique {f : RationalAliasField} {u v : FiberSpace}
    (hu : Represents f u) (hv : Represents f v) : u = v := by
  apply lp.ext
  funext ν
  apply PiLp.ext
  intro j
  exact (hu ν j).symm.trans (hv ν j)

theorem rationalComplexValue_norm_sq (a : RationalComplex) :
    ‖rationalComplexValue a‖^2 = ((a.1^2+a.2^2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm,rationalComplexValue_eq]
  simp [Complex.normSq_apply,pow_two]

theorem rationalNormSq_eq {f : RationalAliasField} {u : FiberSpace} {R : ℕ}
    (hf : RationalSupported f R) (hu : Represents f u) : (rationalNormSq f R : ℝ) = ‖u‖^2 := by
  have hid := represents_unique hu (representedFiber_represents f hf)
  rw [hid,Supercell.square_norm]
  have ht : (∑' ν : Alias, ‖representedFiber f hf ν‖^2) =
      ∑ ν ∈ Product.frequencyCube R, ‖representedFiber f hf ν‖^2 := by
    apply tsum_eq_sum
    intro ν hν
    change ‖fieldValue f ν‖^2 = 0
    rw [fieldValue_zero hf ν hν,norm_zero,zero_pow (by decide)]
  rw [ht]
  simp only [rationalNormSq,Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  exact (rationalComplexValue_norm_sq (f ν j)).symm

#print axioms rationalNormSq_eq

end
end Maxwell.Continuum.Calibration
