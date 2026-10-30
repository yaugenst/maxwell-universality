import Maxwell.Continuum.CalibrationRationalValue
import Maxwell.Continuum.CalibrationScaledSchur

/-! Executable rational central and off-diagonal blocks of the literal
24-dimensional Schur construction. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalBlockMatrix (t E : ℚ) (a : Fin 3 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (t^2*(∑ j, a j^2)-E) • 1-Matrix.vecMulVec (fun j => t*a j) (fun j => t*a j)

theorem rationalBlockMatrix_sound (t E : ℚ) (a : Fin 3 → ℚ) :
    (rationalBlockMatrix t E a).map (Rat.castHom ℂ) =
      blockMatrix (realMomentum (fun j => (t : ℝ)*(a j : ℝ))) (E : ℂ) := by
  ext i j
  change ((rationalBlockMatrix t E a i j : ℚ) : ℂ) = _
  simp only [rationalBlockMatrix, blockMatrix, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, momentumSquare, momentumOuter, realMomentum, smul_eq_mul,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_sum, Complex.ofReal_mul,
    Complex.ofReal_ratCast, Matrix.one_apply]
  split_ifs <;> push_cast <;> simp only [mul_pow, ← Finset.mul_sum]

def rationalCentral {V : Type*} [Zero V] (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun ν j => if rationalCentralCheck ν then f ν j else 0

def rationalCentralApply {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun ν i => if rationalCentralCheck ν then
    ∑ j : Fin 3, rationalBlockMatrix t E (rationalDirection r ν) i j • f ν j else 0

def rationalCentralMaterial {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalCentralApply t E r f-rationalAmplitude • rationalCentral (rationalPotential (rationalCentral f))

def rationalRightCoupling {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  -rationalAmplitude • rationalNoncentral (rationalPotential (rationalCentral f))

def rationalLeftCoupling {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  -rationalAmplitude • rationalCentral (rationalPotential (rationalNoncentral f))

theorem represents_central {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalCentral f) (centralAliasProjection u) := by
  intro ν j
  rw [centralAliasProjection_apply]
  unfold rationalCentral
  by_cases hν : IsCentralAlias ν
  · have hb := (rationalCentralCheck_true ν).mpr hν
    simp only [hν, hb, ↓reduceIte]
    exact hf ν j
  · have hb : rationalCentralCheck ν = false := Bool.eq_false_iff.mpr
      (fun h => hν ((rationalCentralCheck_true ν).mp h))
    simp only [hν, hb, Bool.false_eq_true, ↓reduceIte]
    exact map_zero rationalComplexLinear

theorem represents_centralApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalCentralApply t E r f) (scaledCentralFree t E (fun j => (r j : ℝ)) hr ht hE u) := by
  intro ν i
  change rationalComplexValue (rationalCentralApply t E r f ν i) =
    scaledCentralFreeBlock t E (fun j => (r j : ℝ)) ν (u ν) i
  unfold rationalCentralApply scaledCentralFreeBlock
  by_cases hν : IsCentralAlias ν
  · have hb := (rationalCentralCheck_true ν).mpr hν
    simp only [hν, hb, ↓reduceIte]
    have hm := rationalBlockMatrix_sound t E (rationalDirection r ν)
    have hb' : block (realMomentum (fun j => (t : ℝ)*gridDirection (fun j => (r j : ℝ)) ν j)) (E : ℂ) =
        matrixCLM ((rationalBlockMatrix t E (rationalDirection r ν)).map (Rat.castHom ℂ)) := by
      rw [hm]
      unfold block
      simp only [rationalDirection, gridDirection, Rat.cast_add, Rat.cast_intCast,
        Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [Complex.ofReal_ratCast]
    rw [hb']
    change rationalComplexLinear (∑ j : Fin 3, rationalBlockMatrix t E (rationalDirection r ν) i j • f ν j) = _
    simp only [map_sum, map_smul]
    simp_rw [← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul]
    change (∑ j : Fin 3, (rationalBlockMatrix t E (rationalDirection r ν) i j : ℂ)*rationalComplexValue (f ν j)) =
      ∑ j : Fin 3, (rationalBlockMatrix t E (rationalDirection r ν) i j : ℂ)*u ν j
    apply Finset.sum_congr rfl
    intro j _
    rw [hf]
  · have hb : rationalCentralCheck ν = false := Bool.eq_false_iff.mpr
      (fun h => hν ((rationalCentralCheck_true ν).mp h))
    simp only [hν, hb, Bool.false_eq_true, ↓reduceIte, zero_apply]
    exact map_zero rationalComplexLinear

theorem represents_centralMaterial (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalCentralMaterial t E r f) (scaledCentralMaterial t E (fun j => (r j : ℝ)) hr ht hE u) := by
  have h := represents_sub (represents_centralApply t E r hr ht hE hf)
    (represents_smul rationalAmplitude (represents_central (represents_potential (represents_central hf))))
  rw [rationalAmplitude_complex] at h
  exact h

theorem represents_rightCoupling {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalRightCoupling f) (calibrationRightCoupling u) := by
  have h := represents_smul (-rationalAmplitude)
    (represents_noncentral (represents_potential (represents_central hf)))
  rw [Rat.cast_neg, rationalAmplitude_complex] at h
  exact h

theorem represents_leftCoupling {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalLeftCoupling f) (calibrationLeftCoupling u) := by
  have h := represents_smul (-rationalAmplitude)
    (represents_central (represents_potential (represents_noncentral hf)))
  rw [Rat.cast_neg, rationalAmplitude_complex] at h
  exact h

#print axioms represents_centralMaterial
#print axioms represents_rightCoupling

end Maxwell.Continuum.Calibration
