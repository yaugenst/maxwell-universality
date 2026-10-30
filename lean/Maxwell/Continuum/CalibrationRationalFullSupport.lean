import Maxwell.Continuum.CalibrationRationalFull
import Maxwell.Continuum.CalibrationRationalSupport

/-! Literal finite support of every executable full-inverse output.
The central solve inserts only the eight central aliases; the other
terms propagate through the proved finite-range Neumann stencil. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem centralAlias_abs_le {ν : Alias} (hν : IsCentralAlias ν) (j : Fin 3) :
    |ν j| ≤ (1 : ℤ) := by
  rcases hν j with h | h <;> rw [h] <;> norm_num

omit [Module ℚ V] in
theorem rationalCentral_supported (f : Alias → Fin 3 → V) : RationalSupported (rationalCentral f) 1 := by
  intro ν hν i
  have hn : rationalCentralCheck ν = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨j,hj⟩ := hν
    exact (not_lt_of_ge (centralAlias_abs_le ((rationalCentralCheck_true ν).mp h) j)) hj
  simp only [rationalCentral,hn,Bool.false_eq_true,↓reduceIte]

omit [Module ℚ V] in
theorem RationalSupported.central {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalCentral f) R := by
  intro ν hν i
  unfold rationalCentral
  split_ifs
  · exact hf ν hν i
  · rfl

omit [Module ℚ V] in
theorem RationalSupported.add {f g : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (hg : RationalSupported g R) : RationalSupported (f+g) R := by
  intro ν hν i
  change f ν i+g ν i = 0
  rw [hf ν hν i,hg ν hν i,add_zero]

theorem rationalRightCoupling_supported (f : Alias → Fin 3 → V) :
    RationalSupported (rationalRightCoupling f) 2 :=
  (rationalCentral_supported f).potential.noncentral.smul _

theorem RationalSupported.rightCoupling {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalRightCoupling f) (R+1) :=
  hf.central.potential.noncentral.smul _

theorem rationalLeftCoupling_supported (f : Alias → Fin 3 → V) :
    RationalSupported (rationalLeftCoupling f) 1 :=
  (rationalCentral_supported _).smul _

theorem RationalSupported.complementApply {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) :
    RationalSupported (rationalComplementApply t E r K f) (R+K) :=
  hf.noncentral.inverseApply t E r K

theorem rationalLiftApply_supported (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ)
    (f : Alias → Fin 3 → V) : RationalSupported (rationalLiftApply t E r K f) (K+2) := by
  apply ((rationalCentral_supported f).mono (by omega)).sub
  simpa only [Nat.add_comm 2 K] using
    (rationalRightCoupling_supported f).complementApply t E r K

theorem RationalSupported.fullApply {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) :
    RationalSupported (rationalFullApply t E r K f) (R+K+2) :=
  ((hf.complementApply t E r K).mono (by omega)).add
    ((rationalLiftApply_supported t E r K _).mono (by omega))

#print axioms RationalSupported.fullApply

end Maxwell.Continuum.Calibration
