import Maxwell.Continuum.CalibrationCachedSchur

/-! Materialized full-inverse applications. Both Neumann applications
and every central Schur column use cached finite arrays; the dense
rational inverse remains fixed at dimension 24. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def cachedFullApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (R K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  let B := R+K+2
  let c := extendAliasArray B (cachedInverseApply t E r B (rationalNoncentral f) K)
  let x := rationalCentralMatrixApply (rationalMatrixInverse (cachedSchurMatrix t E r K))
    (f-rationalLeftCoupling c)
  let d := extendAliasArray B (cachedInverseApply t E r B (rationalNoncentral (rationalRightCoupling x)) K)
  c+(rationalCentral x-d)

theorem cachedFullApply_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (R K : ℕ) {f : Alias → Fin 3 → V}
    (hf : RationalSupported f R) : cachedFullApply t E r R K f = rationalFullApply t E r K f := by
  unfold cachedFullApply
  dsimp only
  rw [cachedInverseApply_exact t E r hf.noncentral (R+K+2) K (by omega),cachedSchurMatrix_eq]
  rw [cachedInverseApply_exact t E r (rationalRightCoupling_supported _).noncentral (R+K+2) K (by omega)]
  rfl

def cachedFullVector {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (R K : ℕ) (f : Alias → Fin 3 → V) : Vector V (aliasArraySize (R+K+2)) :=
  let B := R+K+2
  let ca := cachedInverseApply t E r B (rationalNoncentral f) K
  let c := extendAliasArray B ca
  let x := rationalCentralMatrixApply (rationalMatrixInverse (cachedSchurMatrix t E r K))
    (f-rationalLeftCoupling c)
  let da := cachedInverseApply t E r B (rationalNoncentral (rationalRightCoupling x)) K
  sampleAliasArray B (c+(rationalCentral x-extendAliasArray B da))

theorem cachedFullVector_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (R K : ℕ) {f : Alias → Fin 3 → V}
    (hf : RationalSupported f R) :
    extendAliasArray (R+K+2) (cachedFullVector t E r R K f) = rationalFullApply t E r K f := by
  change extendAliasArray (R+K+2) (sampleAliasArray (R+K+2) (cachedFullApply t E r R K f)) = _
  rw [cachedFullApply_eq t E r R K hf]
  exact extend_sample_supported (hf.fullApply t E r K)

#print axioms cachedFullVector_eq

end Maxwell.Continuum.Calibration
