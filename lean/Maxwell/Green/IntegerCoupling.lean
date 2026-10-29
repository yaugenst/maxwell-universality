import Maxwell.Green.CalibrationIndex
import Maxwell.Green.CalibrationSupport
import Maxwell.Green.CalibrationAxial

/-! The signed-channel integer matrix algorithm computes exactly the same
rational coupling used in the physical calibration error bounds. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000
variable {n : ℕ}

def siteRadius (k : Site) : ℕ := Finset.univ.sup fun j => (k j).natAbs

theorem siteRadius_bound (k : Site) (j : Direction) : |k j| ≤ (siteRadius k : ℤ) := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast (Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j))

theorem integerStencilAction_physical_on (edges : Fin n ↪ Edge)
    (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (D : ℕ) (hD : 0 < D) (h64 : 64 ∣ D)
    (hmD : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D) (hsD : s.den ∣ D) (hs : 0 ≤ s)
    (v : SparseField) (R : ℕ) (hv : Supported v R) (N : ℕ)
    (hc : Covers edges (R+4*N+2)) :
    embed (rationalSource edges (integerStencilAction edges m z s D v N)) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed v) := by
  rw [integerStencilAction_eq_dense edges m z s D hD h64 hmD hz hsD hs,
    ← coefficients_inverse edges m K hK hm z s v R hv N hc,
    embed_reconstruction]
  · exact embed_compactInverseAction m K hK hm z s N v
  · exact (((hv.hornerAction m z s N).step m z).scale s).compact.in_cover hc

end Maxwell.Defect.FiniteStencil

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Green.PhysicalCompression
set_option maxHeartbeats 600000

/-- All loops use the explicit division/remainder enumeration of the cube.
The source and material table enter only through exact rational/integer arithmetic. -/
def integerCoupling {n : ℕ} (P : PhysicalPlatform) (edges : Fin n → Edge)
    (a : Fin n → ℚ) (k : Site) (b : ℕ) : ℚ :=
  let v := rationalSource (translateEdge k ∘ edges) a
  let R := edgeRadius edges + 20*siteRadius k
  let N := P.calibrationDegree b
  let Q := radixCubeEmbedding (R+4*N+2)
  let s := (P.rowBound^2)⁻¹
  let D := calibrationDenominator P.background.material 0 s
  pairing (rationalSource edges a)
    (rationalSource Q (integerStencilAction Q P.rationalMaterial 0 s D v N))

theorem integerCoupling_eq {n : ℕ} (P : PhysicalPlatform) (edges : Fin n → Edge)
    (a : Fin n → ℚ) (k : Site) (b : ℕ) :
    P.integerCoupling edges a k b = P.rationalCoupling edges a k b := by
  let v := rationalSource (translateEdge k ∘ edges) a
  let R := edgeRadius edges + 20*siteRadius k
  let N := P.calibrationDegree b
  let Q := radixCubeEmbedding (R+4*N+2)
  let s : ℚ := (P.rowBound^2)⁻¹
  let D := calibrationDenominator P.background.material 0 s
  obtain ⟨hD, h64, hmD, hz, hsD⟩ := calibrationDenominator_spec P.background.material 0 s
  have hv : Supported v R :=
    rationalSource_translated_supported edges a k (siteRadius k) (siteRadius_bound k)
  have hactual := integerStencilAction_physical_on Q P.rationalMaterial 25 (by norm_num)
    P.rationalMaterial_bound 0 s D hD h64 hmD hz hsD (by dsimp [s]; positivity)
    v R hv N (radixCubeEmbedding_covers _)
  apply Rat.cast_injective (α := ℂ)
  change (pairing (rationalSource edges a) (rationalSource Q
      (integerStencilAction Q P.rationalMaterial 0 s D v N)) : ℂ) =
    (pairing (rationalSource edges a) (compactInverseAction P.rationalMaterial 0 s N v) : ℂ)
  rw [pairing_inner, pairing_inner, hactual,
    embed_compactInverseAction P.rationalMaterial 25 (by norm_num) P.rationalMaterial_bound]

def integerSignedCoupling (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (k : Site) (b : ℕ) : ℚ :=
  -P.integerCoupling (ScalarDefect.edgeEmbedding P.defect) a k b

theorem integerSignedCoupling_eq (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (k : Site) (b : ℕ) :
    P.integerSignedCoupling a k b = P.signedCoupling a k b := by
  rw [integerSignedCoupling, P.integerCoupling_eq]
  rfl

/-- The bit-machine's integer numerator and explicit denominator have the
proved requested error against the same actual physical Green coupling. -/
theorem integerSignedCoupling_requested_error (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (η : ℚ) (hη : 0 < η)
    (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤
      (1/2 : ℝ)^P.couplingPrecision η) :
    |(P.integerSignedCoupling a n (P.couplingPrecision η) : ℝ) -
      (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode))| ≤ η := by
  rw [P.integerSignedCoupling_eq]
  exact P.signedCoupling_requested_error a n η hη ha

end Maxwell.Composition.PhysicalPlatform
