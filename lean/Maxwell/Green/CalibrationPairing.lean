import Maxwell.Green.IntegerCoupling
import Maxwell.Cost.CalibrationMatrix.Pairing

/-! The serialized signed-channel dot product is the actual finite-source
coupling used by the Green calibration theorem. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice Cost.CalibrationMatrix
open scoped BigOperators
set_option maxHeartbeats 600000
variable {n : ℕ}

theorem evaluate_rationalSource (edges : Fin n ↪ Edge) (a : Fin n → ℚ) (i : Fin n) :
    evaluate (rationalSource edges a) (edges i) = a i := by
  simp only [evaluate,rationalSource,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  simp [edges.injective.eq_iff]

theorem pairing_rationalSource (edges : Fin n ↪ Edge) (a b : Fin n → ℚ) :
    pairing (rationalSource edges a) (rationalSource edges b) = ∑ i, a i*b i := by
  simp only [pairing,rationalSource,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  change (∑ i, a i*evaluate (rationalSource edges b) (edges i)) = _
  simp only [evaluate_rationalSource]

theorem pairing_coefficients (edges : Fin n ↪ Edge) (u : SparseField) (a : Fin n → ℚ)
    (hu : ∀ t ∈ u, t.1 ∈ Set.range edges) :
    pairing u (rationalSource edges a) = ∑ i, coefficients edges u i*a i := by
  rw [← pairing_rationalSource edges (coefficients edges u) a]
  apply Rat.cast_injective (α := ℂ)
  rw [pairing_inner,pairing_inner,embed_reconstruction edges u hu]

theorem channelPairing_value (x y : Channels n) (u v : Fin n → ℚ) (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V)
    (hx : ∀ i, (x.value i : ℚ) = (U : ℚ)*u i)
    (hy : ∀ i, (y.value i : ℚ) = (V : ℚ)*v i) :
    (Pairing.output (Pairing.positive x y) (Pairing.negative x y) (U*V)
      (Nat.mul_pos hU hV)).value = ∑ i, u i*v i := by
  rw [Pairing.output_value,Nat.cast_mul]
  have hnum : (∑ i, (x.value i : ℚ)*(y.value i : ℚ)) =
      ((U : ℚ)*(V : ℚ))*(∑ i, u i*v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx,hy]
    ring
  rw [hnum]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem integerPairing_value (edges : Fin n ↪ Edge) (u : SparseField)
    (a : Fin n → ℚ) (y : Channels n) (V : ℕ) (hV : 0 < V)
    (hu : ∀ t ∈ u, t.1 ∈ Set.range edges)
    (hy : ∀ i, (y.value i : ℚ) = (V : ℚ)*a i) :
    let x := integerSource (coefficients edges u) (sourceDenominator u)
    (Pairing.output (Pairing.positive x y) (Pairing.negative x y)
      (sourceDenominator u*V) (Nat.mul_pos (sourceDenominator_pos u) hV)).value =
      pairing u (rationalSource edges a) := by
  rw [pairing_coefficients edges u a hu]
  apply channelPairing_value _ _ _ _ _ _ (sourceDenominator_pos u) hV _ hy
  exact integerSource_scaled _ _ (fun i => (has_sourceDenominator u).evaluate (edges i))

theorem integerStencilPairing_value (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (z s : ℚ) (D : ℕ) (hD : 0 < D) (u v : SparseField) (N : ℕ)
    (hu : ∀ t ∈ u, t.1 ∈ Set.range edges) :
    let x := integerSource (coefficients edges u) (sourceDenominator u)
    let y := inverseNumerator (integerMatrix (stencilMatrix edges m z) (D^2)) (D^2)
      (integerScale s (D^2)) (integerSource (coefficients edges v) (sourceDenominator v)) N
    (Pairing.output (Pairing.positive x y) (Pairing.negative x y)
      (sourceDenominator u*(sourceDenominator v*(D^2)^(3*N+2)))
      (by have := sourceDenominator_pos u; have := sourceDenominator_pos v; positivity)).value =
      pairing u (rationalSource edges (integerStencilAction edges m z s D v N)) := by
  apply integerPairing_value edges u _ _ _
    (by have := sourceDenominator_pos v; positivity) hu
  intro i
  simp only [integerStencilAction,Nat.cast_mul,Nat.cast_pow]
  have hden : (sourceDenominator v : ℚ)*((D^2 : ℕ) : ℚ)^(3*N+2) ≠ 0 := by
    have := sourceDenominator_pos v
    positivity
  rw [Nat.cast_pow] at hden
  exact (mul_div_cancel₀ _ hden).symm

end Maxwell.Defect.FiniteStencil

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Green.PhysicalCompression Maxwell.Cost.CalibrationMatrix
set_option maxHeartbeats 600000

def integerCouplingOutput {n : ℕ} (P : PhysicalPlatform) (edges : Fin n → Edge)
    (a : Fin n → ℚ) (k : Site) (b : ℕ) : Maxwell.Codec.RationalPair :=
  let u := rationalSource edges a
  let v := rationalSource (translateEdge k ∘ edges) a
  let N := P.calibrationDegree b
  let Q := radixCubeEmbedding (edgeRadius edges+20*siteRadius k+4*N+2)
  let s := (P.rowBound^2)⁻¹
  let D := calibrationDenominator P.background.material 0 s
  let x := integerSource (coefficients Q u) (sourceDenominator u)
  let y := inverseNumerator (integerMatrix (stencilMatrix Q P.rationalMaterial 0) (D^2))
    (D^2) (integerScale s (D^2)) (integerSource (coefficients Q v) (sourceDenominator v)) N
  Pairing.output (Pairing.positive x y) (Pairing.negative x y)
    (sourceDenominator u*(sourceDenominator v*(D^2)^(3*N+2)))
    (by
      have := sourceDenominator_pos u
      have := sourceDenominator_pos v
      have := (calibrationDenominator_spec P.background.material 0 s).1
      positivity)

theorem integerCouplingOutput_value {n : ℕ} (P : PhysicalPlatform) (edges : Fin n → Edge)
    (a : Fin n → ℚ) (k : Site) (b : ℕ) :
    (P.integerCouplingOutput edges a k b).value = P.integerCoupling edges a k b := by
  let u := rationalSource edges a
  let Q := radixCubeEmbedding (edgeRadius edges+20*siteRadius k+4*P.calibrationDegree b+2)
  have hu : ∀ t ∈ u, t.1 ∈ Set.range Q :=
    (rationalSource_supported edges a).in_cover ((radixCubeEmbedding_covers _).mono (by omega))
  exact integerStencilPairing_value Q P.rationalMaterial 0 ((P.rowBound^2)⁻¹)
    (calibrationDenominator P.background.material 0 ((P.rowBound^2)⁻¹))
    (calibrationDenominator_spec P.background.material 0 ((P.rowBound^2)⁻¹)).1
    u (rationalSource (translateEdge k ∘ edges) a) (P.calibrationDegree b) hu

theorem integerCouplingOutput_physical {n : ℕ} (P : PhysicalPlatform) (edges : Fin n → Edge)
    (a : Fin n → ℚ) (k : Site) (b : ℕ) :
    (P.integerCouplingOutput edges a k b).value = P.rationalCoupling edges a k b := by
  rw [P.integerCouplingOutput_value,P.integerCoupling_eq]

end Maxwell.Composition.PhysicalPlatform
