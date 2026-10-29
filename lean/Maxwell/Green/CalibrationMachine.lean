import Maxwell.Cost.CalibrationMatrix.Horner.Calibration
import Maxwell.Green.CalibrationPairing

/-! Exact semantic value of the literal rational pair emitted by the finite
calibration program, including unreduced signed source channels. -/
namespace Maxwell.Defect.FiniteStencil
open Cost.CalibrationMatrix
open scoped Matrix BigOperators

/-- Unreduced source channels are enough: the physical zero/scatter input
initializer need not perform sign cancellation before the inverse loop. -/
theorem machineCalibration_value {n : ℕ} (A : ChannelMatrix n) (D S U V : ℕ)
    (source left : Channels n) (N : ℕ) (hD : 0 < D) (hU : 0 < U) (hV : 0 < V)
    (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (u v : Fin n → ℚ)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ)^2*H i j)
    (hs : (S : ℚ) = (D : ℚ)^2*s)
    (hu : ∀ i, (left.value i : ℚ) = (U : ℚ)*u i)
    (hv : ∀ i, (source.value i : ℚ) = (V : ℚ)*v i) :
    (Pairing.output (Pairing.positive left (inverseNumerator A (D^2) S source N))
      (Pairing.negative left (inverseNumerator A (D^2) S source N))
      (Horner.Denominator.value D U V N) (Horner.Denominator.value_pos hD hU hV)).value =
      ∑ i, u i*denseInverse H s v N i := by
  have hy : ∀ i, ((inverseNumerator A (D^2) S source N).value i : ℚ) =
      ((V*(D^2)^(3*N+2) : ℕ) : ℚ)*denseInverse H s v N i := by
    intro i
    rw [Nat.cast_mul,Nat.cast_pow]
    exact channelInverse_scaled A (D^2) S V source H s v
      (fun i j => by simpa only [Nat.cast_pow] using hA i j)
      (by simpa only [Nat.cast_pow] using hs) hv N i
  have hh := channelPairing_value left (inverseNumerator A (D^2) S source N)
    u (denseInverse H s v N) U (V*(D^2)^(3*N+2)) hU (by positivity) hu hy
  simpa only [Horner.Denominator.value,Nat.mul_assoc] using hh

/-- For a finite lattice cube, the emitted scalar is exactly the source
pairing of the dense inverse polynomial. Per-record source accumulation may
contain duplicates and unreduced opposite-sign contributions. -/
theorem machineCalibration_pairing {n : ℕ} (Q : Fin n ↪ Spectral.Lattice.Edge)
    (m : Spectral.Lattice.Edge → ℚ) (z s : ℚ) (A : ChannelMatrix n) (D S U V : ℕ)
    (source left : Channels n) (u v : SparseField) (N : ℕ)
    (hD : 0 < D) (hU : 0 < U) (hV : 0 < V)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ)^2*stencilMatrix Q m z i j)
    (hs : (S : ℚ) = (D : ℚ)^2*s)
    (hu : ∀ i, (left.value i : ℚ) = (U : ℚ)*coefficients Q u i)
    (hv : ∀ i, (source.value i : ℚ) = (V : ℚ)*coefficients Q v i)
    (hucover : ∀ t ∈ u, t.1 ∈ Set.range Q) :
    (Pairing.output (Pairing.positive left (inverseNumerator A (D^2) S source N))
      (Pairing.negative left (inverseNumerator A (D^2) S source N))
      (Horner.Denominator.value D U V N) (Horner.Denominator.value_pos hD hU hV)).value =
      pairing u (rationalSource Q (denseInverse (stencilMatrix Q m z) s (coefficients Q v) N)) := by
  rw [pairing_coefficients Q u _ hucover]
  exact machineCalibration_value A D S U V source left N hD hU hV
    (stencilMatrix Q m z) s (coefficients Q u) (coefficients Q v) hA hs hu hv

end Maxwell.Defect.FiniteStencil
