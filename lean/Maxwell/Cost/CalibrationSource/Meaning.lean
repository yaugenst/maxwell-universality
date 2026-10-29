import Maxwell.Cost.CalibrationSource.IndexMachine
import Maxwell.Cost.CalibrationMatrix.SourceInit.Meaning

namespace Maxwell.Cost.CalibrationSource
open Defect.FiniteStencil Spectral Spectral.Lattice
open Green.PhysicalCompression
open CalibrationMatrix
set_option maxHeartbeats 1000000

/-- Actual signed integer coefficients with one shared positive denominator.
No product of separately reduced denominators is needed by the machine. -/
def rationalCoefficients {m : ℕ} (a : Channels m) (D : ℕ) : Fin m → ℚ :=
  fun i => (a.value i : ℚ)/(D : ℚ)

def records {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (d N : ℕ)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (a : Channels m) : SourceInit.Records m (3*cubeWidth (radius R0 L d N)^3) where
  index i := ⟨address R0 L v (edges i) d N,address_lt R0 L v (edges i) d N (he i) hv⟩
  positive := a.positive
  negative := a.negative

theorem records_edge {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (d N : ℕ)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (a : Channels m) (i : Fin m) :
    radixCubeEmbedding (radius R0 L d N) ((records R0 L v edges d N he hv a).index i) =
      translateEdge ((d : ℤ) • v) (edges i) :=
  address_edge R0 L v (edges i) d N (he i) hv

/-- Scattering the physically produced source records gives the exact
finite coefficients of the translated rational source on the real cube. -/
theorem records_scaled {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (d N : ℕ)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (a : Channels m) (D : ℕ) (hD : 0 < D)
    (i : Fin (3*cubeWidth (radius R0 L d N)^3)) :
    ((SourceInit.values (records R0 L v edges d N he hv a) m).value i : ℚ) =
      (D : ℚ)*coefficients (radixCubeEmbedding (radius R0 L d N))
        (rationalSource (translateEdge ((d : ℤ) • v) ∘ edges) (rationalCoefficients a D)) i := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have h := SourceInit.values_scaled (records R0 L v edges d N he hv a)
    (radixCubeEmbedding (radius R0 L d N)) (rationalCoefficients a D) D
    (by intro j; change (a.value j : ℚ) = _; exact (mul_div_cancel₀ (a.value j : ℚ) hd).symm) i
  have heq : (fun j => radixCubeEmbedding (radius R0 L d N)
      ((records R0 L v edges d N he hv a).index j)) = translateEdge ((d : ℤ) • v) ∘ edges := by
    funext j
    exact records_edge R0 L v edges d N he hv a j
  simpa only [heq] using h

/-- Reuse a selected rational vector's actual common-denominator storage. -/
theorem records_scaled_of_coefficients {m : ℕ} (R0 L : ℕ) (v : Site)
    (edges : Fin m → Edge) (d N : ℕ)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (a : Channels m) (q : Fin m → ℚ) (D : ℕ) (hD : 0 < D)
    (ha : ∀ j, (a.value j : ℚ) = (D : ℚ)*q j)
    (i : Fin (3*cubeWidth (radius R0 L d N)^3)) :
    ((SourceInit.values (records R0 L v edges d N he hv a) m).value i : ℚ) =
      (D : ℚ)*coefficients (radixCubeEmbedding (radius R0 L d N))
        (rationalSource (translateEdge ((d : ℤ) • v) ∘ edges) q) i := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hq : rationalCoefficients a D = q := by
    funext j
    simp [rationalCoefficients,ha j,hd]
  simpa only [hq] using records_scaled R0 L v edges d N he hv a D hD i

end Maxwell.Cost.CalibrationSource
