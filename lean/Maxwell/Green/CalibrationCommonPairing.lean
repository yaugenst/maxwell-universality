import Maxwell.Green.CalibrationPairing
import Maxwell.Cost.CalibrationSource.Meaning

/-! Physical pairing for actual scattered signed coefficients carrying their
original shared denominator. No product of reduced source denominators is used. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice Cost.CalibrationMatrix
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {n : ℕ}

/-- The exact rational output of the signed inverse and dot-product machine,
using the two actual common source denominators. -/
def commonPairingOutput (A : ChannelMatrix n) (D S U V : ℕ) (left right : Channels n)
    (N : ℕ) (hD : 0 < D) (hU : 0 < U) (hV : 0 < V) : Maxwell.Codec.RationalPair :=
  let y := inverseNumerator A D S right N
  Pairing.output (Pairing.positive left y) (Pairing.negative left y)
    (U*(V*D^(3*N+2))) (by positivity)

theorem commonPairingOutput_value (A : ChannelMatrix n) (D S U V : ℕ) (left right : Channels n)
    (N : ℕ) (hD : 0 < D) (hU : 0 < U) (hV : 0 < V)
    (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (u v : Fin n → ℚ)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ)*H i j)
    (hs : (S : ℚ) = (D : ℚ)*s)
    (hu : ∀ i, (left.value i : ℚ) = (U : ℚ)*u i)
    (hv : ∀ i, (right.value i : ℚ) = (V : ℚ)*v i) :
    (commonPairingOutput A D S U V left right N hD hU hV).value =
      ∑ i, u i*denseInverse H s v N i := by
  apply channelPairing_value left (inverseNumerator A D S right N)
    u (denseInverse H s v N) U (V*D^(3*N+2)) hU (by positivity) hu
  intro i
  simpa only [Nat.cast_mul,Nat.cast_pow] using
    channelInverse_scaled A D S V right H s v hA hs hv N i

/-- Any containing finite section gives the exact infinite-lattice
inverse-polynomial pairing when it includes the complete propagated support. -/
theorem densePairing_physical (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (u v : SparseField) (R N : ℕ) (hv : Supported v R)
    (hc : Covers edges (R+4*N+2)) :
    pairing u (rationalSource edges (denseInverse (stencilMatrix edges m z) s (coefficients edges v) N)) =
      pairing u (compactInverseAction m z s N v) := by
  rw [← coefficients_inverse edges m K hK hm z s v R hv N hc]
  apply Rat.cast_injective (α := ℂ)
  rw [pairing_inner,pairing_inner,embed_reconstruction]
  exact (((hv.hornerAction m z s N).step m z).scale s).compact.in_cover hc

/-- Exact scalar physical binding for arbitrary signed sources whose actual
stored values use common denominators U and V. -/
theorem commonPairingOutput_physical (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (A : ChannelMatrix n) (D S U V : ℕ) (left right : Channels n)
    (N : ℕ) (hD : 0 < D) (hU : 0 < U) (hV : 0 < V)
    (u v : SparseField) (R : ℕ) (hv : Supported v R)
    (hc : Covers edges (R+4*N+2)) (hu : ∀ t ∈ u, t.1 ∈ Set.range edges)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ)*stencilMatrix edges m z i j)
    (hs : (S : ℚ) = (D : ℚ)*s)
    (hx : ∀ i, (left.value i : ℚ) = (U : ℚ)*coefficients edges u i)
    (hy : ∀ i, (right.value i : ℚ) = (V : ℚ)*coefficients edges v i) :
    (commonPairingOutput A D S U V left right N hD hU hV).value =
      pairing u (compactInverseAction m z s N v) := by
  rw [commonPairingOutput_value A D S U V left right N hD hU hV
    (stencilMatrix edges m z) s (coefficients edges u) (coefficients edges v) hA hs hx hy,
    ← pairing_coefficients edges u _ hu]
  exact densePairing_physical edges m K hK hm z s u v R N hv hc

/-- Concrete integer matrices produced by the stencil generator meet the
common-denominator physical pairing contract. -/
theorem integerCommonPairing_physical (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (D U V : ℕ) (left right : Channels n)
    (N : ℕ) (hD : 0 < D) (hU : 0 < U) (hV : 0 < V)
    (h64 : 64 ∣ D) (hmD : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D)
    (hsD : s.den ∣ D) (hs : 0 ≤ s)
    (u v : SparseField) (R : ℕ) (hv : Supported v R)
    (hc : Covers edges (R+4*N+2)) (hu : ∀ t ∈ u, t.1 ∈ Set.range edges)
    (hx : ∀ i, (left.value i : ℚ) = (U : ℚ)*coefficients edges u i)
    (hy : ∀ i, (right.value i : ℚ) = (V : ℚ)*coefficients edges v i) :
    (commonPairingOutput (integerMatrix (stencilMatrix edges m z) (D^2)) (D^2)
      (integerScale s (D^2)) U V left right N (by positivity) hU hV).value =
        pairing u (compactInverseAction m z s N v) := by
  apply commonPairingOutput_physical edges m K hK hm z s _ _ _ U V left right N
    (by positivity) hU hV u v R hv hc hu
  · exact integerMatrix_scaled _ _ (stencilMatrix_denominator edges m z D h64 hmD hz)
  · exact integerScale_scaled s (D^2) hs (hsD.trans (dvd_pow_self D (by decide)))
  · exact hx
  · exact hy

end Maxwell.Defect.FiniteStencil

namespace Maxwell.Cost.CalibrationSource
open Defect.FiniteStencil Spectral Spectral.Lattice CalibrationMatrix
open Maxwell.Green.PhysicalCompression
set_option maxHeartbeats 1000000

/-- Both translated supports fit the same base cube; propagation consumes
only the additional four cells per Horner iteration and two final cells. -/
theorem translated_source_supported {m : ℕ} (R0 L : ℕ) (shift : Site) (edges : Fin m → Edge)
    (d : ℕ) (a : Fin m → ℚ) (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ))
    (hv : ∀ j, |shift j| ≤ (L : ℤ)) :
    Supported (rationalSource (translateEdge ((d : ℤ) • shift) ∘ edges) a) (R0+20*L*d) := by
  intro t ht j
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  change |(edges i).2 j-20*((d : ℤ)*shift j)| ≤ _
  have hd : (0 : ℤ) ≤ d := by positivity
  have hv' := mul_le_mul_of_nonneg_left (hv j) (show (0 : ℤ) ≤ 20*d by positivity)
  calc
    _ ≤ |(edges i).2 j|+|20*((d : ℤ)*shift j)| := abs_sub _ _
    _ = |(edges i).2 j|+20*(d : ℤ)*|shift j| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hd]
      norm_num
      ring
    _ ≤ (R0 : ℤ)+20*d*L := add_le_add (he i j) hv'
    _ = _ := by push_cast; ring

/-- The actual sparse records of two independently translated sources,
scattered on one explicit cube, produce the exact physical scalar pairing
using their original two shared denominators. -/
theorem records_pairing_physical {m₁ m₂ : ℕ} (R0 L : ℕ) (leftShift rightShift : Site)
    (leftEdges : Fin m₁ → Edge) (rightEdges : Fin m₂ → Edge) (d N : ℕ)
    (hle : ∀ i j, |(leftEdges i).2 j| ≤ (R0 : ℤ)) (hlv : ∀ j, |leftShift j| ≤ (L : ℤ))
    (hre : ∀ i j, |(rightEdges i).2 j| ≤ (R0 : ℤ)) (hrv : ∀ j, |rightShift j| ≤ (L : ℤ))
    (a : Channels m₁) (b : Channels m₂) (U V : ℕ) (hU : 0 < U) (hV : 0 < V)
    (material : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(material e : ℝ)| ≤ K)
    (z s : ℚ) (D S : ℕ) (hD : 0 < D)
    (A : ChannelMatrix (3*cubeWidth (radius R0 L d N)^3))
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ)*
      stencilMatrix (radixCubeEmbedding (radius R0 L d N)) material z i j)
    (hs : (S : ℚ) = (D : ℚ)*s) :
    (commonPairingOutput A D S U V
      (SourceInit.values (records R0 L leftShift leftEdges d N hle hlv a) m₁)
      (SourceInit.values (records R0 L rightShift rightEdges d N hre hrv b) m₂)
      N hD hU hV).value =
      pairing (rationalSource (translateEdge ((d : ℤ) • leftShift) ∘ leftEdges) (rationalCoefficients a U))
        (compactInverseAction material z s N
          (rationalSource (translateEdge ((d : ℤ) • rightShift) ∘ rightEdges) (rationalCoefficients b V))) := by
  have hu := translated_source_supported R0 L leftShift leftEdges d (rationalCoefficients a U) hle hlv
  have hv := translated_source_supported R0 L rightShift rightEdges d (rationalCoefficients b V) hre hrv
  apply commonPairingOutput_physical (radixCubeEmbedding (radius R0 L d N)) material K hK hm z s A D S U V
    _ _ N hD hU hV _ _ (R0+20*L*d) hv
  · exact radixCubeEmbedding_covers _
  · exact hu.in_cover ((radixCubeEmbedding_covers _).mono (by dsimp [radius]; omega))
  · exact hA
  · exact hs
  · exact records_scaled R0 L leftShift leftEdges d N hle hlv a U hU
  · exact records_scaled R0 L rightShift rightEdges d N hre hrv b V hV


/-- Bind the same exact scalar to externally named rational coefficients,
including a selected dyadic qhat with its retained common denominator. -/
theorem records_pairing_of_coefficients {m₁ m₂ : ℕ} (R0 L : ℕ) (leftShift rightShift : Site)
    (leftEdges : Fin m₁ → Edge) (rightEdges : Fin m₂ → Edge) (d N : ℕ)
    (hle : ∀ i j, |(leftEdges i).2 j| ≤ (R0 : ℤ)) (hlv : ∀ j, |leftShift j| ≤ (L : ℤ))
    (hre : ∀ i j, |(rightEdges i).2 j| ≤ (R0 : ℤ)) (hrv : ∀ j, |rightShift j| ≤ (L : ℤ))
    (a : Channels m₁) (b : Channels m₂) (U V : ℕ) (hU : 0 < U) (hV : 0 < V)
    (qleft : Fin m₁ → ℚ) (qright : Fin m₂ → ℚ)
    (ha : ∀ i, (a.value i : ℚ) = (U : ℚ)*qleft i)
    (hb : ∀ i, (b.value i : ℚ) = (V : ℚ)*qright i)
    (material : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(material e : ℝ)| ≤ K)
    (z s : ℚ) (D S : ℕ) (hD : 0 < D)
    (A : ChannelMatrix (3*cubeWidth (radius R0 L d N)^3))
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ)*
      stencilMatrix (radixCubeEmbedding (radius R0 L d N)) material z i j)
    (hs : (S : ℚ) = (D : ℚ)*s) :
    (commonPairingOutput A D S U V
      (SourceInit.values (records R0 L leftShift leftEdges d N hle hlv a) m₁)
      (SourceInit.values (records R0 L rightShift rightEdges d N hre hrv b) m₂)
      N hD hU hV).value =
      pairing (rationalSource (translateEdge ((d : ℤ) • leftShift) ∘ leftEdges) qleft)
        (compactInverseAction material z s N
          (rationalSource (translateEdge ((d : ℤ) • rightShift) ∘ rightEdges) qright)) := by
  have hleft : rationalCoefficients a U = qleft := by
    funext i
    simp only [rationalCoefficients,ha]
    exact mul_div_cancel_left₀ _ (by positivity)
  have hright : rationalCoefficients b V = qright := by
    funext i
    simp only [rationalCoefficients,hb]
    exact mul_div_cancel_left₀ _ (by positivity)
  simpa only [hleft,hright] using records_pairing_physical R0 L leftShift rightShift leftEdges rightEdges d N
    hle hlv hre hrv a b U V hU hV material K hK hm z s D S hD A hA hs

end Maxwell.Cost.CalibrationSource

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect Maxwell.Defect.FiniteStencil
open Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationSource
open Maxwell.Green.PhysicalCompression
set_option maxHeartbeats 1200000

/-- Concrete calibrated coupling output from the actual sparse source
records and generated integer matrix, retaining the selected qhat denominator. -/
def scatteredCouplingOutput {m : ℕ} (P : PhysicalPlatform) (R0 L : ℕ)
    (shift : Site) (edges : Fin m → Edge) (d b : ℕ)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |shift j| ≤ (L : ℤ))
    (a : Channels m) (U : ℕ) (hU : 0 < U) : Maxwell.Codec.RationalPair :=
  let N := P.calibrationDegree b
  let s := (P.rowBound^2)⁻¹
  let D := calibrationDenominator P.background.material 0 s
  let Q := radixCubeEmbedding (radius R0 L d N)
  let left := SourceInit.values (records R0 L 0 edges d N he (by intro j; simp) a) m
  let right := SourceInit.values (records R0 L shift edges d N he hv a) m
  commonPairingOutput (integerMatrix (stencilMatrix Q P.rationalMaterial 0) (D^2))
    (D^2) (integerScale s (D^2)) U U left right N
    (by have := (calibrationDenominator_spec P.background.material 0 s).1; positivity) hU hU

theorem scatteredCouplingOutput_value {m : ℕ} (P : PhysicalPlatform) (R0 L : ℕ)
    (shift : Site) (edges : Fin m → Edge) (d b : ℕ)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |shift j| ≤ (L : ℤ))
    (a : Channels m) (U : ℕ) (hU : 0 < U) (q : Fin m → ℚ)
    (ha : ∀ i, (a.value i : ℚ) = (U : ℚ)*q i) :
    (P.scatteredCouplingOutput R0 L shift edges d b he hv a U hU).value =
      P.rationalCoupling edges q ((d : ℤ) • shift) b := by
  let N := P.calibrationDegree b
  let s : ℚ := (P.rowBound^2)⁻¹
  let D := calibrationDenominator P.background.material 0 s
  let Q := radixCubeEmbedding (radius R0 L d N)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨hD,h64,hmD,hz,hsD⟩ := calibrationDenominator_spec P.background.material 0 s
  have hactual := records_pairing_of_coefficients R0 L 0 shift edges edges d N he
    (by intro j; simp) he hv a a U U hU hU q q ha ha P.rationalMaterial 25 (by norm_num)
    P.rationalMaterial_bound 0 s (D^2) (integerScale s (D^2)) (by dsimp [D]; positivity)
    (integerMatrix (stencilMatrix Q P.rationalMaterial 0) (D^2))
    (integerMatrix_scaled _ _ (stencilMatrix_denominator Q P.rationalMaterial 0 D h64 hmD hz))
    (integerScale_scaled s (D^2) hs (hsD.trans (dvd_pow_self D (by decide))))
  have hzero : translateEdge ((d : ℤ) • (0 : Site)) ∘ edges = edges := by
    funext i
    simp [translateEdge]
  rw [hzero] at hactual
  exact hactual

/-- The same actual shared-denominator machine output satisfies the
requested physical Green-coupling error budget. -/
theorem scatteredSignedCoupling_requested_error (P : PhysicalPlatform) (R0 L : ℕ)
    (shift : Site) (d : ℕ)
    (he : ∀ i j, |(ScalarDefect.edgeEmbedding P.defect i).2 j| ≤ (R0 : ℤ))
    (hv : ∀ j, |shift j| ≤ (L : ℤ))
    (a : Channels (ScalarDefect.edges P.defect).card) (U : ℕ) (hU : 0 < U)
    (q : Fin (ScalarDefect.edges P.defect).card → ℚ)
    (ha : ∀ i, (a.value i : ℚ) = (U : ℚ)*q i)
    (η : ℚ) (hη : 0 < η)
    (hq : ‖rationalCoordinates q-P.weightedMode‖ ≤ (1/2 : ℝ)^P.couplingPrecision η) :
    |((-(P.scatteredCouplingOutput R0 L shift (ScalarDefect.edgeEmbedding P.defect) d
        (P.couplingPrecision η) he hv a U hU).value : ℚ) : ℝ) -
      (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
        ((d : ℤ) • shift) P.mode))| ≤ η := by
  rw [P.scatteredCouplingOutput_value R0 L shift (ScalarDefect.edgeEmbedding P.defect) d
    (P.couplingPrecision η) he hv a U hU q ha]
  exact P.signedCoupling_requested_error q ((d : ℤ) • shift) η hη hq

end Maxwell.Composition.PhysicalPlatform
