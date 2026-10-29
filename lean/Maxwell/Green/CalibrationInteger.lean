import Maxwell.Green.CalibrationLattice
import Maxwell.Green.CalibrationBitBounds
import Maxwell.Cost.CalibrationMatrix.Bounds

/-! The actual integer two-channel Horner recurrence computes the same
finite rational stencil polynomial, with an explicit common denominator. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
open Cost.CalibrationMatrix
open scoped Matrix
set_option maxHeartbeats 600000
variable {n : ℕ}

theorem channelMatvec_scaled (A : ChannelMatrix n) (x : Channels n)
    (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) (D V : ℚ)
    (hA : ∀ i j, (A.value i j : ℚ) = D * H i j)
    (hx : ∀ i, (x.value i : ℚ) = V * v i) (i : Fin n) :
    ((matvec A x).value i : ℚ) = (D * V) * (H *ᵥ v) i := by
  rw [value_matvec]
  simp only [Int.cast_sum, Int.cast_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hA, hx]
  ring

/-- Both the growing source and the Horner numerator have their exact
intended rational meaning at every iteration. -/
theorem channelHorner_scaled (A : ChannelMatrix n) (D S V : ℕ) (source : Channels n)
    (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (v : Fin n → ℚ)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ) * H i j)
    (hs : (S : ℚ) = (D : ℚ) * s)
    (hv : ∀ i, (source.value i : ℚ) = (V : ℚ) * v i) (N : ℕ) :
    (∀ i, ((horner A D S source N).1.value i : ℚ) =
      ((V : ℚ) * (D : ℚ) ^ (3 * N)) * v i) ∧
    (∀ i, ((horner A D S source N).2.value i : ℚ) =
      ((V : ℚ) * (D : ℚ) ^ (3 * N)) * denseHorner H s v N i) := by
  induction N with
  | zero => simpa only [horner, denseHorner, Nat.mul_zero, pow_zero, mul_one] using And.intro hv hv
  | succ N ih =>
    have ht := channelMatvec_scaled A (horner A D S source N).2 H
      (denseHorner H s v N) (D : ℚ) ((V : ℚ) * (D : ℚ) ^ (3 * N)) hA ih.2
    have hu := channelMatvec_scaled A (matvec A (horner A D S source N).2) H
      (H *ᵥ denseHorner H s v N) (D : ℚ)
      ((D : ℚ) * ((V : ℚ) * (D : ℚ) ^ (3 * N))) hA ht
    constructor
    · intro i
      rw [horner, hornerStep_source_value]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [ih.1]
      rw [Nat.mul_succ, pow_add]
      ring
    · intro i
      simp only [horner, hornerStep, value_add, value_scale, value_negate,
        Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_natCast, Nat.cast_pow]
      rw [ih.1, ih.2, hu, hs]
      simp only [denseHorner, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      ring

theorem channelHorner_eq (A : ChannelMatrix n) (D S V : ℕ) (source : Channels n)
    (hD : 0 < D) (hV : 0 < V)
    (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (v : Fin n → ℚ)
    (hA : ∀ i j, H i j = (A.value i j : ℚ) / D)
    (hs : s = (S : ℚ) / D)
    (hv : ∀ i, v i = (source.value i : ℚ) / V) (N : ℕ) (i : Fin n) :
    ((horner A D S source N).2.value i : ℚ) / ((V : ℚ) * (D : ℚ) ^ (3 * N)) =
      denseHorner H s v N i := by
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hV0 : (V : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hV
  have h := (channelHorner_scaled A D S V source H s v
    (fun i j => by rw [hA]; field_simp)
    (by rw [hs]; field_simp)
    (fun i => by rw [hv]; field_simp) N).2 i
  rw [h]
  field_simp

theorem channelInverse_scaled (A : ChannelMatrix n) (D S V : ℕ) (source : Channels n)
    (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (v : Fin n → ℚ)
    (hA : ∀ i j, (A.value i j : ℚ) = (D : ℚ) * H i j)
    (hs : (S : ℚ) = (D : ℚ) * s)
    (hv : ∀ i, (source.value i : ℚ) = (V : ℚ) * v i) (N : ℕ) (i : Fin n) :
    ((inverseNumerator A D S source N).value i : ℚ) =
      ((V : ℚ) * (D : ℚ) ^ (3 * N + 2)) * denseInverse H s v N i := by
  have hx := (channelHorner_scaled A D S V source H s v hA hs hv N).2
  have ht := channelMatvec_scaled A (horner A D S source N).2 H
    (denseHorner H s v N) (D : ℚ) ((V : ℚ) * (D : ℚ) ^ (3 * N)) hA hx i
  simp only [inverseNumerator, value_scale, Int.cast_mul, Int.cast_natCast]
  rw [ht, hs]
  simp only [denseInverse, Pi.smul_apply, smul_eq_mul, pow_add]
  ring

theorem channelInverse_eq (A : ChannelMatrix n) (D S V : ℕ) (source : Channels n)
    (hD : 0 < D) (hV : 0 < V)
    (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (v : Fin n → ℚ)
    (hA : ∀ i j, H i j = (A.value i j : ℚ) / D)
    (hs : s = (S : ℚ) / D)
    (hv : ∀ i, v i = (source.value i : ℚ) / V) (N : ℕ) (i : Fin n) :
    ((inverseNumerator A D S source N).value i : ℚ) / ((V : ℚ) * (D : ℚ) ^ (3 * N + 2)) =
      denseInverse H s v N i := by
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hV0 : (V : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hV
  rw [channelInverse_scaled A D S V source H s v
    (fun i j => by rw [hA]; field_simp)
    (by rw [hs]; field_simp)
    (fun i => by rw [hv]; field_simp) N i]
  field_simp

/-- Numerator at a specified common denominator, calculated by exact integer
arithmetic. The division is exact under the accompanying divisibility proof. -/
def commonNumerator (D : ℕ) (q : ℚ) : ℤ := q.num * (D / q.den : ℕ)

theorem commonNumerator_scaled (D : ℕ) (q : ℚ) (hq : q.den ∣ D) :
    (commonNumerator D q : ℚ) = (D : ℚ) * q := by
  have hmul : (q.den : ℚ) * (D / q.den : ℕ) = D := by
    exact_mod_cast Nat.mul_div_cancel' hq
  simp only [commonNumerator, Int.cast_mul, Int.cast_natCast]
  rw [← Rat.mul_den_eq_num q, mul_assoc, hmul, mul_comm]

private theorem split_integer (z : ℤ) : (z.toNat : ℤ) - (-z).toNat = z := by omega

/-- Computed sign channels of a rational matrix at its common denominator. -/
def integerMatrix (H : Matrix (Fin n) (Fin n) ℚ) (D : ℕ) : ChannelMatrix n :=
  ⟨fun i j => (commonNumerator D (H i j)).toNat,
   fun i j => (-commonNumerator D (H i j)).toNat⟩

def integerSource (v : Fin n → ℚ) (V : ℕ) : Channels n :=
  ⟨fun i => (commonNumerator V (v i)).toNat,
   fun i => (-commonNumerator V (v i)).toNat⟩

def integerScale (s : ℚ) (D : ℕ) : ℕ := (commonNumerator D s).toNat

theorem integerMatrix_scaled (H : Matrix (Fin n) (Fin n) ℚ) (D : ℕ)
    (hH : ∀ i j, (H i j).den ∣ D) (i j : Fin n) :
    ((integerMatrix H D).value i j : ℚ) = (D : ℚ) * H i j := by
  change (↑(((commonNumerator D (H i j)).toNat : ℤ) -
    (-commonNumerator D (H i j)).toNat) : ℚ) = _
  rw [split_integer, commonNumerator_scaled D _ (hH i j)]

theorem integerSource_scaled (v : Fin n → ℚ) (V : ℕ)
    (hv : ∀ i, (v i).den ∣ V) (i : Fin n) :
    ((integerSource v V).value i : ℚ) = (V : ℚ) * v i := by
  change (↑(((commonNumerator V (v i)).toNat : ℤ) -
    (-commonNumerator V (v i)).toNat) : ℚ) = _
  rw [split_integer, commonNumerator_scaled V _ (hv i)]

theorem integerScale_scaled (s : ℚ) (D : ℕ) (hs : 0 ≤ s) (hden : s.den ∣ D) :
    (integerScale s D : ℚ) = (D : ℚ) * s := by
  have hnonneg : 0 ≤ commonNumerator D s := by
    apply mul_nonneg (Rat.num_nonneg.mpr hs) (Int.natCast_nonneg _)
  have h := Int.toNat_of_nonneg hnonneg
  have hcast := congrArg (fun z : ℤ => (z : ℚ)) h
  simpa only [integerScale, Int.cast_natCast, commonNumerator_scaled D s hden] using hcast

theorem integerInverse_eq (H : Matrix (Fin n) (Fin n) ℚ) (s : ℚ)
    (v : Fin n → ℚ) (D V : ℕ) (hD : 0 < D) (hV : 0 < V) (hs : 0 ≤ s)
    (hH : ∀ i j, (H i j).den ∣ D) (hsD : s.den ∣ D)
    (hv : ∀ i, (v i).den ∣ V) (N : ℕ) (i : Fin n) :
    ((inverseNumerator (integerMatrix H D) D (integerScale s D)
      (integerSource v V) N).value i : ℚ) / ((V : ℚ) * (D : ℚ) ^ (3 * N + 2)) =
      denseInverse H s v N i := by
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  apply channelInverse_eq _ _ _ _ _ hD hV _ _ _
  · intro i j
    rw [integerMatrix_scaled H D hH]
    field_simp
  · rw [integerScale_scaled s D hs hsD]
    field_simp
  · intro i
    rw [integerSource_scaled v V hv]
    have hV0 : (V : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hV
    field_simp

/-- The actual finite Yee matrix has a fixed common denominator, independent
of the containing support cube and its lattice translation. -/
theorem stencilMatrix_denominator (edges : Fin n → Edge) (m : Edge → ℚ)
    (z : ℚ) (D : ℕ) (h64 : 64 ∣ D) (hm : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D)
    (i j : Fin n) : (stencilMatrix edges m z i j).den ∣ D ^ 2 := by
  have hv : HasDenominator [(edges j, 1)] 1 := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp
  have h := (hv.step m z h64 hm hz).evaluate (edges i)
  simpa only [stencilMatrix, Nat.mul_one] using h

/-- The finite integer implementation, including matrix and source conversion,
with its exact unreduced output denominator. -/
def integerStencilAction (edges : Fin n → Edge) (m : Edge → ℚ)
    (z s : ℚ) (D : ℕ) (v : SparseField) (N : ℕ) : Fin n → ℚ :=
  let V := sourceDenominator v
  let A := integerMatrix (stencilMatrix edges m z) (D ^ 2)
  let source := integerSource (coefficients edges v) V
  let numerator := inverseNumerator A (D ^ 2) (integerScale s (D ^ 2)) source N
  fun i => (numerator.value i : ℚ) / ((V : ℚ) * ((D ^ 2 : ℕ) : ℚ) ^ (3 * N + 2))

theorem integerStencilAction_eq_dense (edges : Fin n → Edge) (m : Edge → ℚ)
    (z s : ℚ) (D : ℕ) (hD : 0 < D) (h64 : 64 ∣ D)
    (hm : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D) (hsD : s.den ∣ D)
    (hs : 0 ≤ s) (v : SparseField) (N : ℕ) :
    integerStencilAction edges m z s D v N =
      denseInverse (stencilMatrix edges m z) s (coefficients edges v) N := by
  funext i
  apply integerInverse_eq _ s _ (D ^ 2) (sourceDenominator v) (by positivity)
    (sourceDenominator_pos v) hs
  · exact stencilMatrix_denominator edges m z D h64 hm hz
  · exact hsD.trans (by rw [pow_two]; exact dvd_mul_right _ _)
  · intro j
    exact (has_sourceDenominator v).evaluate (edges j)

/-- No approximate or finite-domain operator is assumed: the computed
integer channels represent the polynomial of the actual infinite Yee operator. -/
theorem integerStencilAction_physical (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (D : ℕ) (hD : 0 < D)
    (h64 : 64 ∣ D) (hmD : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D)
    (hsD : s.den ∣ D) (hs : 0 ≤ s) (v : SparseField)
    (R : ℕ) (hv : Supported v R) (N : ℕ) :
    embed (rationalSource (cubeEmbedding (R + 4 * N + 2))
      (integerStencilAction (cubeEmbedding (R + 4 * N + 2)) m z s D v N)) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed v) := by
  rw [integerStencilAction_eq_dense _ m z s D hD h64 hmD hz hsD hs]
  exact denseInverse_physical m K hK hm z s v R hv N

/-- For any finite periodic rational material table, the common denominator
is computed from that table. It is independent of precision and source location. -/
theorem integerPeriodicInverse_physical (material : Cell20 → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(rationalEdgeAverage material e : ℝ)| ≤ K)
    (z s : ℚ) (hs : 0 ≤ s) (v : SparseField) (R : ℕ) (hv : Supported v R) (N : ℕ) :
    embed (rationalSource (cubeEmbedding (R + 4 * N + 2))
      (integerStencilAction (cubeEmbedding (R + 4 * N + 2)) (rationalEdgeAverage material)
        z s (calibrationDenominator material z s) v N)) =
      inversePolynomial (operator (rationalEdgeAverage material) K hK hm z) (s : ℂ) N (embed v) := by
  obtain ⟨hD, h64, hmD, hz, hsD⟩ := calibrationDenominator_spec material z s
  exact integerStencilAction_physical _ K hK hm z s _ hD h64 hmD hz hsD hs v R hv N

end Maxwell.Defect.FiniteStencil
