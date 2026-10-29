import Maxwell.Cost.CalibrationSource.Producer

namespace Maxwell.Cost.CalibrationSource.Producer
open Structured CalibrationMatrix
open Defect.FiniteStencil Spectral.Lattice
set_option maxHeartbeats 1000000

def channels {m : ℕ} (d : ModeRead.Data m) : Channels m := ⟨fun i => d.value i 0,fun i => d.value i 1⟩

def inputBases (c : Repack.Data) (base : List Bool) : Fin 3 → List Bool := ![base,c.bases 0,c.bases 1]

def inputWords {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (spacing degree : ℕ)
    (c : Repack.Data) (d : ModeRead.Data m) : Fin 3 → Vector (List Bool) m :=
  ![IndexArray.words R0 L v edges spacing degree (addressValue c.width),Repack.words c d 0,Repack.words c d 1]

/-- The concrete sparse-input descriptor consumed by the existing zero/scatter
machine. Every input word is the output of `Producer.executes`. -/
def sourceData {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (spacing degree : ℕ)
    (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (outputBases : Fin 4 → List Bool)
    (hout : ∀ i j, i ≠ j → IncidenceEncoding.Separated (addressValue (outputBases i))
      ((3*cubeWidth (radius R0 L spacing degree)^3)*addressValue c.width)
      (addressValue (outputBases j)) ((3*cubeWidth (radius R0 L spacing degree)^3)*addressValue c.width))
    (hin : ∀ i j, IncidenceEncoding.Separated (addressValue (inputBases c base i)) (m*addressValue c.width)
      (addressValue (outputBases j)) ((3*cubeWidth (radius R0 L spacing degree)^3)*addressValue c.width)) :
    SourceInit.Data m (3*cubeWidth (radius R0 L spacing degree)^3) where
  width := c.width
  clock := c.clock
  dimension := (3*cubeWidth (radius R0 L spacing degree)^3).bits
  count := m.bits
  inputBases := inputBases c base
  outputBases := outputBases
  inputWords := inputWords R0 L v edges spacing degree c d
  width_nonempty := c.width_nonempty
  width_positive := c.width_positive
  clock_length := c.clock_length
  dimension_value := addressValue_bits _
  count_value := addressValue_bits _
  index_bound j := by
    change addressValue ((IndexArray.words R0 L v edges spacing degree (addressValue c.width)).get j) < _
    rw [IndexArray.words_get,FixedWidth.bits_value _ _
      (IndexArray.address_bits_fit R0 L v (edges j) spacing degree _ (he j) hv hwidth),addressValue_bits]
    exact address_lt R0 L v (edges j) spacing degree (he j) hv
  output_separated := hout
  input_separated := hin

/-- The generated sparse records carry the actual translated edges and
exact qhat channels, including cancelling contributions on repeated edges. -/
theorem sourceData_records {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (spacing degree : ℕ)
    (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (outputBases : Fin 4 → List Bool) (hout) (hin)
    (hfit : ∀ i a, (d.value i a).bits.length ≤ addressValue c.width) :
    (sourceData R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin).records =
      records R0 L v edges spacing degree he hv (channels d) := by
  change SourceInit.Records.mk _ _ _ = SourceInit.Records.mk _ _ _
  congr 1
  · funext i
    apply Fin.ext
    change addressValue ((IndexArray.words R0 L v edges spacing degree (addressValue c.width)).get i) = _
    rw [IndexArray.words_get,FixedWidth.bits_value _ _
      (IndexArray.address_bits_fit R0 L v (edges i) spacing degree _ (he i) hv hwidth),addressValue_bits]
  · funext i; exact Repack.words_value c d i 0 (hfit i 0)
  · funext i; exact Repack.words_value c d i 1 (hfit i 1)

/-- Bind the initialized signed dense source to the actual physical qhat
source with its original shared denominator. -/
theorem sourceData_values {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (spacing degree : ℕ)
    (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (outputBases : Fin 4 → List Bool) (hout) (hin)
    (hfit : ∀ i a, (d.value i a).bits.length ≤ addressValue c.width)
    (hden : 0 < d.denominator) (i : Fin (3*cubeWidth (radius R0 L spacing degree)^3)) :
    ((SourceInit.values (sourceData R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin).records m).value i : ℚ) =
      (d.denominator : ℚ)*coefficients (radixCubeEmbedding (radius R0 L spacing degree))
        (rationalSource (Maxwell.Green.PhysicalCompression.translateEdge ((spacing : ℤ) • v) ∘ edges)
          (rationalCoefficients (channels d) d.denominator)) i := by
  rw [sourceData_records R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin hfit]
  exact records_scaled R0 L v edges spacing degree he hv (channels d) d.denominator hden i

/-- Bit fit follows from the actual retained array width and the allocation
width; it is not an assumption about unknown numerical mode entries. -/
theorem stored_value_fit {m : ℕ} (c : Repack.Data) (d : ModeRead.Data m) (state : BitRAMState)
    (hs : ModeRead.Stored Repack.readLayout d state)
    (hwidth : addressValue d.width ≤ addressValue c.width) (i : Fin m) (a : Fin 2) :
    (d.value i a).bits.length ≤ addressValue c.width := by
  have h : (addressValue ((d.words a).get i)).bits.length ≤ ((d.words a).get i).length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length _)
  exact h.trans (((hs.arrays a).length i).le.trans hwidth)

/-- Same physical-source identity with all coefficient-width premises
obtained from the actual stored mode array. -/
theorem sourceData_values_of_stored {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (spacing degree : ℕ)
    (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (outputBases : Fin 4 → List Bool) (hout) (hin)
    (state : BitRAMState) (hs : ModeRead.Stored Repack.readLayout d state)
    (hmodewidth : addressValue d.width ≤ addressValue c.width)
    (hden : 0 < d.denominator) (i : Fin (3*cubeWidth (radius R0 L spacing degree)^3)) :
    ((SourceInit.values (sourceData R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin).records m).value i : ℚ) =
      (d.denominator : ℚ)*coefficients (radixCubeEmbedding (radius R0 L spacing degree))
        (rationalSource (Maxwell.Green.PhysicalCompression.translateEdge ((spacing : ℤ) • v) ∘ edges)
          (rationalCoefficients (channels d) d.denominator)) i :=
  sourceData_values R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin
    (stored_value_fit c d state hs hmodewidth) hden i

end Maxwell.Cost.CalibrationSource.Producer
