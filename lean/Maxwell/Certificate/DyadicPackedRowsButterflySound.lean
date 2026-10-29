import Maxwell.Certificate.DyadicPackedRowsButterflyStages

namespace Maxwell.Certificate.DyadicKernel.PackedRowsButterfly
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee
open PackedRowsFFT

theorem diagonal_contains {p w : Nat} {input output : Field} {t : FFT.Field}
    {a v : Cell → ℂ} (h : Forced.diagonal w 52 t input = some output)
    (ht : DyadicFFT.Contains 52 (FFT.toField t) a)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) (Matrix.diagonal a *ᵥ v) := by
  have hd : PackedRowsFFT.diagonal w 52 t input = some output := by
    simpa only [Forced.diagonal_eq] using h
  rw [PackedRowsFFT.diagonal_eq hd]
  exact DyadicFFT.diagonalCheck_sound ht hv (FFT.diagonal_checked p 52 t (decode w input))

attribute [local irreducible] axisX axisY axisZ Forced.diagonal decode

theorem forward_contains {p w : Nat} {root : Int → Rectangle} {norm20 norm10 : Rectangle}
    {twiddle : FFT.Field} {input output : Field}
    (h : forward w root norm20 norm10 twiddle input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn20 : norm20.toDyadic = FFTWitness.norm20)
    (hn10 : norm10.toDyadic = FFTWitness.norm10)
    (ht : DyadicFFT.Contains 52 (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) ((transform 0).conjTranspose *ᵥ v) := by
  obtain ⟨first,hfirst,second,hsecond,third,hthird,hresult⟩ :=
    (by simpa only [forward, bind, Option.bind_eq_some_iff] using h :
      ∃ first, axisX w root norm20 (-1) input = some first ∧
      ∃ second, Forced.diagonal w 52 twiddle first = some second ∧
      ∃ third, axisY w root norm10 (-1) second = some third ∧
        axisZ w root norm10 (-1) third = some output)
  have h1 := axisX_forward_contains hfirst hr hn20 hv
  have h2 := diagonal_contains hsecond ht h1
  have h3 := axisY_forward_contains hthird hr hn10 h2
  have h4 := axisZ_forward_contains hresult hr hn10 h3
  rw [← forwardFFT_eq_conjTranspose, forwardFFT]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

theorem inverse_contains {p w : Nat} {root : Int → Rectangle} {norm20 norm10 : Rectangle}
    {twiddle : FFT.Field} {input output : Field}
    (h : inverse w root norm20 norm10 twiddle input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn20 : norm20.toDyadic = FFTWitness.norm20)
    (hn10 : norm10.toDyadic = FFTWitness.norm10)
    (ht : DyadicFFT.Contains 52 (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) (transform 0 *ᵥ v) := by
  obtain ⟨first,hfirst,second,hsecond,third,hthird,hresult⟩ :=
    (by simpa only [inverse, bind, Option.bind_eq_some_iff] using h :
      ∃ first, axisZ w root norm10 1 input = some first ∧
      ∃ second, axisY w root norm10 1 first = some second ∧
      ∃ third, Forced.diagonal w 52 (FFT.conjugateField twiddle) second = some third ∧
        axisX w root norm20 1 third = some output)
  have h1 := axisZ_inverse_contains hfirst hr hn10 hv
  have h2 := axisY_inverse_contains hsecond hr hn10 h1
  have ht' : DyadicFFT.Contains 52 (FFT.toField (FFT.conjugateField twiddle)) (star fccTwiddle) := by
    simpa only [FFT.toField_conjugate] using DyadicFFT.conjugate_contains ht
  have h3 := diagonal_contains hthird ht' h2
  have h4 := axisX_inverse_contains hresult hr hn20 h3
  rw [← inverseFFT_eq_transform, inverseFFT, axisX_conjTranspose, axisY_conjTranspose,
    axisZ_conjTranspose, Matrix.diagonal_conjTranspose]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

theorem inverse_native_contains {p w : Nat} {root : Int → Rectangle} {norm20 norm10 : Rectangle}
    {twiddle : FFT.Field} {input native : Field}
    (h : (inverse w root norm20 norm10 twiddle input).any
      (fun output => PackedRowsFFT.subset w output native) = true)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn20 : norm20.toDyadic = FFTWitness.norm20)
    (hn10 : norm10.toDyadic = FFTWitness.norm10)
    (ht : DyadicFFT.Contains 52 (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w native)) (transform 0 *ᵥ v) := by
  obtain ⟨output,he,hs⟩ := (Option.any_eq_true _ _).mp h
  exact PackedRowsFFT.subset_sound hs (inverse_contains he hr hn20 hn10 ht v hv)

theorem forward_native_contains {p w : Nat} {root : Int → Rectangle} {norm20 norm10 : Rectangle}
    {twiddle : FFT.Field} {input native : Field}
    (h : (forward w root norm20 norm10 twiddle input).any
      (fun output => PackedRowsFFT.subset w output native) = true)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn20 : norm20.toDyadic = FFTWitness.norm20)
    (hn10 : norm10.toDyadic = FFTWitness.norm10)
    (ht : DyadicFFT.Contains 52 (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w native)) ((transform 0).conjTranspose *ᵥ v) := by
  obtain ⟨output,he,hs⟩ := (Option.any_eq_true _ _).mp h
  exact PackedRowsFFT.subset_sound hs (forward_contains he hr hn20 hn10 ht v hv)

end Maxwell.Certificate.DyadicKernel.PackedRowsButterfly
