import Maxwell.Certificate.DyadicPackedRowsFFTForced

/-! Keep exact-stage composition generic so kernel equality checking does not
expand the complete closed FFT computation when assembling its certificate. -/
namespace Maxwell.Certificate.DyadicKernel.PackedRowsFFT

theorem inverse_accept_of_stages (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input first second third result native : Field)
    (h1 : Forced.axisZ w q (FFT.adjoint K10) input = some first)
    (h2 : Forced.axisY w q (FFT.adjoint K10) first = some second)
    (h3 : Forced.diagonal w q (FFT.conjugateField twiddle) second = some third)
    (h4 : Forced.axisX w q (FFT.adjoint K20) third = some result)
    (hs : subset w result native = true) :
    (Forced.inverse w q K20 K10 twiddle input).any
      (fun a => subset w a native) = true := by
  simp only [Forced.inverse, bind, h1, Option.bind_some, h2, h3, h4, Option.any_some, hs]

end Maxwell.Certificate.DyadicKernel.PackedRowsFFT
