import Maxwell.Certificate.DyadicPackedRowsFFTForced
import Maxwell.Certificate.DyadicPackedRowsFFTSound

namespace Maxwell.Certificate.DyadicKernel.PackedRowsFFT.Forced

@[simp] theorem forceOption_eq (a : Option Nat) : forceOption a = a := by
  cases a with
  | none => rfl
  | some n => cases n <;> rfl

theorem build_eq (w : Nat) (f : Fin 20 → Fin 10 → Fin 10 → Rectangle) :
    build w f = PackedRowsFFT.build w f := by
  simp only [build, forceOption_eq, PackedRowsFFT.build]

theorem axisX_eq (w q : Nat) (K : FFT.Kernel 20) (a : Field) :
    axisX w q K a = PackedRowsFFT.axisX w q K a := by
  simp only [axisX, build_eq, PackedRowsFFT.axisX]

theorem axisY_eq (w q : Nat) (K : FFT.Kernel 10) (a : Field) :
    axisY w q K a = PackedRowsFFT.axisY w q K a := by
  simp only [axisY, build_eq, PackedRowsFFT.axisY]

theorem axisZ_eq (w q : Nat) (K : FFT.Kernel 10) (a : Field) :
    axisZ w q K a = PackedRowsFFT.axisZ w q K a := by
  simp only [axisZ, build_eq, PackedRowsFFT.axisZ]

theorem diagonal_eq (w q : Nat) (t : FFT.Field) (a : Field) :
    diagonal w q t a = PackedRowsFFT.diagonal w q t a := by
  simp only [diagonal, build_eq, PackedRowsFFT.diagonal]

theorem forward_eq (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input : Field) :
    forward w q K20 K10 twiddle input = PackedRowsFFT.forward w q K20 K10 twiddle input := by
  simp only [forward, axisX_eq, axisY_eq, axisZ_eq, diagonal_eq, PackedRowsFFT.forward]

theorem inverse_eq (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input : Field) :
    inverse w q K20 K10 twiddle input = PackedRowsFFT.inverse w q K20 K10 twiddle input := by
  simp only [inverse, axisX_eq, axisY_eq, axisZ_eq, diagonal_eq, PackedRowsFFT.inverse]

end Maxwell.Certificate.DyadicKernel.PackedRowsFFT.Forced
