import Maxwell.Certificate.DyadicPackedRowsFFTForced
import Maxwell.Certificate.DyadicKernelButterfly

/-! Packed-row FCC FFT using shared five-point sums and 10/20-point butterflies. -/
namespace Maxwell.Certificate.DyadicKernel.PackedRowsButterfly

open PackedRowsFFT

def axisX (w : Nat) (root : Int → Rectangle) (norm : Rectangle) (sign : Int)
    (a : Field) : Option Field :=
  Forced.build w fun x y z =>
    Butterfly.get (Butterfly.transform20 root norm sign
      (Array.ofFn fun j : Fin 20 => get w a j y z)) x.val

def axisY (w : Nat) (root : Int → Rectangle) (norm : Rectangle) (sign : Int)
    (a : Field) : Option Field :=
  Forced.build w fun x y z =>
    Butterfly.get (Butterfly.transform10 root norm sign
      (Array.ofFn fun j : Fin 10 => get w a x j z)) y.val

def axisZ (w : Nat) (root : Int → Rectangle) (norm : Rectangle) (sign : Int)
    (a : Field) : Option Field :=
  Forced.build w fun x y z =>
    Butterfly.get (Butterfly.transform10 root norm sign
      (Array.ofFn fun j : Fin 10 => get w a x y j)) z.val

def forward (w : Nat) (root : Int → Rectangle) (norm20 norm10 : Rectangle)
    (twiddle : FFT.Field) (input : Field) : Option Field := do
  let first ← axisX w root norm20 (-1) input
  let second ← Forced.diagonal w 52 twiddle first
  let third ← axisY w root norm10 (-1) second
  axisZ w root norm10 (-1) third

def inverse (w : Nat) (root : Int → Rectangle) (norm20 norm10 : Rectangle)
    (twiddle : FFT.Field) (input : Field) : Option Field := do
  let first ← axisZ w root norm10 1 input
  let second ← axisY w root norm10 1 first
  let third ← Forced.diagonal w 52 (FFT.conjugateField twiddle) second
  axisX w root norm20 1 third

end Maxwell.Certificate.DyadicKernel.PackedRowsButterfly
