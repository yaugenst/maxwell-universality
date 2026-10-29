import Maxwell.Certificate.DyadicPackedRowsFFT

namespace Maxwell.Certificate.DyadicKernel.PackedRowsFFT.Forced

/-- Pattern matching the packed word normalizes all row components before
storing the row in an Array. -/
def forceOption : Option Nat → Option Nat
  | none => none
  | some 0 => some 0
  | some (n+1) => some (n+1)

def build (w : Nat) (f : Fin 20 → Fin 10 → Fin 10 → Rectangle) : Option Field :=
  collect fun x => collect fun y =>
    forceOption (PackedFFT.packChecked w (List.ofFn fun z => f x y z))

def axisX (w q : Nat) (K : FFT.Kernel 20) (a : Field) : Option Field :=
  build w fun x y z => dotRound q (List.ofFn fun j : Fin 20 => (get w a j y z,K x j))

def axisY (w q : Nat) (K : FFT.Kernel 10) (a : Field) : Option Field :=
  build w fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get w a x j z,K y j))

def axisZ (w q : Nat) (K : FFT.Kernel 10) (a : Field) : Option Field :=
  build w fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get w a x y j,K z j))

def diagonal (w q : Nat) (t : FFT.Field) (a : Field) : Option Field :=
  build w fun x y z => mulRound q (get w a x y z) (FFT.get t x y z)

def forward (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input : Field) : Option Field := do
  let first ← axisX w q K20 input
  let second ← diagonal w q twiddle first
  let third ← axisY w q K10 second
  axisZ w q K10 third

def inverse (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input : Field) : Option Field := do
  let first ← axisZ w q (FFT.adjoint K10) input
  let second ← axisY w q (FFT.adjoint K10) first
  let third ← diagonal w q (FFT.conjugateField twiddle) second
  axisX w q (FFT.adjoint K20) third

end Maxwell.Certificate.DyadicKernel.PackedRowsFFT.Forced
