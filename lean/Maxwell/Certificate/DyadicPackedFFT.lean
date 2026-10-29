import Maxwell.Certificate.DyadicPacked
import Maxwell.Certificate.DyadicKernelFFT

/-! Exact checked packing forces each computed FFT stage into one integer.
Only the canonical input and the final enclosure need literal storage. -/
namespace Maxwell.Certificate.DyadicKernel.PackedFFT

def packChecked (w : Nat) : List Rectangle → Option Nat
  | [] => some 0
  | a::tail =>
    if Packed.fits w a then
      (packChecked w tail).map (fun n => Packed.packRect w a + 2^(3*w)*n)
    else none

def coordinateX (i : Fin 2000) : Fin 20 := Fin.ofNat 20 (i.val/100)
def coordinateY (i : Fin 2000) : Fin 10 := Fin.ofNat 10 (i.val/10)
def coordinateZ (i : Fin 2000) : Fin 10 := Fin.ofNat 10 i.val

def build (w : Nat) (f : Fin 20 → Fin 10 → Fin 10 → Rectangle) : Option Nat :=
  packChecked w (List.ofFn fun i : Fin 2000 =>
    f (coordinateX i) (coordinateY i) (coordinateZ i))

def get (w data : Nat) (x : Fin 20) (y z : Fin 10) : Rectangle :=
  Packed.getPacked w data (100*x.val+10*y.val+z.val)

def decode (w data : Nat) : FFT.Field := FFT.build (get w data)

def axisX (w q : Nat) (K : FFT.Kernel 20) (a : Nat) : Option Nat :=
  build w fun x y z => dotRound q (List.ofFn fun j : Fin 20 => (get w a j y z,K x j))

def axisY (w q : Nat) (K : FFT.Kernel 10) (a : Nat) : Option Nat :=
  build w fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get w a x j z,K y j))

def axisZ (w q : Nat) (K : FFT.Kernel 10) (a : Nat) : Option Nat :=
  build w fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get w a x y j,K z j))

def diagonal (w q : Nat) (t : FFT.Field) (a : Nat) : Option Nat :=
  build w fun x y z => mulRound q (get w a x y z) (FFT.get t x y z)

def forward (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input : Nat) : Option Nat := do
  let first ← axisX w q K20 input
  let second ← diagonal w q twiddle first
  let third ← axisY w q K10 second
  axisZ w q K10 third

def inverse (w q : Nat) (K20 : FFT.Kernel 20) (K10 : FFT.Kernel 10)
    (twiddle : FFT.Field) (input : Nat) : Option Nat := do
  let first ← axisZ w q (FFT.adjoint K10) input
  let second ← axisY w q (FFT.adjoint K10) first
  let third ← diagonal w q (FFT.conjugateField twiddle) second
  axisX w q (FFT.adjoint K20) third

def subsetRow (w a b : Nat) (x : Fin 20) : Bool :=
  (List.ofFn fun y : Fin 10 =>
    (List.ofFn fun z : Fin 10 => subsetCheck (get w a x y z) (get w b x y z)).all id).all id

def subset (w a b : Nat) : Bool :=
  (List.ofFn fun x : Fin 20 => subsetRow w a b x).all id

end Maxwell.Certificate.DyadicKernel.PackedFFT
