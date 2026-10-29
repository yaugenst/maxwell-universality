import Maxwell.Certificate.DyadicPackedFFT

/-! Row-sized packed integers avoid division of an entire 2000-cell field.
Every computed row is range checked before it is made available. -/
namespace Maxwell.Certificate.DyadicKernel.PackedRowsFFT

abbrev Field := Array (Array Nat)

def collectList {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x::xs => do
    let y ← f x
    let ys ← collectList f xs
    pure (y::ys)

def collect {n : Nat} {α : Type} (f : Fin n → Option α) : Option (Array α) :=
  (collectList f (List.ofFn fun i => i)).map List.toArray

def build (w : Nat) (f : Fin 20 → Fin 10 → Fin 10 → Rectangle) : Option Field :=
  collect fun x => collect fun y =>
    PackedFFT.packChecked w (List.ofFn fun z => f x y z)

def get (w : Nat) (a : Field) (x : Fin 20) (y z : Fin 10) : Rectangle :=
  Packed.getPacked w (((a[x.val]?.getD #[])[y.val]?).getD 0) z.val

def decode (w : Nat) (a : Field) : FFT.Field := FFT.build (get w a)

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

def subsetRow (w : Nat) (a b : Field) (x : Fin 20) : Bool :=
  (List.ofFn fun y : Fin 10 =>
    (List.ofFn fun z : Fin 10 => subsetCheck (get w a x y z) (get w b x y z)).all id).all id

def subset (w : Nat) (a b : Field) : Bool :=
  (List.ofFn fun x : Fin 20 => subsetRow w a b x).all id

end Maxwell.Certificate.DyadicKernel.PackedRowsFFT
