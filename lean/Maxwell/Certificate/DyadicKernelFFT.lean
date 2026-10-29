import Maxwell.Certificate.DyadicKernelRounded

/-! Deterministic FCC FFT evaluation over exact integers. This module has no
analytic imports and stores no proposed intermediate arrays. -/
namespace Maxwell.Certificate.DyadicKernel.FFT

abbrev Field := Array (Array (Array Rectangle))
abbrev Kernel (n : Nat) := Fin n → Fin n → Rectangle

def get (a : Field) (x : Fin 20) (y z : Fin 10) : Rectangle :=
  (((a[x.val]?.getD #[])[y.val]?.getD #[])[z.val]?).getD zero

def build (a : Fin 20 → Fin 10 → Fin 10 → Rectangle) : Field :=
  Array.ofFn fun x => Array.ofFn fun y => Array.ofFn fun z => a x y z

def axisX (q : Nat) (K : Kernel 20) (a : Field) : Field :=
  build fun x y z => dotRound q (List.ofFn fun j : Fin 20 => (get a j y z,K x j))

def axisY (q : Nat) (K : Kernel 10) (a : Field) : Field :=
  build fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get a x j z,K y j))

def axisZ (q : Nat) (K : Kernel 10) (a : Field) : Field :=
  build fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get a x y j,K z j))

def diagonal (q : Nat) (t : Field) (a : Field) : Field :=
  build fun x y z => mulRound q (get a x y z) (get t x y z)

def adjoint {n : Nat} (K : Kernel n) : Kernel n := fun i j => conjugate (K j i)

def conjugateField (a : Field) : Field := build fun x y z => conjugate (get a x y z)

def forward (q : Nat) (K20 : Kernel 20) (K10 : Kernel 10) (twiddle input : Field) : Field :=
  let first := axisX q K20 input
  let second := diagonal q twiddle first
  let third := axisY q K10 second
  axisZ q K10 third

def inverse (q : Nat) (K20 : Kernel 20) (K10 : Kernel 10) (twiddle input : Field) : Field :=
  let first := axisZ q (adjoint K10) input
  let second := axisY q (adjoint K10) first
  let third := diagonal q (conjugateField twiddle) second
  axisX q (adjoint K20) third

def subsetRow (a b : Field) (x : Fin 20) : Bool :=
  (List.ofFn fun y : Fin 10 =>
    (List.ofFn fun z : Fin 10 => subsetCheck (get a x y z) (get b x y z)).all id).all id

end Maxwell.Certificate.DyadicKernel.FFT
