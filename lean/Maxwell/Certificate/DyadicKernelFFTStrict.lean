import Maxwell.Certificate.DyadicKernelFFT

namespace Maxwell.Certificate.DyadicKernel.FFT

/-- Constructor matching forces arithmetic to a numeral before it is stored
in the result array. The continuation retains that normalized constructor. -/
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | n+1 => k (n+1)

def forceInt {α : Type} (n : Int) (k : Int → α) : α :=
  match n with
  | .ofNat n => forceNat n fun m => k (.ofNat m)
  | .negSucc n => forceNat n fun m => k (.negSucc m)

def forceRectangle {α : Type} (a : Rectangle) (k : Rectangle → α) : α :=
  match a with
  | ⟨r,i,e⟩ => forceInt r fun r' => forceInt i fun i' => forceNat e fun e' => k ⟨r',i',e'⟩

def collect {α β γ : Type} (f : α → (β → γ) → γ) : List α → (List β → γ) → γ
  | [], k => k []
  | x::xs, k => f x fun y => collect f xs fun ys => k (y::ys)

def buildStrict (a : Fin 20 → Fin 10 → Fin 10 → Rectangle) : Field :=
  collect (fun x kx =>
    collect (fun y ky =>
      collect (fun z kz => forceRectangle (a x y z) kz)
        (List.ofFn fun z : Fin 10 => z) (fun zs => ky ⟨zs⟩))
      (List.ofFn fun y : Fin 10 => y) (fun ys => kx ⟨ys⟩))
    (List.ofFn fun x : Fin 20 => x) (fun xs => ⟨xs⟩)

def axisXStrict (q : Nat) (K : Kernel 20) (a : Field) : Field :=
  buildStrict fun x y z => dotRound q (List.ofFn fun j : Fin 20 => (get a j y z,K x j))

def axisYStrict (q : Nat) (K : Kernel 10) (a : Field) : Field :=
  buildStrict fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get a x j z,K y j))

def axisZStrict (q : Nat) (K : Kernel 10) (a : Field) : Field :=
  buildStrict fun x y z => dotRound q (List.ofFn fun j : Fin 10 => (get a x y j,K z j))

def diagonalStrict (q : Nat) (t : Field) (a : Field) : Field :=
  buildStrict fun x y z => mulRound q (get a x y z) (get t x y z)

def forwardStrict (q : Nat) (K20 : Kernel 20) (K10 : Kernel 10) (twiddle input : Field) : Field :=
  let first := axisXStrict q K20 input
  let second := diagonalStrict q twiddle first
  let third := axisYStrict q K10 second
  axisZStrict q K10 third

def inverseStrict (q : Nat) (K20 : Kernel 20) (K10 : Kernel 10) (twiddle input : Field) : Field :=
  let first := axisZStrict q (adjoint K10) input
  let second := axisYStrict q (adjoint K10) first
  let third := diagonalStrict q (conjugateField twiddle) second
  axisXStrict q (adjoint K20) third

end Maxwell.Certificate.DyadicKernel.FFT
