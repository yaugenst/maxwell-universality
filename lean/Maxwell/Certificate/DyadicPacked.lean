import Maxwell.Certificate.DyadicKernel

/-! Fixed-width exact storage for dyadic rectangles. Bounds are checked before
using a packed word; the signed centers use an offset binary representation. -/
namespace Maxwell.Certificate.DyadicKernel.Packed

def base (w : Nat) : Nat := 2^w

def bias (w : Nat) : Nat := 2^(w-1)

def fits (w : Nat) (a : Rectangle) : Bool := decide
  (0 < w ∧ -(bias w : Int) ≤ a.re ∧ a.re < (bias w : Int) ∧
    -(bias w : Int) ≤ a.im ∧ a.im < (bias w : Int) ∧ a.radius < base w)

def packRect (w : Nat) (a : Rectangle) : Nat :=
  (a.re + bias w).toNat + base w * ((a.im + bias w).toNat + base w*a.radius)

def unpackRect (w : Nat) (n : Nat) : Rectangle :=
  ⟨(n % base w : Nat) - (bias w : Int),
   ((n / base w) % base w : Nat) - (bias w : Int),
   (n / base w / base w) % base w⟩

def getPacked (w data idx : Nat) : Rectangle :=
  unpackRect w (data / 2^(3*w*idx))

def packRects (w : Nat) : List Rectangle → Nat
  | [] => 0
  | a::tail => packRect w a + 2^(3*w)*packRects w tail

end Maxwell.Certificate.DyadicKernel.Packed
