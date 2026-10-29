import Maxwell.Certificate.DyadicKernelSchur

namespace Maxwell.Certificate.DyadicKernel

def signedEntry {n : Nat} (negative : Bool) (a : Rectangle) (i j : Fin n) : Rectangle :=
  add (if negative then neg a else a)
    ⟨if i=j then -(4503599627370496-4398046511104) else 0,0,0⟩

end Maxwell.Certificate.DyadicKernel
