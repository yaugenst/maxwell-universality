import Maxwell.Certificate.DyadicKernelVector
import Maxwell.Certificate.GlobalFFTComputed.Constants

namespace Maxwell.Certificate.GlobalComputedSymbol
open DyadicKernel

def root (n : Fin 20) : Rectangle := (GlobalFFTComputed.roots[n.val]?).getD zero

def frequencyIndex (f : Fin 20 × Fin 10 × Fin 10) (j : Fin 3) : Fin 20 :=
  ⟨(match j.val with
    | 0 => f.1.val
    | 1 => 2*f.2.1.val+20-f.1.val
    | _ => 2*f.2.2.val+20-f.1.val) % 20, Nat.mod_lt _ (by decide)⟩

def table (phases : Triple) : Vector (Vector Rectangle 20) 3 :=
  Vector.ofFn fun j => Vector.ofFn fun n =>
    add (mulRound 52 (root n) (phases.get j)) ⟨-(2^52),0,0⟩

def symbols (phases : Triple) (f : Fin 20 × Fin 10 × Fin 10) : Triple :=
  Triple.ofFn fun j => (table phases)[j][frequencyIndex f j]

end Maxwell.Certificate.GlobalComputedSymbol
