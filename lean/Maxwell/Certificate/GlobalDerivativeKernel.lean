import Maxwell.Certificate.DyadicKernelVector

/-! Integer-only evaluators for the global verifier's first derivatives. -/
namespace Maxwell.Certificate.DyadicKernel.Derivative

def integerAt (p : Nat) (n : Int) : Rectangle := ⟨n*2^p,0,0⟩

def axisRound (p : Nat) (a : Fin 3) (theta : Rectangle) (d : Triple) : Triple :=
  Triple.ofFn fun j => if j = a then mulRound p (add (d.get j) (integerAt p 1)) theta else zero

def addTriple (u v : Triple) : Triple := Triple.ofFn fun j => add (u.get j) (v.get j)

def scaledAddRound (p : Nat) (u : Triple) (s : Rectangle) (v : Triple) : Triple :=
  Triple.ofFn fun j => add (u.get j) (mulRound p s (v.get j))

def projectionPrimeRound (p : Nat) (d dp u : Triple) (lap : Rectangle) : Option Triple := do
  let z ← divRound p (dotTriple p dp u) lap
  return Triple.ofFn fun j => mulRound p (conjugate (d.get j)) z

/-- The same evaluator handles the center gradient (`d`) and its raw
first coefficient (`dp`); the center normalization is fixed in both. -/
def gradientRound (p : Nat) (d : Triple) (root : Rectangle) : Option Triple := do
  let z ← divideTriple p (Triple.ofFn fun j => conjugate (d.get j)) (Triple.ofFn fun _ => root)
  return Triple.ofFn fun j => mulRound p (integerAt p 8) (z.get j)

def magneticPrimeRound (p : Nat) (d dp weighted weightedPrime : Triple) : Triple :=
  addTriple (curlRound p false dp weighted) (curlRound p false d weightedPrime)

end Maxwell.Certificate.DyadicKernel.Derivative
