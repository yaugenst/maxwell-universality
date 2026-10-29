import Maxwell.Certificate.DyadicKernelSqrt
import Maxwell.Certificate.GlobalDerivativeKernel

namespace Maxwell.Certificate.DyadicKernel.Weight

def inverseLaplacian (p : Nat) (lap : Rectangle) : Option Rectangle :=
  divRound p (Derivative.integerAt p 1) lap

def inverseRoot (p : Nat) (lap : Rectangle) : Option Rectangle := do
  let root ← sqrtRound p lap
  divRound p (Derivative.integerAt p 1) root

/-- The center high-frequency weight at the verifier's shift 1/64. -/
def high (rho : Nat) (lap : Rectangle) : Option Rectangle := do
  let scaled ← divRound 52 lap (Derivative.integerAt 52 rho)
  inverseRoot 52 (add scaled ⟨-70368744177664,0,0⟩)

end Maxwell.Certificate.DyadicKernel.Weight
