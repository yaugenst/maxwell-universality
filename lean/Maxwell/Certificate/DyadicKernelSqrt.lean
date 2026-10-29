import Maxwell.Certificate.DyadicKernelRounded
import Init.Data.Nat.Sqrt.Basic

namespace Maxwell.Certificate.DyadicKernel

/-- Integer square roots of the scaled endpoints give an outward square-root
rectangle without supplying a proposed root or intermediate enclosure. -/
def sqrtRound (p : Nat) (a : Rectangle) : Option Rectangle :=
  if 0 ≤ a.re-(a.radius:Int) then
    let lo := Nat.sqrt (((a.re-(a.radius:Int))*2^p).toNat)
    let hi := Nat.sqrt (((a.re+(a.radius:Int))*2^p).toNat)+1
    let cr := centerRadius lo hi
    some ⟨cr.1,0,cr.2⟩
  else none

end Maxwell.Certificate.DyadicKernel
