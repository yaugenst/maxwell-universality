import Maxwell.Certificate.DyadicKernel

namespace Maxwell.Certificate.DyadicKernel

structure Triple where
  x : Rectangle
  y : Rectangle
  z : Rectangle
  deriving DecidableEq

def neg : Rectangle → Rectangle
  | ⟨r,i,e⟩ => ⟨-r,-i,e⟩

structure MagneticRow where
  symbol : Triple
  weighted : Triple
  field : Triple
  result : Triple
  deriving DecidableEq

def magneticCheck (a : MagneticRow) : Bool :=
  let t : Rectangle := ⟨-(2^46),0,0⟩
  dotCheck 52 [(t,a.field.x),(zero,a.weighted.x),
    (neg a.symbol.z,a.weighted.y),(a.symbol.y,a.weighted.z)] a.result.x &&
  dotCheck 52 [(t,a.field.y),(a.symbol.z,a.weighted.x),
    (zero,a.weighted.y),(neg a.symbol.x,a.weighted.z)] a.result.y &&
  dotCheck 52 [(t,a.field.z),(neg a.symbol.y,a.weighted.x),
    (a.symbol.x,a.weighted.y),(zero,a.weighted.z)] a.result.z

end Maxwell.Certificate.DyadicKernel
