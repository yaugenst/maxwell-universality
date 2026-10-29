import Maxwell.Spectral.GlobalCubic.Action

namespace Maxwell.Spectral.GlobalCubic

open PeriodicYee
open PrimitiveYee (RawCell rawUnit)

def cellAction (g : Generator) (a : ℤ) (r : RawCell) : RawCell :=
  node g a r - if g = .reflect0 then rawUnit 0 else 0

theorem cellAction_sub_unit (g : Generator) (a : ℤ) (r : RawCell) (j : Direction) :
    cellAction g a (r-rawUnit j) = cellAction g a r-unitImage g j := by
  unfold cellAction
  rw [node_sub_unit]
  abel

end Maxwell.Spectral.GlobalCubic
