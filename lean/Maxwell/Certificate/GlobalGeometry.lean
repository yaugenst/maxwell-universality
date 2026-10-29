import Maxwell.Certificate.CoverData
import Maxwell.Certificate.FourierBinding

namespace Maxwell.Certificate.FrozenGlobal

def centerQ (i : Fin 2056) (j : Fin 3) : ℚ :=
  ((FrozenCover.matrixBoxes i).lo j + (FrozenCover.matrixBoxes i).hi j)/2

def halfQ (i : Fin 2056) (j : Fin 3) : ℚ :=
  ((FrozenCover.matrixBoxes i).hi j - (FrozenCover.matrixBoxes i).lo j)/2

noncomputable def center (i : Fin 2056) : Maxwell.Spectral.PeriodicYee.Momentum :=
  fun j => (centerQ i j : ℝ)

noncomputable def half (i : Fin 2056) : Maxwell.Spectral.PeriodicYee.Momentum :=
  fun j => (halfQ i j : ℝ)

theorem box_displacement (i : Fin 2056) (x : Maxwell.Spectral.PeriodicYee.Momentum)
    (hx : (FrozenCover.matrixBoxes i).Contains x) (j : Fin 3) :
    |(x-center i) j| ≤ half i j := by
  have hj := hx j
  change |x j - (centerQ i j : ℝ)| ≤ (halfQ i j : ℝ)
  simp only [centerQ, halfQ, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith

theorem point_eq_center_add_displacement (i : Fin 2056)
    (x : Maxwell.Spectral.PeriodicYee.Momentum) : center i+(x-center i)=x := by
  ext j
  simp

end Maxwell.Certificate.FrozenGlobal
