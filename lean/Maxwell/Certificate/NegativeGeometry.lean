import Maxwell.Certificate.NegativeCover.Data
import Maxwell.Certificate.FourierBinding

namespace Maxwell.Certificate.FrozenNegative

def centerQ (i : Fin 604) (j : Fin 3) : ℚ :=
  ((FrozenNegativeCover.matrixBoxes i).lo j + (FrozenNegativeCover.matrixBoxes i).hi j)/2

def halfQ (i : Fin 604) (j : Fin 3) : ℚ :=
  ((FrozenNegativeCover.matrixBoxes i).hi j - (FrozenNegativeCover.matrixBoxes i).lo j)/2

noncomputable def center (i : Fin 604) : Maxwell.Spectral.PeriodicYee.Momentum :=
  fun j => (centerQ i j : ℝ)

noncomputable def half (i : Fin 604) : Maxwell.Spectral.PeriodicYee.Momentum :=
  fun j => (halfQ i j : ℝ)

theorem box_displacement (i : Fin 604) (x : Maxwell.Spectral.PeriodicYee.Momentum)
    (hx : (FrozenNegativeCover.matrixBoxes i).Contains x) (j : Fin 3) :
    |(x-center i) j| ≤ half i j := by
  have hj := hx j
  change |x j - (centerQ i j : ℝ)| ≤ (halfQ i j : ℝ)
  simp only [centerQ, halfQ, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith

theorem point_eq_center_add_displacement (i : Fin 604)
    (x : Maxwell.Spectral.PeriodicYee.Momentum) : center i+(x-center i)=x := by
  ext j
  simp

end Maxwell.Certificate.FrozenNegative
