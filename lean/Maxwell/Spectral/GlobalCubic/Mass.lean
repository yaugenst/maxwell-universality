import Maxwell.Spectral.GlobalCubic.Unitary

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (RawCell rawUnit conventionalCell)
open scoped Matrix
set_option maxHeartbeats 2200000
noncomputable section

def rawAverage (m : RawCell → ℝ) (j : Direction) (r : RawCell) : ℝ :=
  let p := transverseDirections j
  (m r+m (r-rawUnit p.1)+m (r-rawUnit p.2)+m (r-rawUnit p.1-rawUnit p.2))/4

theorem rawAverage_binding (m : Cell20 → ℝ) (j : Direction) (r : RawCell) :
    PeriodicYee.edgeAverage m (j,conventionalCell r) = rawAverage (fun r => m (conventionalCell r)) j r := by
  simp only [edgeAverage, rawAverage, ← PrimitiveYee.conventionalCell_rawUnit,
    ← PrimitiveYee.conventionalCell_sub]

theorem rawAverage_action (m : RawCell → ℝ) (g : Generator) (a : ℤ)
    (hm : ∀ r, m (node g a r - if g = .reflect0 then rawUnit 0 else 0) = m r)
    (j : Direction) (r : RawCell) :
    rawAverage m (direction g j)
      (node g a r-if g = .reflect0 ∧ j = 0 then rawUnit 0 else 0) = rawAverage m j r := by
  have h0 := hm r
  have h1 := hm (r-rawUnit 0)
  have h2 := hm (r-rawUnit 1)
  have h3 := hm (r-rawUnit 2)
  have h12 := hm (r-rawUnit 0-rawUnit 1)
  have h13 := hm (r-rawUnit 0-rawUnit 2)
  have h23 := hm (r-rawUnit 1-rawUnit 2)
  cases g <;> fin_cases j <;>
    simp [node_sub_unit, unitImage] at h0 h1 h2 h3 h12 h13 h23 ⊢ <;>
    simp [rawAverage, direction, transverseDirections] <;>
    simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_neg_cancel_left] at h0 h1 h2 h3 h12 h13 h23 ⊢ <;>
    linarith

theorem rawMass_action (m : Cell20 → ℝ) (g : Generator) (a : ℤ)
    (hm : ∀ r, m (conventionalCell (node g a r-if g = .reflect0 then rawUnit 0 else 0)) =
      m (conventionalCell r)) (v : RawField) :
    rawMass m (edgeAction g a v) = edgeAction g a (rawMass m v) := by
  have ha := rawAverage_action (fun r => m (conventionalCell r)) g a hm
  funext j r
  have hj := ha j r
  cases g <;> fin_cases j <;>
    simp [direction] at hj <;>
    simp [rawMass, edgeAction, rawAverage_binding] <;>
    simp [hj]

end
end Maxwell.Spectral.GlobalCubic
