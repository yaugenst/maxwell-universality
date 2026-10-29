import Maxwell.Spectral.PrimitiveYee
import Maxwell.Spectral.Concrete
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Data.Rat.Cast.CharZero

/-! Exact rational source representation of the actual primitive Yee matrix
at time-reversal momenta. This is a matrix identity against the frozen
material Bloch fiber, so finite checks can target the operator itself. -/
namespace Maxwell.Certificate.PrimitiveBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Cell20 transverseDirections)

noncomputable section

def differenceQ (k : Translation) (j : Direction) : Matrix Cell Cell ℚ :=
  fun p q =>
    (if q = forwardCell j p then (-1 : ℚ) ^ (∑ a, k a * reduceTranslation (forwardRaw j p) a) else 0) -
    (if q = p then 1 else 0)

def curlQ (k : Translation) : Matrix Face Electric ℚ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then differenceQ k 1 i.2 j.2
    else if j.1 = 1 then -differenceQ k 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then differenceQ k 2 i.2 j.2
    else if j.1 = 2 then -differenceQ k 0 i.2 j.2 else 0
  else
    if j.1 = 1 then differenceQ k 0 i.2 j.2
    else if j.1 = 0 then -differenceQ k 1 i.2 j.2 else 0

def materialQ (r : Cell20) : ℚ := Material.cellValue (Concrete.cellCoordinate r)

def edgeAverageQ (e : Electric) : ℚ :=
  let p := transverseDirections e.1
  let r := representative e.2
  (materialQ (conventionalCell r) + materialQ (conventionalCell (r - rawUnit p.1)) +
    materialQ (conventionalCell (r - rawUnit p.2)) +
    materialQ (conventionalCell (r - rawUnit p.1 - rawUnit p.2))) / 4

def massQ : Matrix Electric Electric ℚ := Matrix.diagonal edgeAverageQ

def fiberQ (k : Translation) : Matrix Electric Electric ℚ :=
  (curlQ k).transpose * curlQ k - (1 / 64 : ℚ) • massQ

theorem difference_binding (k : Translation) (j : Direction) :
    (differenceQ k j).map ((↑) : ℚ → ℂ) = difference (timeReversalMomentum k) j := by
  ext p q
  simp only [Matrix.map_apply, differenceQ, difference, boundaryPhase, character_timeReversal, Rat.cast_sub]
  split_ifs <;> simp

theorem curl_binding (k : Translation) :
    (curlQ k).map ((↑) : ℚ → ℂ) = curl (timeReversalMomentum k) := by
  ext i j
  have hd (a : Direction) : ((differenceQ k a i.2 j.2 : ℚ) : ℂ) =
      difference (timeReversalMomentum k) a i.2 j.2 := congrFun (congrFun (difference_binding k a) i.2) j.2
  simp only [Matrix.map_apply]
  dsimp [curlQ, curl]
  split_ifs <;> simp [hd]

theorem material_binding (r : Cell20) : (materialQ r : ℝ) = Concrete.material r := rfl

theorem edgeAverage_binding (e : Electric) :
    (edgeAverageQ e : ℝ) = edgeAverage Concrete.material e := by
  simp [edgeAverageQ, edgeAverage, material_binding]

theorem mass_binding : massQ.map ((↑) : ℚ → ℂ) = mass Concrete.material := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [massQ, mass, ← edgeAverage_binding]
  · simp [massQ, mass, hij]

/-- The formal matrix is exactly the primitive Maxwell fiber with the
frozen 8000-cell scalar material, not merely a matrix with matching size. -/
theorem fiber_binding (k : Translation) :
    (fiberQ k).map ((↑) : ℚ → ℂ) =
      fiber Concrete.material (timeReversalMomentum k) := by
  have ht : (curlQ k).transpose.map ((↑) : ℚ → ℂ) =
      ((curlQ k).map ((↑) : ℚ → ℂ)).conjTranspose := by
    ext i j
    simp
  have hm : ((1 / 64 : ℚ) • massQ).map ((↑) : ℚ → ℂ) =
      (1 / 64 : ℂ) • massQ.map ((↑) : ℚ → ℂ) := by
    ext i j
    simp
  have hsub : (fiberQ k).map ((↑) : ℚ → ℂ) =
      ((curlQ k).transpose * curlQ k).map ((↑) : ℚ → ℂ) -
      ((1 / 64 : ℚ) • massQ).map ((↑) : ℚ → ℂ) := by
    ext i j
    simp [fiberQ]
  rw [hsub, Matrix.map_mul_ratCast, ht, hm, curl_binding, mass_binding]
  rfl

end
end Maxwell.Certificate.PrimitiveBinding
