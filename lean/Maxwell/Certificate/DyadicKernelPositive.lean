import Maxwell.Certificate.DyadicKernelVector
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Maxwell.Certificate.DyadicKernel

/-- Three units at the incoming scale leave a strictly positive lower
endpoint after division and the two outward-rounding units. -/
theorem round_pos_of_margin (q : ℕ) (a : Rectangle)
    (h : 3*(2 : ℤ)^q ≤ a.re-(a.radius : ℤ)) :
    0 < (round q a).re-((round q a).radius : ℤ) := by
  have hs : 0 < (2 : ℤ)^q := by positivity
  have hf := Int.ediv_mul_le (a.radius : ℤ) (ne_of_gt hs)
  have he : (a.radius : ℤ)/(2 : ℤ)^q+3 ≤ a.re/(2 : ℤ)^q := by
    apply (Int.le_ediv_iff_mul_le hs).mpr
    nlinarith
  rcases a with ⟨r,i,e⟩
  simp only [round, Int.natCast_add, Int.natCast_ediv, Int.natCast_pow,
    Int.cast_ofNat_Int]
  change (e : ℤ)/(2 : ℤ)^q+3 ≤ r/(2 : ℤ)^q at he
  omega

/-- A shared scalar self-square margin for each of the three phase symbols
certifies the positive denominator used by `projectRound`. -/
theorem laplacianRound_pos_of_self_squares (p : ℕ) (d : Triple)
    (h : ∀ j : Fin 3, 3*(2 : ℤ)^p ≤
      (mulExact (conjugate (d.get j)) (d.get j)).re-
        ((mulExact (conjugate (d.get j)) (d.get j)).radius : ℤ)) :
    0 < (laplacianRound p d).re-((laplacianRound p d).radius : ℤ) := by
  apply round_pos_of_margin
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change 3*(2 : ℤ)^p ≤ (mulExact (conjugate d.x) d.x).re-
    ((mulExact (conjugate d.x) d.x).radius : ℤ) at h0
  change 3*(2 : ℤ)^p ≤ (mulExact (conjugate d.y) d.y).re-
    ((mulExact (conjugate d.y) d.y).radius : ℤ) at h1
  change 3*(2 : ℤ)^p ≤ (mulExact (conjugate d.z) d.z).re-
    ((mulExact (conjugate d.z) d.z).radius : ℤ) at h2
  simp only [dot, add, zero, Int.natCast_add, add_zero]
  have hp : 0 < (2 : ℤ)^p := by positivity
  linarith

end Maxwell.Certificate.DyadicKernel
