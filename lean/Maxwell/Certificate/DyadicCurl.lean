import Maxwell.Certificate.DyadicRectangle
import Maxwell.Certificate.FourierBinding

/-! Integer checks for the actual three-component Fourier curl. -/
namespace Maxwell.Certificate.DyadicRectangle
open Matrix

def curlMatrix (d : Fin 3 → DyadicRectangle) : Fin 3 → Fin 3 → DyadicRectangle :=
  !![zero, (d 2).neg, d 1;
     d 2, zero, (d 0).neg;
     (d 1).neg, d 0, zero]

def adjointCurlMatrix (d : Fin 3 → DyadicRectangle) : Fin 3 → Fin 3 → DyadicRectangle :=
  fun i j => (curlMatrix d j i).conjugate

def curlCheck (p : ℕ) (adjoint : Bool) (d a b : Fin 3 → DyadicRectangle) : Bool :=
  decide (∀ j, dotCheck p p (if adjoint then adjointCurlMatrix d j else curlMatrix d j)
    a (b j) = true)

theorem curlMatrix_contains {p : ℕ} {d : Fin 3 → DyadicRectangle}
    {c : Maxwell.Spectral.PeriodicYee.Momentum} {f : FourierBinding.Frequency}
    (hd : ∀ i, (d i).Contains p (FourierBinding.symbol c f i)) (i j : Fin 3) :
    (curlMatrix d i j).Contains p (FourierBinding.curlSymbolMatrix c f i j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [curlMatrix, FourierBinding.curlSymbolMatrix] <;>
    first | exact zero_contains p | exact hd _ | exact neg_contains (hd _)

theorem curlCheck_sound {p : ℕ} {adjoint : Bool} {d a b : Fin 3 → DyadicRectangle}
    {c : Maxwell.Spectral.PeriodicYee.Momentum} {f : FourierBinding.Frequency}
    {u : Fin 3 → ℂ} (h : curlCheck p adjoint d a b = true)
    (hd : ∀ i, (d i).Contains p (FourierBinding.symbol c f i))
    (hu : ∀ i, (a i).Contains p (u i)) (j : Fin 3) :
    (b j).Contains p (((if adjoint then (FourierBinding.curlSymbolMatrix c f).conjTranspose
      else FourierBinding.curlSymbolMatrix c f) *ᵥ u) j) := by
  have hh : ∀ j, dotCheck p p (if adjoint then adjointCurlMatrix d j else curlMatrix d j)
      a (b j) = true := of_decide_eq_true h
  cases adjoint
  · exact dotCheck_sound (hh j) (fun i => curlMatrix_contains hd j i) hu
  · exact dotCheck_sound (hh j)
      (fun i => conjugate_contains (curlMatrix_contains hd i j)) hu

end Maxwell.Certificate.DyadicRectangle

namespace Maxwell.Certificate.FourierBinding
open Matrix Maxwell.Spectral.PrimitiveYee

theorem frequencyCurl_mulVec (c : Maxwell.Spectral.PeriodicYee.Momentum) (u : Electric → ℂ) (e : Electric) :
    (frequencyCurl c *ᵥ u) e =
      (curlSymbolMatrix c e.2 *ᵥ fun j => u (j, e.2)) e.1 := by
  simp only [frequencyCurl, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp [ite_mul]

theorem frequencyCurl_adjoint_mulVec (c : Maxwell.Spectral.PeriodicYee.Momentum) (u : Electric → ℂ) (e : Electric) :
    ((frequencyCurl c).conjTranspose *ᵥ u) e =
      ((curlSymbolMatrix c e.2).conjTranspose *ᵥ fun j => u (j, e.2)) e.1 := by
  simp only [frequencyCurl, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp [apply_ite, ite_mul]

end Maxwell.Certificate.FourierBinding
