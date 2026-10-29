import Maxwell.Certificate.DyadicCurl
import Maxwell.Certificate.PointInertia.HighBlock

namespace Maxwell.Certificate.DyadicRectangle
open Matrix

def negativeFrequencySquared : DyadicRectangle := ⟨-(2^46), 0, 0⟩

theorem negativeFrequencySquared_contains :
    negativeFrequencySquared.Contains 52 (-1/64 : ℂ) := by
  norm_num [negativeFrequencySquared, Contains]

def magneticCheck (d weighted field result : Fin 3 → DyadicRectangle) : Bool :=
  decide (∀ j, dotCheck 52 52 (Fin.cons negativeFrequencySquared (curlMatrix d j))
    (Fin.cons (field j) weighted) (result j) = true)

theorem magneticCheck_sound {d weighted field result : Fin 3 → DyadicRectangle}
    {c : Maxwell.Spectral.PeriodicYee.Momentum} {f : FourierBinding.Frequency}
    {v u : Fin 3 → ℂ} (h : magneticCheck d weighted field result = true)
    (hd : ∀ i, (d i).Contains 52 (FourierBinding.symbol c f i))
    (hv : ∀ i, (weighted i).Contains 52 (v i))
    (hu : ∀ i, (field i).Contains 52 (u i)) (j : Fin 3) :
    (result j).Contains 52 ((FourierBinding.curlSymbolMatrix c f *ᵥ v) j - u j/64) := by
  have hh : ∀ j, dotCheck 52 52 (Fin.cons negativeFrequencySquared (curlMatrix d j))
      (Fin.cons (field j) weighted) (result j) = true := of_decide_eq_true h
  have hcoef (i : Fin 4) :
      ((Fin.cons negativeFrequencySquared (curlMatrix d j) : Fin 4 → DyadicRectangle) i).Contains 52
        ((Fin.cons (-1/64 : ℂ) (FourierBinding.curlSymbolMatrix c f j) : Fin 4 → ℂ) i) := by
    refine Fin.cases negativeFrequencySquared_contains (fun k => ?_) i
    exact curlMatrix_contains hd j k
  have hval (i : Fin 4) : ((Fin.cons (field j) weighted : Fin 4 → DyadicRectangle) i).Contains 52
      ((Fin.cons (u j) v : Fin 4 → ℂ) i) := by
    exact Fin.cases (hu j) (fun k => hv k) i
  have hs := dotCheck_sound (hh j) hcoef hval
  rw [Fin.sum_univ_succ] at hs
  simp only [Fin.cons_zero, Fin.cons_succ] at hs
  convert hs using 1
  simp only [Matrix.mulVec, dotProduct]
  ring

end Maxwell.Certificate.DyadicRectangle
