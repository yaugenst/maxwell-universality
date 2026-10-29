import Maxwell.Certificate.DyadicRectangle
import Maxwell.Certificate.Trigonometric
import Maxwell.Certificate.FourierTransverse

namespace Maxwell.Certificate.GlobalSymbol
open DyadicRectangle FourierBinding

private def one52 : DyadicRectangle := ⟨2^52,0,0⟩
private theorem one52_contains : one52.Contains 52 1 := by norm_num [Contains,one52]

def frequencyIndex (f : Frequency) (j : Fin 3) : Fin 20 :=
  ⟨(reciprocalIndex f j % 20).toNat, by omega⟩

def enclosure (table : Fin 3 → Fin 20 → DyadicRectangle) (f : Frequency) (j : Fin 3) : DyadicRectangle :=
  table j (frequencyIndex f j)

def symbolCheck (roots : Fin 20 → DyadicRectangle) (phases : Fin 3 → DyadicRectangle)
    (table : Fin 3 → Fin 20 → DyadicRectangle) (j : Fin 3) (n : Fin 20) : Bool :=
  mulCheck 52 (roots n) (phases j) ((table j n).add one52)

theorem enclosure_contains (center : Fin 3 → ℚ) (roots : Fin 20 → DyadicRectangle)
    (phases : Fin 3 → DyadicRectangle) (table : Fin 3 → Fin 20 → DyadicRectangle)
    (hr : ∀ n, Trigonometric.cisCheck ((n.val:ℚ)/20) ((roots n).toRectangle 52) = true)
    (hp : ∀ j, Trigonometric.cisCheck (center j/20) ((phases j).toRectangle 52) = true)
    (hm : ∀ j n, symbolCheck roots phases table j n = true)
    (f : Frequency) (j : Fin 3) :
    (enclosure table f j).Contains 52 (symbol (fun i => (center i:ℝ)) f j) := by
  let n := frequencyIndex f j
  have hroot := (contains_iff 52 _ _).mpr (Trigonometric.cisCheck_sound (hr n))
  have hphase := (contains_iff 52 _ _).mpr (Trigonometric.cisCheck_sound (hp j))
  have hprod := mulCheck_sound (hm j n) hroot hphase
  have h := add_contains hprod (neg_contains one52_contains)
  have he : ((table j n).add one52).add one52.neg = table j n := by
    cases ht : table j n
    simp [add,neg,one52]
  change (((table j n).add one52).add one52.neg).Contains 52 _ at h
  rw [he] at h
  have hn : ((n.val:ℕ):ℤ) = reciprocalIndex f j % 20 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hq : (n.val:ℚ) = ((reciprocalIndex f j % 20:ℤ):ℚ) := by exact_mod_cast hn
  rw [hq] at h
  simpa only [enclosure, n, symbol, shiftSymbol_factorization, sub_eq_add_neg] using h

theorem laplacian_contains (c : Maxwell.Spectral.PeriodicYee.Momentum)
    (d : Frequency → Fin 3 → DyadicRectangle) (lap : Frequency → DyadicRectangle)
    (hd : ∀ f j, (d f j).Contains 52 (symbol c f j))
    (h : ∀ f, dotCheck 52 52 (fun j => (d f j).conjugate) (d f) (lap f) = true)
    (f : Frequency) : (lap f).Contains 52 (laplacianSymbol c f : ℂ) := by
  have hh := dotCheck_sound (h f) (fun j => conjugate_contains (hd f j)) (hd f)
  have he : (∑ j, star (symbol c f j)*symbol c f j) = (laplacianSymbol c f : ℂ) := by
    simp only [laplacianSymbol, Complex.ofReal_sum, Complex.star_def]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm, Complex.mul_conj]
  rwa [he] at hh

end Maxwell.Certificate.GlobalSymbol
