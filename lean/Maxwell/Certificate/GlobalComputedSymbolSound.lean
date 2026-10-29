import Maxwell.Certificate.GlobalComputedSymbol
import Maxwell.Certificate.DyadicKernelVectorSound
import Maxwell.Certificate.FFTWitness.Constants

namespace Maxwell.Certificate.GlobalComputedSymbol
open DyadicKernel FourierBinding

theorem root_binding (n : Fin 20) : (root n).toDyadic = FFTWitness.roots n := by
  revert n
  decide +kernel

theorem root_contains (n : Fin 20) : (root n).toDyadic.Contains 52
    (Trigonometric.cis ((n.val:ℚ)/20)) := by
  rw [root_binding]
  exact (DyadicRectangle.contains_iff _ _ _).mpr
    (Trigonometric.cisCheck_sound (FFTWitness.roots_checked n))

theorem frequencyIndex_binding (f : Frequency) (j : Fin 3) :
    ((frequencyIndex f j).val:ℤ) = reciprocalIndex f j % 20 := by
  rcases f with ⟨x,y,z⟩
  fin_cases j <;> simp [frequencyIndex, reciprocalIndex] <;> omega

private theorem minusOne_contains :
    (⟨-(2^52),0,0⟩ : Rectangle).toDyadic.Contains 52 (-1:ℂ) := by
  norm_num [Rectangle.toDyadic,DyadicRectangle.Contains]

theorem symbols_contains (c : Fin 3 → ℚ) (phases : Triple)
    (hp : ∀ j, (phases.toVector j).Contains 52 (Trigonometric.cis (c j/20)))
    (f : Frequency) (j : Fin 3) :
    ((symbols phases f).toVector j).Contains 52 (symbol (fun i => (c i:ℝ)) f j) := by
  rw [← Triple.toDyadic_get]
  simp only [symbols,Triple.get_ofFn]
  have ht : (table phases)[j][frequencyIndex f j] =
      add (mulRound 52 (root (frequencyIndex f j)) (phases.get j)) ⟨-(2^52),0,0⟩ := by
    simp [table]
  rw [ht,toDyadic_add]
  have hroot := root_contains (frequencyIndex f j)
  have hn : ((frequencyIndex f j).val:ℚ) = ((reciprocalIndex f j % 20:ℤ):ℚ) := by
    exact_mod_cast frequencyIndex_binding f j
  rw [hn] at hroot
  have hphase : (phases.get j).toDyadic.Contains 52 (Trigonometric.cis (c j/20)) := by
    simpa only [Triple.toDyadic_get] using hp j
  have hh := DyadicRectangle.add_contains (mulRound_contains hroot hphase) minusOne_contains
  simpa only [symbol,shiftSymbol_factorization,sub_eq_add_neg] using hh

end Maxwell.Certificate.GlobalComputedSymbol
