import Maxwell.Continuum.BoxCutoffBasic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Uniform operator norms for the first two derivatives of the
actual three-dimensional box cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

def coordinate (N : Fin 3 → ℝ) (j : Fin 3) (x : Space) : ℝ := interval (N j) (x j)

theorem coordinate_contDiff (N : Fin 3 → ℝ) (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (coordinate N j) :=
  (interval_contDiff (N j)).comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Space →L[ℝ] ℝ).contDiff

theorem coordinate_iterated_bound (N : Fin 3 → ℝ) (j : Fin 3) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (coordinate N j) x‖ ≤ |iteratedDeriv n (interval (N j)) (x j)| := by
  let P : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) j
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    change ‖y j‖ ≤ 1*‖y‖
    simpa only [one_mul] using PiLp.norm_apply_le y j
  change ‖iteratedFDeriv ℝ n (interval (N j) ∘ P) x‖ ≤ _
  rw [P.iteratedFDeriv_comp_right (interval_contDiff (N j)) x (by simp)]
  have h := (iteratedFDeriv ℝ n (interval (N j)) (P x)).norm_compContinuousLinearMap_le (fun _ => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  calc
    _ ≤ |iteratedDeriv n (interval (N j)) (x j)| * ‖P‖^n := h
    _ ≤ |iteratedDeriv n (interval (N j)) (x j)| * 1 :=
      mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_left₀ (norm_nonneg P) hP n) (abs_nonneg _)
    _ = _ := mul_one _

theorem coordinate_norm (N : Fin 3 → ℝ) (j : Fin 3) (x : Space) : ‖coordinate N j x‖ ≤ 1 := by
  change ‖interval (N j) (x j)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (interval_nonneg _ _)]
  exact interval_le_one _ _

theorem coordinate_first (N : Fin 3 → ℝ) (j : Fin 3) (x : Space) :
    ‖iteratedFDeriv ℝ 1 (coordinate N j) x‖ ≤ 32 := by
  exact (coordinate_iterated_bound N j 1 x).trans (by simpa using interval_deriv_bound (N j) (x j))

theorem coordinate_second (N : Fin 3 → ℝ) (j : Fin 3) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (coordinate N j) x‖ ≤ 26112 := by
  apply (coordinate_iterated_bound N j 2 x).trans
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using interval_second_bound (N j) (x j)

theorem product_first (f g : Space → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Space) :
    ‖iteratedFDeriv ℝ 1 (fun y => f y*g y) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 1 f x‖*‖g x‖ := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (n := 1) (by simp)
  norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero] at h
  simpa [norm_iteratedFDeriv_zero] using h

theorem product_second (f g : Space → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Space) :
    ‖iteratedFDeriv ℝ 2 (fun y => f y*g y) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 2 f x‖*‖g x‖ := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (n := 2) (by simp)
  norm_num [Finset.sum_range_succ, norm_iteratedFDeriv_zero] at h
  simpa [norm_iteratedFDeriv_zero] using h

theorem value_frechet_bounds (N : Fin 3 → ℝ) (x : Space) :
    ‖iteratedFDeriv ℝ 1 (value N) x‖ ≤ 96 ∧
      ‖iteratedFDeriv ℝ 2 (value N) x‖ ≤ 84480 := by
  let f := coordinate N
  have hf := coordinate_contDiff N
  have h0 := coordinate_norm N
  have h1 := coordinate_first N
  have h2 := coordinate_second N
  have hab0 : ‖f 0 x*f 1 x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (h0 0 x) (h0 1 x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hab1 : ‖iteratedFDeriv ℝ 1 (fun y => f 0 y*f 1 y) x‖ ≤ 64 := by
    apply (product_first _ _ (hf 0) (hf 1) x).trans
    calc
      _ ≤ 1*32+32*1 := add_le_add
        (mul_le_mul (h0 0 x) (h1 1 x) (norm_nonneg _) (by norm_num))
        (mul_le_mul (h1 0 x) (h0 1 x) (norm_nonneg _) (by norm_num))
      _ = _ := by norm_num
  have hab2 : ‖iteratedFDeriv ℝ 2 (fun y => f 0 y*f 1 y) x‖ ≤ 54272 := by
    apply (product_second _ _ (hf 0) (hf 1) x).trans
    calc
      _ ≤ (1 : ℝ)*26112+2*32*32+26112*1 := by gcongr <;> first | exact h0 _ x | exact h1 _ x | exact h2 _ x
      _ = _ := by norm_num
  have he : value N = fun y => (f 0 y*f 1 y)*f 2 y := by
    funext y
    simp only [value, Fin.prod_univ_three, f, coordinate]
  rw [he]
  constructor
  · apply (product_first _ _ ((hf 0).mul (hf 1)) (hf 2) x).trans
    calc
      _ ≤ (1 : ℝ)*32+64*1 := by gcongr <;> first | exact hab0 | exact hab1 | exact h0 _ x | exact h1 _ x
      _ = _ := by norm_num
  · apply (product_second _ _ ((hf 0).mul (hf 1)) (hf 2) x).trans
    calc
      _ ≤ (1 : ℝ)*26112+2*64*32+54272*1 := by
        gcongr <;> first | exact hab0 | exact hab1 | exact hab2 | exact h0 _ x | exact h1 _ x | exact h2 _ x
      _ = _ := by norm_num

#print axioms value_frechet_bounds

end Maxwell.Continuum.BoxCutoff
