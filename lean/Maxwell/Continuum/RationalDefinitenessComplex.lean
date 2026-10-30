import Maxwell.Continuum.RationalDefiniteness
import Mathlib.Analysis.Complex.Basic

/-! The rational sign test controls every complex polarization as well. -/

namespace Maxwell.Continuum.Calibration

def complexQuadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (z i)*(A i j : ℂ)*z j

theorem complexQuadratic_re {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℂ) :
    (complexQuadratic A z).re=realQuadratic (rationalMatrixReal A) (fun i => (z i).re)+
      realQuadratic (rationalMatrixReal A) (fun i => (z i).im) := by
  simp only [complexQuadratic,realQuadratic,rationalMatrixReal,Complex.re_sum,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.ratCast_re,Complex.ratCast_im,mul_zero,sub_zero,zero_add]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realQuadratic_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    realQuadratic A 0=0 := by simp [realQuadratic]

theorem negativeTest_complex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j=A j i) :
    negativeTest A=true ↔ ∀ z : Fin n → ℂ, z≠0 → (complexQuadratic A z).re<0 := by
  rw [negativeTest_correct A hA]
  constructor
  · intro h z hz
    rw [complexQuadratic_re]
    have hn (x : Fin n → ℝ) : realQuadratic (rationalMatrixReal A) x≤0 := by
      by_cases hx : x=0
      · rw [hx,realQuadratic_zero]
      · exact (h x hx).le
    by_cases hr : (fun i => (z i).re)=0
    · have hi : (fun i => (z i).im)≠0 := by
        intro hi
        apply hz
        funext i
        apply Complex.ext
        · exact congrFun hr i
        · exact congrFun hi i
      exact add_neg_of_nonpos_of_neg (hn _) (h _ hi)
    · exact add_neg_of_neg_of_nonpos (h _ hr) (hn _)
  · intro h x hx
    have hz : (fun i => (x i : ℂ))≠0 := by
      intro hz
      apply hx
      funext i
      simpa only [Complex.ofReal_re,Pi.zero_apply,Complex.zero_re] using
        congrArg Complex.re (congrFun hz i)
    have he := h (fun i => (x i : ℂ)) hz
    rw [complexQuadratic_re] at he
    simp only [Complex.ofReal_re,Complex.ofReal_im] at he
    change realQuadratic (rationalMatrixReal A) x+realQuadratic (rationalMatrixReal A) 0<0 at he
    simpa only [realQuadratic_zero,add_zero] using he

#print axioms negativeTest_complex

end Maxwell.Continuum.Calibration
