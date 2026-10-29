import Maxwell.Continuum.WellCutoffGevrey
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Operator-norm Gevrey estimates for every mixed derivative of the
literal compact cutoff, with a base smaller than the Taylor cutoff scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Well

theorem normGevrey_product (f g : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (Cf Cg R : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hR : 0 ≤ R) (x : Space)
    (hfb : ∀ n : ℕ, ‖iteratedFDeriv ℝ n f x‖ ≤ Cf*R^n*(n.factorial : ℝ)^2)
    (hgb : ∀ n : ℕ, ‖iteratedFDeriv ℝ n g x‖ ≤ Cg*R^n*(n.factorial : ℝ)^2) (K : ℕ) :
    ‖iteratedFDeriv ℝ K (fun y => f y*g y) x‖ ≤ (Cf*Cg)*(2*R)^K*(K.factorial : ℝ)^2 := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range (K+1)) :
      (K.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (K-i) g x‖ ≤
        Cf*Cg*R^K*(K.factorial : ℝ)^2 := by
    have hiK : i ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    calc
      _ ≤ (K.choose i : ℝ)*(Cf*R^i*(i.factorial : ℝ)^2)*
          (Cg*R^(K-i)*((K-i).factorial : ℝ)^2) := by gcongr; exact hfb i; exact hgb (K-i)
      _ = (Cf*Cg*R^K)*
          ((K.choose i : ℝ)*(i.factorial : ℝ)^2*((K-i).factorial : ℝ)^2) := by
        have hp : R^i*R^(K-i)=R^K := by rw [← pow_add, Nat.add_sub_of_le hiK]
        calc
          _ = (Cf*Cg*(R^i*R^(K-i)))*
            ((K.choose i : ℝ)*(i.factorial : ℝ)^2*((K-i).factorial : ℝ)^2) := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_split_bound K i hiK) (by positivity)
  calc
    _ ≤ ∑ i ∈ Finset.range (K+1),
        (K.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (K-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ _i ∈ Finset.range (K+1), Cf*Cg*R^K*(K.factorial : ℝ)^2 := Finset.sum_le_sum hterm
    _ = (K+1 : ℝ)*(Cf*Cg*R^K*(K.factorial : ℝ)^2) := by simp
    _ ≤ (2 : ℝ)^K*(Cf*Cg*R^K*(K.factorial : ℝ)^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := K))
    _ = _ := by rw [mul_pow]; ring

def scaledCoordinate (q₀ : ℝ) (j : Fin 3) : Space →L[ℝ] ℝ :=
  q₀⁻¹ • PiLp.proj 2 (fun _ : Fin 3 => ℝ) j

theorem scaledCoordinate_norm_le {q₀ : ℝ} (hq : 0 < q₀) (j : Fin 3) :
    ‖scaledCoordinate q₀ j‖ ≤ q₀⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hq).le
  intro q
  change ‖q₀⁻¹*q j‖ ≤ q₀⁻¹*‖q‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq)]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le q j) (inv_pos.mpr hq).le

theorem coordinatePsi_frechet {q₀ : ℝ} (hq : 0 < q₀) (j : Fin 3) (K : ℕ) (q : Space) :
    ‖iteratedFDeriv ℝ K (fun x : Space => psi (x j/q₀)) q‖ ≤
      16*(800/q₀)^K*(K.factorial : ℝ)^2 := by
  let L := scaledCoordinate q₀ j
  have he : (fun x : Space => psi (x j/q₀)) = psi ∘ L := by
    funext x
    change psi (x j/q₀)=psi (q₀⁻¹*x j)
    congr 1
    ring
  rw [he, L.iteratedFDeriv_comp_right psi_contDiff q (by simp)]
  have hn := (iteratedFDeriv ℝ K psi (L q)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hn
  calc
    _ ≤ |iteratedDeriv K psi (L q)| * ‖L‖^K := hn
    _ ≤ (16*(800 : ℝ)^K*(K.factorial : ℝ)^2)*(q₀⁻¹)^K := by
      gcongr
      · exact psi_gevrey K _
      · exact scaledCoordinate_norm_le hq j
    _ = _ := by rw [div_pow]; ring

theorem chi_frechet_gevrey (q₀ : ℝ) (hq : 0 < q₀) (K : ℕ) (q : Space) :
    ‖iteratedFDeriv ℝ K (chi q₀) q‖ ≤
      (2 : ℝ)^12 * ((2 : ℝ)^12/q₀)^K * (K.factorial : ℝ)^2 := by
  let f : Fin 3 → Space → ℝ := fun j x => psi (x j/q₀)
  let R : ℝ := 800/q₀
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hf (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f j) := psi_contDiff.comp (by fun_prop)
  have hb (j : Fin 3) (n : ℕ) : ‖iteratedFDeriv ℝ n (f j) q‖ ≤
      16*R^n*(n.factorial : ℝ)^2 := coordinatePsi_frechet hq j n q
  have h01 (n : ℕ) : ‖iteratedFDeriv ℝ n (fun x => f 0 x*f 1 x) q‖ ≤
      256*(2*R)^n*(n.factorial : ℝ)^2 := by
    simpa only [show (16 : ℝ)*16=256 by norm_num] using
      normGevrey_product (f 0) (f 1) (hf 0) (hf 1) 16 16 R (by norm_num) (by norm_num)
        hR q (hb 0) (hb 1) n
  have hb2 (n : ℕ) : ‖iteratedFDeriv ℝ n (f 2) q‖ ≤ 16*(2*R)^n*(n.factorial : ℝ)^2 := by
    apply (hb 2 n).trans
    gcongr
    linarith only [hR]
  have he : chi q₀ = fun x => (f 0 x*f 1 x)*f 2 x := by
    funext x
    simp only [chi, Fin.prod_univ_three]
    rfl
  rw [he]
  apply (normGevrey_product (fun x => f 0 x*f 1 x) (f 2) ((hf 0).mul (hf 1)) (hf 2)
    256 16 (2*R) (by norm_num) (by norm_num) (by positivity) q h01 hb2 K).trans
  have hc : (256 : ℝ)*16=2^12 := by norm_num
  rw [hc]
  gcongr
  dsimp only [R]
  have he : 2*(2*(800/q₀))=3200/q₀ := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (by norm_num) hq.le

#print axioms chi_frechet_gevrey

end Maxwell.Continuum.Well
