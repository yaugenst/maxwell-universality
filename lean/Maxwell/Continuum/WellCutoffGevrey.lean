import Maxwell.Continuum.WellCutoffDeriv

/-! The quantitative Gevrey bound for the literal three-dimensional Bloch cutoff. -/

noncomputable section

namespace Maxwell.Continuum.Well

theorem factorial_split_bound (K i : ℕ) (hi : i ≤ K) :
    (K.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((K - i).factorial : ℝ) ^ 2 ≤
      (K.factorial : ℝ) ^ 2 := by
  have he : (K.choose i : ℝ) * (i.factorial : ℝ) * ((K - i).factorial : ℝ) = K.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hl : (i.factorial : ℝ) * ((K - i).factorial : ℝ) ≤ K.factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos K) (Nat.factorial_mul_factorial_dvd_factorial hi)
  calc
    (K.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((K - i).factorial : ℝ) ^ 2 =
        ((K.choose i : ℝ) * i.factorial * (K - i).factorial) *
          ((i.factorial : ℝ) * (K - i).factorial) := by ring
    _ = (K.factorial : ℝ) * ((i.factorial : ℝ) * (K - i).factorial) := by rw [he]
    _ ≤ (K.factorial : ℝ) * K.factorial := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = (K.factorial : ℝ) ^ 2 := by ring

theorem gevrey_product (f g : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (Cf Cg R : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hR : 0 ≤ R)
    (x : ℝ)
    (hfb : ∀ n : ℕ, |iteratedDeriv n f x| ≤ Cf * R ^ n * (n.factorial : ℝ) ^ 2)
    (hgb : ∀ n : ℕ, |iteratedDeriv n g x| ≤ Cg * R ^ n * (n.factorial : ℝ) ^ 2)
    (K : ℕ) :
    |iteratedDeriv K (fun t => f t * g t) x| ≤
      (Cf * Cg) * (2 * R) ^ K * (K.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_fun_mul (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (K + 1)) :
      |(K.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (K - i) g x| ≤
        Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2 := by
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (K.choose i : ℝ))]
    calc
      (K.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (K - i) g x| ≤
          (K.choose i : ℝ) * (Cf * R ^ i * (i.factorial : ℝ) ^ 2) *
            (Cg * R ^ (K - i) * ((K - i).factorial : ℝ) ^ 2) := by
        gcongr
        · exact hfb i
        · exact hgb (K - i)
      _ = (Cf * Cg * R ^ K) *
          ((K.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((K - i).factorial : ℝ) ^ 2) := by
        have hp : R ^ i * R ^ (K - i) = R ^ K := by rw [← pow_add, Nat.add_sub_of_le hiK]
        calc
          _ = (Cf * Cg * (R ^ i * R ^ (K - i))) *
              ((K.choose i : ℝ) * (i.factorial : ℝ) ^ 2 * ((K - i).factorial : ℝ) ^ 2) := by ring
          _ = _ := by rw [hp]
      _ ≤ Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (factorial_split_bound K i hiK) (by positivity)
  calc
    |∑ i ∈ Finset.range (K + 1), (K.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (K - i) g x| ≤
        ∑ i ∈ Finset.range (K + 1), |(K.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (K - i) g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (K + 1), Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = (K + 1 : ℝ) * (Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2) := by simp
    _ ≤ (2 : ℝ) ^ K * (Cf * Cg * R ^ K * (K.factorial : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := K))
    _ = (Cf * Cg) * (2 * R) ^ K * (K.factorial : ℝ) ^ 2 := by rw [mul_pow]; ring

def scaledPsi (q₀ a b : ℝ) (t : ℝ) : ℝ := psi ((a + t * b) / q₀)

theorem scaledPsi_contDiff (q₀ a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaledPsi q₀ a b) :=
  psi_contDiff.comp (by fun_prop)

theorem scaledPsi_iteratedDeriv (q₀ a b : ℝ) (K : ℕ) (t : ℝ) :
    iteratedDeriv K (scaledPsi q₀ a b) t =
      (b / q₀) ^ K * iteratedDeriv K psi (a / q₀ + (b / q₀) * t) := by
  have he : scaledPsi q₀ a b = (fun t : ℝ => (fun u : ℝ => psi (a / q₀ + u)) ((b / q₀) * t)) := by
    funext t
    unfold scaledPsi
    congr 1
    ring
  have hs : ContDiff ℝ (K : ℕ) (fun u : ℝ => psi (a / q₀ + u)) :=
    (psi_contDiff.of_le (by simp)).comp (contDiff_const.add contDiff_id)
  rw [he, iteratedDeriv_comp_const_mul hs, iteratedDeriv_comp_const_add]

theorem scaledPsi_gevrey (q₀ a b : ℝ) (hq : 0 < q₀) (hb : |b| ≤ 1) (K : ℕ) (t : ℝ) :
    |iteratedDeriv K (scaledPsi q₀ a b) t| ≤
      16 * (800 / q₀) ^ K * (K.factorial : ℝ) ^ 2 := by
  rw [scaledPsi_iteratedDeriv, abs_mul, abs_pow, abs_div, abs_of_pos hq]
  calc
    (|b| / q₀) ^ K * |iteratedDeriv K psi (a / q₀ + b / q₀ * t)| ≤
        (1 / q₀) ^ K * (16 * (800 : ℝ) ^ K * (K.factorial : ℝ) ^ 2) := by
      gcongr
      exact psi_gevrey K _
    _ = 16 * (800 / q₀) ^ K * (K.factorial : ℝ) ^ 2 := by
      rw [div_pow, div_pow, one_pow]
      ring

theorem chi_directional_gevrey (q₀ : ℝ) (hq : 0 < q₀) (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    |directionalDerivative K (chi q₀) q v| ≤
      (2 : ℝ) ^ 45 * ((2 : ℝ) ^ 16 / q₀) ^ K * (K.factorial : ℝ) ^ 2 := by
  let f : Fin 3 → ℝ → ℝ := fun j => scaledPsi q₀ (q j) (v j)
  let R : ℝ := 800 / q₀
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hf (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (f j) := scaledPsi_contDiff _ _ _
  have hb (j : Fin 3) (n : ℕ) : |iteratedDeriv n (f j) 0| ≤ 16 * R ^ n * (n.factorial : ℝ) ^ 2 := by
    exact scaledPsi_gevrey q₀ (q j) (v j) hq
      (by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le v j).trans hv) n 0
  have h01 (n : ℕ) : |iteratedDeriv n (fun t => f 0 t * f 1 t) 0| ≤
      256 * (2 * R) ^ n * (n.factorial : ℝ) ^ 2 := by
    simpa only [show (16 : ℝ) * 16 = 256 by norm_num] using
      gevrey_product (f 0) (f 1) (hf 0) (hf 1) 16 16 R (by norm_num) (by norm_num) hR 0 (hb 0) (hb 1) n
  have hb2 (n : ℕ) : |iteratedDeriv n (f 2) 0| ≤ 16 * (2 * R) ^ n * (n.factorial : ℝ) ^ 2 := by
    apply (hb 2 n).trans
    gcongr
    linarith
  have h012 := gevrey_product (fun t => f 0 t * f 1 t) (f 2) ((hf 0).mul (hf 1)) (hf 2)
    256 16 (2 * R) (by norm_num) (by norm_num) (by positivity) 0 h01 hb2 K
  have he : (fun t : ℝ => chi q₀ (q + t • v)) = (fun t => (f 0 t * f 1 t) * f 2 t) := by
    funext t
    simp only [chi, Fin.prod_univ_three]
    rfl
  rw [directionalDerivative_eq_line K (chi q₀) (chi_contDiff q₀), he]
  apply h012.trans
  have hbase : 2 * (2 * R) ≤ (2 : ℝ) ^ 16 / q₀ := by
    dsimp [R]
    apply (le_div_iff₀ hq).mpr
    field_simp
    norm_num
  gcongr
  norm_num

end Maxwell.Continuum.Well
