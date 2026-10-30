import Maxwell.Continuum.CalibrationLatticeWeight

/-! Explicit summation of stretched-exponential periodic-image tails.
The entire three-dimensional lattice is included. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

def imageRadius (j : Fin 3 → ℤ) : ℕ := Finset.univ.sup (fun i => (j i).natAbs)

theorem coordinate_le_imageRadius (j : Fin 3 → ℤ) (i : Fin 3) :
    |(j i : ℝ)| ≤ (imageRadius j : ℝ) := by
  have h : (j i).natAbs ≤ imageRadius j :=
    Finset.le_sup (f := fun i : Fin 3 => (j i).natAbs) (Finset.mem_univ i)
  have hc : ((j i).natAbs : ℝ) ≤ (imageRadius j : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hc

theorem imageRadius_pos {j : Fin 3 → ℤ} (hj : j ≠ 0) : 0 < imageRadius j := by
  by_contra h
  have hr : imageRadius j = 0 := by omega
  apply hj
  funext i
  have hb : (j i).natAbs ≤ imageRadius j :=
    Finset.le_sup (f := fun i : Fin 3 => (j i).natAbs) (Finset.mem_univ i)
  have hz : (j i).natAbs = 0 := by omega
  exact Int.natAbs_eq_zero.mp hz

theorem latticeWeight_radial_lower (j : Fin 3 → ℤ) :
    1/(1+(imageRadius j : ℝ))^6 ≤ latticeWeight j := by
  have hp : (∏ _i : Fin 3, (1/(1+(imageRadius j : ℝ))^2)) ≤ latticeWeight j := by
    apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro i _
    apply one_div_le_one_div_of_le (by positivity)
    have hc := coordinate_le_imageRadius j i
    nlinarith [abs_nonneg (j i : ℝ)]
  calc
    _ = ∏ _i : Fin 3, (1/(1+(imageRadius j : ℝ))^2) := by simp; ring
    _ ≤ _ := hp

def latticeDecayConstant (b : ℝ) : ℝ := 64*(12 : ℕ).factorial/b^12

theorem latticeDecayConstant_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ latticeDecayConstant b := by
  unfold latticeDecayConstant
  positivity

theorem stretched_lattice_majorant {b : ℝ} (hb : 0 < b) (j : Fin 3 → ℤ) (hj : j ≠ 0) :
    Real.exp (-b*Real.sqrt (imageRadius j)) ≤ latticeDecayConstant b*latticeWeight j := by
  let r : ℝ := imageRadius j
  have hr : 1 ≤ r := by
    change 1 ≤ (imageRadius j : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (imageRadius_pos hj)
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hs : (Real.sqrt r)^12 = r^6 := by
    rw [show (12 : ℕ) = 2*6 by norm_num,pow_mul,Real.sq_sqrt hr0]
  have hf := Well.pow_mul_exp_neg_le_factorial (b*Real.sqrt r) (by positivity) 12
  rw [mul_pow,hs] at hf
  have hp : (1+r)^6 ≤ 64*r^6 := by
    calc
      _ ≤ (2*r)^6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
      _ = _ := by ring
  have hrbound : r^6*Real.exp (-b*Real.sqrt r) ≤ ((12 : ℕ).factorial : ℝ)/b^12 := by
    apply (le_div_iff₀ (pow_pos hb 12)).mpr
    convert hf using 1
    ring
  have he : Real.exp (-b*Real.sqrt r) ≤ latticeDecayConstant b/(1+r)^6 := by
    apply (le_div_iff₀ (by positivity : 0 < (1+r)^6)).mpr
    calc
      _ = (1+r)^6*Real.exp (-b*Real.sqrt r) := mul_comm _ _
      _ ≤ (64*r^6)*Real.exp (-b*Real.sqrt r) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = 64*(r^6*Real.exp (-b*Real.sqrt r)) := by ring
      _ ≤ 64*(((12 : ℕ).factorial : ℝ)/b^12) :=
        mul_le_mul_of_nonneg_left hrbound (by norm_num)
      _ = _ := by unfold latticeDecayConstant; ring
  apply he.trans
  change latticeDecayConstant b/(1+(imageRadius j : ℝ))^6 ≤ _
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using latticeWeight_radial_lower j)
    (latticeDecayConstant_nonneg hb)

def imageTail (a : ℝ) (j : Fin 3 → ℤ) : ℝ :=
  if j = 0 then 0 else Real.exp (-a*Real.sqrt (imageRadius j))

theorem imageTail_nonneg (a : ℝ) (j : Fin 3 → ℤ) : 0 ≤ imageTail a j := by
  unfold imageTail
  split_ifs <;> positivity

theorem imageTail_majorant {a b : ℝ} (hb : 0 < b) (hab : 2*b ≤ a) (j : Fin 3 → ℤ) :
    imageTail a j ≤ (Real.exp (-a/2)*latticeDecayConstant b)*latticeWeight j := by
  by_cases hj : j = 0
  · rw [imageTail,ite_eq_left hj]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (latticeDecayConstant_nonneg hb))
      (latticeWeight_nonneg j)
  · rw [imageTail,ite_eq_right hj]
    have hr : (1 : ℝ) ≤ imageRadius j := by exact_mod_cast imageRadius_pos hj
    have hs : 1 ≤ Real.sqrt (imageRadius j) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
    have he : Real.exp (-a*Real.sqrt (imageRadius j)) ≤
        Real.exp (-a/2)*Real.exp (-b*Real.sqrt (imageRadius j)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    exact he.trans ((mul_le_mul_of_nonneg_left (stretched_lattice_majorant hb j hj)
      (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm)

theorem imageTail_summable {a b : ℝ} (hb : 0 < b) (hab : 2*b ≤ a) : Summable (imageTail a) :=
  Summable.of_nonneg_of_le (imageTail_nonneg a) (imageTail_majorant hb hab)
    (latticeWeight_summable.mul_left (Real.exp (-a/2)*latticeDecayConstant b))

theorem imageTail_tsum_bound {a b : ℝ} (hb : 0 < b) (hab : 2*b ≤ a) :
    ∑' j : Fin 3 → ℤ,imageTail a j ≤ 64*latticeDecayConstant b*Real.exp (-a/2) := by
  calc
    _ ≤ ∑' j : Fin 3 → ℤ,(Real.exp (-a/2)*latticeDecayConstant b)*latticeWeight j :=
      (imageTail_summable hb hab).tsum_le_tsum (imageTail_majorant hb hab)
        (latticeWeight_summable.mul_left _)
    _ = (Real.exp (-a/2)*latticeDecayConstant b)*(∑' j : Fin 3 → ℤ,latticeWeight j) := tsum_mul_left
    _ ≤ (Real.exp (-a/2)*latticeDecayConstant b)*64 :=
      mul_le_mul_of_nonneg_left latticeWeight_tsum_le
        (mul_nonneg (Real.exp_pos _).le (latticeDecayConstant_nonneg hb))
    _ = _ := by ring

#print axioms imageTail_tsum_bound

end Maxwell.Continuum.Calibration
