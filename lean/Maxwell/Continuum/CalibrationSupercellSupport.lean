import Maxwell.Continuum.CalibrationSupercellInverse

/-! Finite global-frequency propagation through the actual regrouped
inverse. The radius grows additively with the number of Neumann steps;
it is not multiplied by the supercell length at each application. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

theorem centeredOffset_abs (j : ZMod M) : |centeredOffset M j| ≤ (M : ℤ) := by
  have hj := ZMod.val_lt j
  unfold centeredOffset
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

theorem carrierOffset_abs (j : ZMod M) :
    |((M/2 : ℕ) : ℤ)+centeredOffset M j| ≤ 2*(M : ℤ) := by
  have hh : (((M/2 : ℕ) : ℤ)) ≤ M := by exact_mod_cast Nat.div_le_self M 2
  have h := abs_add_le (((M/2 : ℕ) : ℤ)) (centeredOffset M j)
  rw [abs_of_nonneg (Int.natCast_nonneg _)] at h
  linarith [centeredOffset_abs M j]

theorem joinCoordinate_abs (j : ZMod M) (ν : ℤ) :
    |joinCoordinate M (j,ν)| ≤ (M : ℤ)*|ν|+2*(M : ℤ) := by
  have h := abs_add_le ((M : ℤ)*ν) (((M/2 : ℕ) : ℤ)+centeredOffset M j)
  rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at h
  change |(M : ℤ)*ν+((M/2 : ℕ) : ℤ)+centeredOffset M j| ≤ _
  rw [add_assoc]
  linarith [carrierOffset_abs M j]

theorem joinCoordinate_lower (j : ZMod M) (ν : ℤ) :
    (M : ℤ)*|ν| ≤ |joinCoordinate M (j,ν)|+2*(M : ℤ) := by
  have h := abs_sub (joinCoordinate M (j,ν)) (((M/2 : ℕ) : ℤ)+centeredOffset M j)
  have he : joinCoordinate M (j,ν)-(((M/2 : ℕ) : ℤ)+centeredOffset M j) = (M : ℤ)*ν := by
    unfold joinCoordinate
    ring
  rw [he,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at h
  linarith [carrierOffset_abs M j]

def fiberRadius (R : ℕ) : ℕ := R/M+2

theorem fiberRadius_bound (R : ℕ) (j : ZMod M) (ν : ℤ)
    (hν : |joinCoordinate M (j,ν)| ≤ (R : ℤ)) : |ν| ≤ (fiberRadius M R : ℕ) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM
  have hmod := Nat.mod_lt R hM
  have hdiv := Nat.div_add_mod R M
  have hd : (R : ℤ) < (M : ℤ)*((R/M : ℕ) : ℤ)+(M : ℤ) := by
    have hnat : R < M*(R/M)+M := by omega
    exact_mod_cast hnat
  have hb := joinCoordinate_lower M j ν
  change |ν| ≤ ((R/M+2 : ℕ) : ℤ)
  push_cast
  by_contra hn
  have hn' : ((R/M : ℕ) : ℤ)+3 ≤ |ν| := by omega
  nlinarith

def outputRadius (R K : ℕ) : ℕ := R+M*(K+6)

theorem join_output_bound (R K : ℕ) (j : ZMod M) (ν : ℤ)
    (hν : |ν| ≤ ((fiberRadius M R+K+2 : ℕ) : ℤ)) :
    |joinCoordinate M (j,ν)| ≤ (outputRadius M R K : ℕ) := by
  have hd : (M : ℤ)*((R/M : ℕ) : ℤ) ≤ R := by
    exact_mod_cast Nat.mul_div_le R M
  have hb := joinCoordinate_abs M j ν
  have hm : (0 : ℤ) ≤ M := Int.natCast_nonneg _
  unfold fiberRadius at hν
  unfold outputRadius
  simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_mul] at hν ⊢
  nlinarith

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

omit [Module ℚ V] in
theorem rationalFiber_supported {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (j : Grid M) :
    RationalSupported (fun ν i => f (join M (j,ν)) i) (fiberRadius M R) := by
  intro ν hν i
  obtain ⟨k,hk⟩ := hν
  have hn : (R : ℤ) < |join M (j,ν) k| := by
    by_contra h
    exact (not_lt_of_ge (fiberRadius_bound M R (j k) (ν k) (le_of_not_gt h))) hk
  exact hf _ ⟨k,hn⟩ i

theorem rationalApply_supported {f : Alias → Fin 3 → V} {R : ℕ}
    (hf : RationalSupported f R) (z σ : ℚ) (K P : ℕ) :
    RationalSupported (rationalApply M z σ K P f) (outputRadius M R K) := by
  intro n hn i
  obtain ⟨⟨j,ν⟩,rfl⟩ := (indexEquiv M).surjective n
  change rationalApply M z σ K P f (join M (j,ν)) i = 0
  rw [rationalApply_join]
  apply ((rationalFiber_supported M hf j).gridApply z σ (gridCoordinates M j) K P) ν
  obtain ⟨k,hk⟩ := hn
  refine ⟨k,?_⟩
  by_contra h
  exact (not_lt_of_ge (join_output_bound M R K (j k) (ν k) (le_of_not_gt h))) hk

#print axioms rationalApply_supported

end Maxwell.Continuum.Calibration.Supercell
