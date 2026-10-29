import Maxwell.Cost.SelectedParameters.Geometric
import Maxwell.Realization.Precision

namespace Maxwell.Cost.SelectedParameters.Geometric

private theorem loop_bound (J N W : ℕ) (hw : 1 ≤ W) :
    8000*W^2+1+N*(J*W^2+8000*W^2+1) ≤ (J+16002)*(N+1)*W^2 := by
  have hs : 1 ≤ W^2 := Nat.one_le_pow _ _ hw
  have hn := Nat.mul_le_mul_left N hs
  nlinarith only [hs,hn]

private theorem width_bound (N A B : ℕ) : width N A B+2 ≤ (N+1)*(A+B+3) := by
  dsimp [width]
  nlinarith

private theorem factor_bound (J N A B W : ℕ) (hw : W ≤ (N+1)*(A+B+3)) :
    (J+16002)*(N+1)*W^2 ≤ (J+16002)*(N+1)^3*(A+B+3)^2 := by
  calc
    _ ≤ (J+16002)*(N+1)*((N+1)*(A+B+3))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)
    _ = _ := by ring

private theorem initial_bound (I N A B : ℕ) :
    I*(B+2)^2 ≤ I*(N+1)^3*(A+B+3)^2 := by
  have hn : 1 ≤ (N+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hi : I ≤ I*(N+1)^3 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left I hn
  exact Nat.mul_le_mul hi (Nat.pow_le_pow_left (by omega) 2)

/-- Fixed-base least-power selection has a polynomial charged cost in the
searched exponent and the runtime input-word width. -/
theorem cost_polynomial (N A B : ℕ) :
    initialCost B+searchCost N A B ≤
      (3000*8^11+(3000*8^5+16002))*(N+1)^3*(A+B+3)^2 := by
  have hs : searchCost N A B ≤ (3000*8^5+16002)*(N+1)^3*(A+B+3)^2 :=
    (loop_bound (3000*8^5) N (width N A B+2) (by omega)).trans
      (factor_bound _ N A B _ (width_bound N A B))
  have hi := initial_bound (3000*8^11) N A B
  have ht := Nat.add_le_add hi hs
  rw [← Nat.add_mul,← Nat.add_mul] at ht
  exact ht

/-- Binary precision is the same least-exponent search even when the
positive budget is larger than one; the cap does not require an extra
approximation or an assumed iteration count. -/
theorem binary_exponent (c d : ℕ) (hc : 0 < c) (hd : 0 < d) :
    exponent 1 2 c d (by decide) (by decide) hc hd =
      Maxwell.Realization.precisionBits ((c:ℚ)/d)
        (div_pos (by exact_mod_cast hc) (by exact_mod_cast hd)) := by
  let target := (c:ℚ)/d
  have he : ∀ n : ℕ, (1/2:ℚ)^n ≤ target ↔ (1/2:ℚ)^n ≤ min 1 target := by
    intro n
    have hpow : (1/2:ℚ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact ⟨fun h => le_min hpow h,fun h => h.trans (min_le_right _ _)⟩
  unfold exponent Realization.precisionBits Realization.geometricSteps
  apply Nat.find_congr'
  exact he _

end Maxwell.Cost.SelectedParameters.Geometric
