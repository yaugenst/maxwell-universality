import Maxwell.Cost.SelectedParameters.BufferCore

namespace Maxwell.Cost.SelectedParameters.Buffer

private theorem loop_price_bound (K N W : ℕ) (hW : 1 ≤ W) :
    8000*W^2+1+N*(K*W^2+8000*W^2+1) ≤ (K+16002)*(N+1)*W^2 := by
  have hs : 1 ≤ W^2 := Nat.one_le_pow _ _ hW
  have hn := Nat.mul_le_mul_left N hs
  nlinarith only [hs,hn]

private theorem factor_bound (K N B W : ℕ) (hW : W ≤ 23*(N+1)*(B+2)) :
    (K+16002)*(N+1)*W^2 ≤ (K+16002)*23^2*(N+1)^3*(B+2)^2 := by
  calc
    _ ≤ (K+16002)*(N+1)*(23*(N+1)*(B+2))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW 2)
    _ = _ := by ring

/-- Cubic in the number of tested buffer indices and quadratic in the input
word width. The fixed coefficient depends only on the finite program. -/
theorem searchCost_polynomial (N B : ℕ) :
    searchCost N B ≤ (3000*8^31+16002)*23^2*(N+1)^3*(B+2)^2 := by
  have h := loop_price_bound (3000*8^31) N (width N B+2) (by omega)
  exact h.trans (factor_bound _ N B _ (by dsimp [width]; nlinarith))

theorem searchCost_mono (N M B C : ℕ) (hn : N ≤ M) (hb : B ≤ C) : searchCost N B ≤ searchCost M C := by
  have hw : width N B ≤ width M C := by unfold width; gcongr
  unfold searchCost testCost advanceCost
  gcongr

def costBound (N B : ℕ) : ℕ := initializationCost B+searchCost N B

private theorem initialization_price_bound (K N B : ℕ) :
    K*(B+3)^2 ≤ K*(N+1)^3*(B+3)^2 := by
  have hn : 1 ≤ (N+1)^3 := Nat.one_le_pow _ _ (by omega)
  have h := Nat.mul_le_mul_right ((B+3)^2) (Nat.mul_le_mul_left K hn)
  simpa only [Nat.mul_one] using h

/-- Initialization and the exact least-success search together have a
polynomial charged cost; the separate logarithmic theorem bounds N. -/
theorem costBound_polynomial (N B : ℕ) :
    costBound N B ≤ (3000*8^32+(3000*8^31+16002)*23^2)*(N+1)^3*(B+3)^2 := by
  have hp := searchCost_polynomial N B
  have hi := initialization_price_bound (3000*8^32) N B
  have hb : (3000*8^31+16002)*23^2*(N+1)^3*(B+2)^2 ≤
      (3000*8^31+16002)*23^2*(N+1)^3*(B+3)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h := Nat.add_le_add hi (hp.trans hb)
  rw [← Nat.add_mul,← Nat.add_mul] at h
  exact h

end Maxwell.Cost.SelectedParameters.Buffer
