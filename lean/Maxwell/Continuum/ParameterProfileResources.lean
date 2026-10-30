import Maxwell.Continuum.ProfileSampleEvaluation
import Maxwell.Continuum.CalibrationPowerStability
import Maxwell.Continuum.CalibrationInversePrecision

/-! Resource bounds for the literal profile and calibration dimensions.
These count finite indices and arithmetic iterations; compiled machine
costs are accounted for separately. -/

namespace Maxwell.Continuum.Parameters
open Profile Calibration
set_option maxHeartbeats 800000

private theorem clog_profile_degree (N : ℕ) :
    Nat.clog 2 (profileDegree N+1) ≤ 31+2*(N+1) := by
  apply Nat.clog_le_of_le_pow
  have hp : (N+1)^2 ≤ (2^(N+1))^2 := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := N+1)).le 2
  have hd := (profileDegree_bound N).trans (Nat.mul_le_mul_left (2^30) hp)
  have he : 2^30*(2^(N+1))^2 = 2^(30+2*(N+1)) := by rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [he] at hd
  have hpos : 0 < 2^(30+2*(N+1)) := by positivity
  have hs : 2^(31+2*(N+1))=2*2^(30+2*(N+1)) := by
    rw [show 31+2*(N+1)=1+(30+2*(N+1)) by omega,pow_add,pow_one]
  rw [hs]
  omega

theorem profileWorkBits_bound (N : ℕ) : profileWorkBits N ≤ 131*(N+1) := by
  have h := clog_profile_degree N
  unfold profileWorkBits
  omega

theorem profileGrid_bound (N : ℕ) : profileGrid N ≤ 2^46*(N+1)^2 := by
  have hw := profileWorkBits_bound N
  have hw' : profileWorkBits N+1 ≤ 132*(N+1) := by omega
  have hD := profileDegree_bound N
  have hM := (profileDegree_bound (profileWorkBits N)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw' 2))
  have h1 : 1 ≤ (N+1)^2 := one_le_pow₀ (by omega)
  unfold profileGrid
  nlinarith only [hD,hM,h1]

theorem profile_phase_bits_bound (N : ℕ) :
    phaseBits (profileDegree N+1) (profileWorkBits N) ≤ 200*(N+1) := by
  have hw := profileWorkBits_bound N
  have hc : Nat.clog 2 (profileDegree N+2) ≤ 32+2*(N+1) := by
    apply Nat.clog_le_of_le_pow
    have h := Nat.le_pow_clog (by decide : 1 < 2) (profileDegree N+1)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (clog_profile_degree N)
    have hd := h.trans hp
    have hpos : 0 < 2^(31+2*(N+1)) := by positivity
    rw [show 32+2*(N+1)=1+(31+2*(N+1)) by omega,pow_add,pow_one]
    omega
  unfold phaseBits
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

theorem profile_phase_taylor_bound (N : ℕ) :
    taylorOrder (10*(profileDegree N+1+1)) (profileWorkBits N+3) ≤
      2^80*(N+1)^4 := by
  have hD := profileDegree_bound N
  have hw := profileWorkBits_bound N
  have h1 : 1 ≤ (N+1)^2 := one_le_pow₀ (by omega)
  have hB : 10*(profileDegree N+1+1) ≤ 2^35*(N+1)^2 := by nlinarith only [hD,h1]
  have hsq := Nat.pow_le_pow_left hB 2
  have hN : N+1 ≤ (N+1)^4 := le_self_pow₀ (by omega : 1 ≤ N+1) (by decide : (4 : ℕ) ≠ 0)
  have h4 : 1 ≤ (N+1)^4 := one_le_pow₀ (by omega)
  unfold taylorOrder taylorHalfOrder
  nlinarith only [hsq,hw,hN,h4]

private instance profileGrid_neZero (N : ℕ) : NeZero (profileGrid N) :=
  ⟨(profileGrid_pos N).ne'⟩

/-- Exact rectangular index count of the direct coefficient/sample transform. -/
theorem profile_sampling_pair_count (N : ℕ) :
    Fintype.card (Fin (profileDegree N+1) × ZMod (profileGrid N)) ≤ 2^78*(N+1)^4 := by
  rw [Fintype.card_prod,Fintype.card_fin,ZMod.card]
  have h1 : 1 ≤ (N+1)^2 := one_le_pow₀ (by omega)
  have hd : profileDegree N+1 ≤ 2^31*(N+1)^2 := by have := profileDegree_bound N; nlinarith
  have hp := Nat.mul_le_mul hd (profileGrid_bound N)
  apply hp.trans
  nlinarith only [show 0 ≤ (N+1)^4 from Nat.zero_le _]

/-- A fully copied three-dimensional tensor coefficient array. -/
theorem profile_tensor_index_count (N : ℕ) :
    Fintype.card (Fin 3 → Fin (profileDegree N+1)) ≤ 2^93*(N+1)^6 := by
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_fin]
  have h1 : 1 ≤ (N+1)^2 := one_le_pow₀ (by omega)
  have hd : profileDegree N+1 ≤ 2^31*(N+1)^2 := by have := profileDegree_bound N; nlinarith
  calc
    _ ≤ (2^31*(N+1)^2)^3 := Nat.pow_le_pow_left hd 3
    _ = _ := by ring

theorem powerSteps_bound (N : ℕ) : powerSteps N ≤ 2^114*(N+1) := by
  unfold powerSteps
  nlinarith

theorem powerWorkPrecision_bound (N : ℕ) : powerWorkPrecision N ≤ 2^122*(N+1) := by
  have hs := powerSteps_bound N
  have hc : Nat.clog 2 (powerSteps N+1) ≤ powerSteps N+1 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := powerSteps N+1)).le
  unfold powerWorkPrecision powerWorkBits
  omega

theorem aliasSteps_bound {N ℓ C : ℕ} (hℓ : 0 < ℓ) (hN : N ≤ C*ℓ) :
    aliasSteps N ℓ ≤ (C+16+2^20)*ℓ := by
  unfold aliasSteps
  nlinarith only [hN,hℓ]

#print axioms profileWorkBits_bound
#print axioms profileGrid_bound
#print axioms profile_phase_taylor_bound
#print axioms profile_sampling_pair_count
#print axioms profile_tensor_index_count
#print axioms powerWorkPrecision_bound

end Maxwell.Continuum.Parameters
