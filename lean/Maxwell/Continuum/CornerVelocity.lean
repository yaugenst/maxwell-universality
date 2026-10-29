import Maxwell.Continuum.CornerDecomposition

/-! Exact velocity mean and Gram identities for the full continuum corner. -/

noncomputable section
namespace Maxwell.Continuum.Corner

def velocity (j : Fin 3) (u : ClusterField) : ClusterField :=
  fun s i => waveSigns s j * u s i

theorem character_toggle_parity (p s : Parity) (j : Fin 3) :
    character (toggle p j) s = waveSigns s j * character p s := by
  obtain ⟨p₁, p₂, p₃⟩ := p
  obtain ⟨s₁, s₂, s₃⟩ := s
  cases p₁ <;> cases p₂ <;> cases p₃ <;>
    cases s₁ <;> cases s₂ <;> cases s₃ <;> fin_cases j <;>
    norm_num [character, toggle, waveSigns, sign]

theorem toggle_ne_self (p : Parity) (j : Fin 3) : toggle p j ≠ p := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> fin_cases j <;> decide

theorem toggle_inj_iff (p : Parity) (j k : Fin 3) : toggle p j = toggle p k ↔ j = k := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> fin_cases j <;> fin_cases k <;> decide

theorem velocity_embedding (j : Fin 3) (p : Parity) (v : Vec) :
    velocity j (embedding p v) = embedding (toggle p j) v := by
  ext s i
  simp only [velocity, embedding, character_toggle_parity, Pi.smul_apply, smul_eq_mul]
  ring

theorem velocity_smul (j : Fin 3) (r : ℝ) (u : ClusterField) :
    velocity j (r • u) = r • velocity j u := by
  ext s i
  simp only [velocity, Pi.smul_apply, smul_eq_mul]
  ring

theorem clusterDot_smul_left (r : ℝ) (u v : ClusterField) :
    clusterDot (r • u) v = r * clusterDot u v := by
  simp only [clusterDot, Pi.smul_apply, smul_dotProduct, smul_eq_mul, Finset.mul_sum]

theorem clusterDot_smul_right (r : ℝ) (u v : ClusterField) :
    clusterDot u (r • v) = r * clusterDot u v := by
  simp only [clusterDot, Pi.smul_apply, dotProduct_smul, smul_eq_mul, Finset.mul_sum]

theorem embedding_velocity_mean (p : Parity) (v : Vec) (j : Fin 3) :
    clusterDot (embedding p v) (velocity j (embedding p v)) = 0 := by
  rw [velocity_embedding, embedding_gram]
  simp [Ne.symm (toggle_ne_self p j)]

theorem embedding_velocity_gram (p : Parity) (v : Vec) (j k : Fin 3) :
    clusterDot (velocity j (embedding p v)) (velocity k (embedding p v)) =
      if j = k then 8 * dotProduct v v else 0 := by
  rw [velocity_embedding, velocity_embedding, embedding_gram]
  simp only [toggle_inj_iff]

def normalizedClusterVector : ClusterField :=
  (Real.sqrt 8)⁻¹ • embedding selectedParity normalizedTopVector

theorem normalizedClusterVector_normSq :
    clusterDot normalizedClusterVector normalizedClusterVector = 1 := by
  rw [normalizedClusterVector, clusterDot_smul_left, clusterDot_smul_right,
    embedding_normSq, normalizedTopVector_normSq]
  calc
    _ = 8 / (Real.sqrt 8)^2 := by ring
    _ = 1 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]; norm_num

theorem normalized_velocity_mean (j : Fin 3) :
    clusterDot normalizedClusterVector (velocity j normalizedClusterVector) = 0 := by
  rw [normalizedClusterVector, velocity_smul, clusterDot_smul_left, clusterDot_smul_right,
    embedding_velocity_mean]
  simp

theorem normalized_velocity_gram (j k : Fin 3) :
    clusterDot (velocity j normalizedClusterVector) (velocity k normalizedClusterVector) =
      if j = k then 1 else 0 := by
  rw [normalizedClusterVector, velocity_smul, velocity_smul,
    clusterDot_smul_left, clusterDot_smul_right, embedding_velocity_gram, normalizedTopVector_normSq]
  by_cases h : j = k
  · simp only [h, ite_true, mul_one]
    calc
      _ = 8 / (Real.sqrt 8)^2 := by ring
      _ = 1 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]; norm_num
  · simp [h]

theorem clusterDot_sum_left (u : Fin 3 → ClusterField) (v : ClusterField) :
    clusterDot (∑ j, u j) v = ∑ j, clusterDot (u j) v := by
  simp only [clusterDot, Finset.sum_apply, sum_dotProduct]
  exact Finset.sum_comm

theorem clusterDot_sum_right (u : ClusterField) (v : Fin 3 → ClusterField) :
    clusterDot u (∑ j, v j) = ∑ j, clusterDot u (v j) := by
  simp only [clusterDot, Finset.sum_apply, dotProduct_sum]
  exact Finset.sum_comm

def velocityCombination (t : Vec) (u : ClusterField) : ClusterField :=
  ∑ j, t j • velocity j u

theorem velocityCombination_mean (t : Vec) :
    clusterDot normalizedClusterVector (velocityCombination t normalizedClusterVector) = 0 := by
  simp only [velocityCombination, clusterDot_sum_right, clusterDot_smul_right,
    normalized_velocity_mean, mul_zero, Finset.sum_const_zero]

theorem velocityCombination_normSq (t : Vec) :
    clusterDot (velocityCombination t normalizedClusterVector)
      (velocityCombination t normalizedClusterVector) = dotProduct t t := by
  simp only [velocityCombination, clusterDot_sum_left, clusterDot_smul_left,
    clusterDot_sum_right, clusterDot_smul_right, normalized_velocity_gram]
  simp [dotProduct]

/-- Taking `scale = π` gives the displayed physical free-velocity identity. -/
theorem scaled_velocityCombination_normSq (scale : ℝ) (t : Vec) :
    clusterDot (scale • velocityCombination t normalizedClusterVector)
      (scale • velocityCombination t normalizedClusterVector) = scale^2 * dotProduct t t := by
  rw [clusterDot_smul_left, clusterDot_smul_right, velocityCombination_normSq]
  ring

end Maxwell.Continuum.Corner
