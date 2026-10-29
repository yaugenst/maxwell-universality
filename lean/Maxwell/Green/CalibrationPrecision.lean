import Maxwell.Green.FiniteCalibration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact rational degree selection for binary inverse precision. The
one-time contraction block depends only on the fixed physical gap and norm
enclosures; the requested precision contributes linearly to the degree. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000

def inverseFactor (δ M : ℚ) : ℚ := 1 - δ ^ 2 / M ^ 2

theorem inverseFactor_range (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) :
    0 ≤ inverseFactor δ M ∧ inverseFactor δ M < 1 := by
  unfold inverseFactor
  have hp : 0 < M ^ 2 := sq_pos_of_pos hM
  have hle : δ ^ 2 / M ^ 2 ≤ 1 :=
    (div_le_one hp).mpr (pow_le_pow_left₀ hδ.le hδM 2)
  have hpos : 0 < δ ^ 2 / M ^ 2 := div_pos (sq_pos_of_pos hδ) hp
  constructor <;> linarith

theorem exists_precisionBlock (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) :
    ∃ k : ℕ, inverseFactor δ M ^ k ≤ 1 / 2 ∧ inverseFactor δ M ^ k ≤ δ := by
  have hr := inverseFactor_range δ M hδ hM hδM
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (lt_min (by norm_num : (0 : ℚ) < 1 / 2) hδ) hr.2
  exact ⟨k, (hk.trans_le (min_le_left _ _)).le, (hk.trans_le (min_le_right _ _)).le⟩

/-- A terminating search over exact rational powers, performed once for
fixed gap and norm data; no real-number oracle is queried. -/
def precisionBlock (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) : ℕ :=
  Nat.find (exists_precisionBlock δ M hδ hM hδM)

def precisionDegree (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) (b : ℕ) : ℕ :=
  precisionBlock δ M hδ hM hδM * (b + 1)

theorem precisionBlock_spec (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) :
    inverseFactor δ M ^ precisionBlock δ M hδ hM hδM ≤ 1 / 2 ∧
      inverseFactor δ M ^ precisionBlock δ M hδ hM hδM ≤ δ :=
  Nat.find_spec (exists_precisionBlock δ M hδ hM hδM)

theorem precisionBlock_pos (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) :
    0 < precisionBlock δ M hδ hM hδM := by
  have h := (precisionBlock_spec δ M hδ hM hδM).1
  by_contra hn
  have he : precisionBlock δ M hδ hM hδM = 0 := by omega
  rw [he, pow_zero] at h
  norm_num at h

theorem precisionDegree_error (δ M : ℚ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) (b : ℕ) :
    δ⁻¹ * inverseFactor δ M ^ (precisionDegree δ M hδ hM hδM b + 1) ≤ (1 / 2 : ℚ) ^ b := by
  let r := inverseFactor δ M
  let k := precisionBlock δ M hδ hM hδM
  have hr := inverseFactor_range δ M hδ hM hδM
  have hk := precisionBlock_spec δ M hδ hM hδM
  have hinv : δ⁻¹ * r ^ k ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hδ).mpr hk.2
  have hpower : r ^ (precisionDegree δ M hδ hM hδM b) = r ^ k * (r ^ k) ^ b := by
    dsimp only [precisionDegree, k]
    rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
    ring
  calc
    _ ≤ δ⁻¹ * r ^ (precisionDegree δ M hδ hM hδM b) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hδ.le)
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hr.1 _) hr.2.le
    _ = (δ⁻¹ * r ^ k) * (r ^ k) ^ b := by rw [hpower]; ring
    _ ≤ 1 * (1 / 2 : ℚ) ^ b :=
      mul_le_mul hinv (pow_le_pow_left₀ (pow_nonneg hr.1 k) hk.1 b)
        (pow_nonneg (pow_nonneg hr.1 k) b) (by norm_num)
    _ = _ := one_mul _

/-- Exact compact matrix evaluation inherits the true infinite-operator
error, at a degree linear in the number of requested binary digits. -/
theorem compactCompression_binary_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : ι ↪ Edge) (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z δ M : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), (δ : ℝ) ≤ |x|) (b : ℕ) :
    ‖compressionOperator edges (Ring.inverse (operator m K hK hm z)) -
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        ((compactCompression (coordinateBasis edges) m z ((M ^ 2)⁻¹)
          (precisionDegree δ M hδ hM hδM b)).map ((↑) : ℚ → ℂ))‖ ≤ (1 / 2 : ℝ)^b := by
  rw [compactCompression_eq _ m K hK hm]
  have he := rationalCompressionOperator_spectral_error edges m K hK hm z M (δ : ℝ)
    (precisionDegree δ M hδ hM hδM b) (by exact_mod_cast hδ) (by exact_mod_cast hM)
    (by exact_mod_cast hδM) hnorm hgap
  apply he.trans
  have hb := precisionDegree_error δ M hδ hM hδM b
  unfold inverseFactor at hb
  have hc := (Rat.cast_le (K := ℝ)).mpr hb
  simpa only [Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_sub, Rat.cast_one,
    Rat.cast_div, Rat.cast_ofNat] using hc

end Maxwell.Defect.FiniteStencil
