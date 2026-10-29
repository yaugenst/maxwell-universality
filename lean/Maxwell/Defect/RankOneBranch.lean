import Maxwell.Defect.RankOneGap
import Maxwell.Defect.RankOneTransport
import Maxwell.Defect.RankOneAsymptotics

/-! The rank-one branch theorem in an arbitrary finite spectral coordinate
system. All spectral gaps and the orthogonal conjugation are constructed
from the original diagonal spectrum and perturbation vector. -/
namespace Maxwell.Defect

open Module.End

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual skew operator used to eliminate the first-order cross blocks. -/
noncomputable def rankOneGenerator (d : ι → ℝ) (lam c : ℝ) (w : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  euclideanOperator (spectralBlockGenerator d lam
    (-c • Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w)))

/-- A finite explicit constant for the transformed quadratic remainder. -/
noncomputable def rankOneErrorConstant (d : ι → ℝ) (lam c C : ℝ) (w : EuclideanSpace ℝ ι) : ℝ :=
  cayleyErrorConstant (euclideanOperator (Matrix.diagonal d))
    (euclideanOperator (-c • Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w)))
    (rankOneGenerator d lam c w) C

/-- Quantitative rank-one branch selection, including degeneracy of the
selected unperturbed eigenvalue. There is no branch, simple-eigenvalue, or
perturbed-gap hypothesis: these are all conclusions. -/
theorem rankOne_diagonal_branch
    (d : ι → ℝ) (lam c C τ G : ℝ) (w : EuclideanSpace ℝ ι)
    (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (ha : spectralP d lam w ≠ 0) (hc : 0 < c) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hG : 0 ≤ G)
    (hgap : ∀ i, d i ≠ lam → G ≤ |d i - lam|)
    (hXsmall : τ * ‖rankOneGenerator d lam c w‖ ≤ 1)
    (hblock : (c * τ) * (2 * ‖spectralP d lam w‖^2 + ‖spectralQ d lam w‖^2) ≤ G)
    (hsmall : 2 * (rankOneErrorConstant d lam c C w * τ ^ 2) <
      c * τ * ‖spectralP d lam w‖ ^ 2)
    (hS : S.toLinearMap.IsSymmetric)
    (hrem : ‖S - euclideanOperator (Matrix.diagonal d) -
      τ • euclideanOperator (-c • Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w))‖ ≤ C * τ ^ 2) :
    ∃ ν : ℝ, ∃ u : EuclideanSpace ℝ ι, ‖u‖ = 1 ∧ S u = ν • u ∧
      |ν - (lam - c * τ * ‖spectralP d lam w‖ ^ 2)| ≤
        rankOneErrorConstant d lam c C w * τ ^ 2 ∧
      Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 ∧
      ‖u - ‖spectralP d lam w‖⁻¹ • spectralP d lam w‖ ≤
        4 * (rankOneErrorConstant d lam c C w * τ ^ 2) /
          (c * τ * ‖spectralP d lam w‖ ^ 2) + 2 * τ * ‖rankOneGenerator d lam c w‖ ∧
      ∀ (ρ : ℝ) (x : EuclideanSpace ℝ ι), ‖x‖ = 1 → S x = ρ • x → ν ≠ ρ →
        c * τ * ‖spectralP d lam w‖ ^ 2 -
          2 * (rankOneErrorConstant d lam c C w * τ ^ 2) ≤ |ρ - ν| := by
  let B : Matrix ι ι ℝ := -c • Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w)
  let A := euclideanOperator (Matrix.diagonal d)
  let D := euclideanOperator (spectralBlockPart d lam B)
  let X := rankOneGenerator d lam c w
  let a := spectralP d lam w
  let v := ‖a‖⁻¹ • a
  let : Nontrivial (EuclideanSpace ℝ ι) := ⟨⟨a, 0, ha⟩⟩
  have hB : B.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [B, Matrix.vecMulVec, mul_comm]
  have hX : star X = -X := euclidean_spectralBlockGenerator_skew d lam B hB
  have hcancel : euclideanOperator B + (A * X - X * A) = D :=
    euclidean_spectralBlockGenerator_cancel d lam B
  have hR : A + τ • D = euclideanOperator (blockReference d lam (c * τ) w) := by
    rw [blockReference_eq_blockPart]
    simp only [A, D, B, map_add, map_smul]
  obtain ⟨hv, hAv, hrefgap⟩ := blockReference_unit_reference d lam (c * τ) G w
    ha (mul_nonneg hc.le hτ.le) hG hgap hblock
  apply cayley_selected_branch A (euclideanOperator B) D S X τ C
    (lam - c * τ * ‖a‖ ^ 2) (c * τ * ‖a‖ ^ 2) v hτ.le hτ1 hC hXsmall hX hS
    hcancel hrem hv
  · rw [hR]
    exact hAv
  · intro y hy
    rw [hR]
    exact hrefgap y hy
  · exact hsmall

/-- The complete small-parameter branch, with fixed constants and a single
positive interval for all conclusions. -/
theorem rankOne_diagonal_branch_eventually
    (d : ι → ℝ) (lam c C r : ℝ) (w : EuclideanSpace ℝ ι)
    (S : ℝ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (ha : spectralP d lam w ≠ 0) (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r)
    (hS : ∀ τ, (S τ).toLinearMap.IsSymmetric)
    (hrem : ∀ τ, 0 < τ → τ < r →
      ‖S τ - euclideanOperator (Matrix.diagonal d) -
        τ • euclideanOperator (-c • Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w))‖ ≤ C * τ ^ 2) :
    ∃ η K L : ℝ, 0 < η ∧ 0 ≤ K ∧ 0 ≤ L ∧ ∀ τ : ℝ, 0 < τ → τ < η →
      ∃ ν : ℝ, ∃ u : EuclideanSpace ℝ ι, ‖u‖ = 1 ∧ S τ u = ν • u ∧
        |ν - (lam - c * ‖spectralP d lam w‖ ^ 2 * τ)| ≤ K * τ ^ 2 ∧
        Module.finrank ℝ (eigenspace (S τ).toLinearMap ν) = 1 ∧
        ‖u - ‖spectralP d lam w‖⁻¹ • spectralP d lam w‖ ≤ L * τ ∧
        |inner ℝ w u - ‖spectralP d lam w‖| ≤ ‖w‖ * L * τ ∧
        0 < inner ℝ w u ∧
        ∀ (ρ : ℝ) (x : EuclideanSpace ℝ ι), ‖x‖ = 1 → S τ x = ρ • x → ν ≠ ρ →
          c * ‖spectralP d lam w‖ ^ 2 * τ / 2 ≤ |ρ - ν| := by
  let a := spectralP d lam w
  let b := spectralQ d lam w
  let K := rankOneErrorConstant d lam c C w
  let X := ‖rankOneGenerator d lam c w‖
  let L := 4 * K / (c * ‖a‖ ^ 2) + 2 * X
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hK : 0 ≤ K := by dsimp [K, rankOneErrorConstant, cayleyErrorConstant]; positivity
  have hL : 0 ≤ L := by dsimp [L, X]; positivity
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hall
    apply ha
    ext i
    exact hall i
  obtain ⟨i, _⟩ := hex
  let : Nonempty ι := ⟨i⟩
  obtain ⟨G, hG, hgap⟩ := exists_spectral_complement_gap d lam
  obtain ⟨η, hη, hscale⟩ := exists_rankOne_small_scale ‖a‖ ‖b‖ ‖w‖ c G K X hapos hc hG
  refine ⟨min η r, K, L, lt_min hη hr, hK, hL, ?_⟩
  intro τ hτ hτη
  obtain ⟨hτ1, hXsmall, hblock, hsmall, hoverlap⟩ := hscale τ hτ (lt_min_iff.mp hτη).1
  have hbudget : 4 * (K * τ ^ 2) ≤ c * τ * ‖a‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hτ.le
    nlinarith
  have hg : 0 < c * τ * ‖a‖ ^ 2 := by positivity
  have hsmall' : 2 * (K * τ ^ 2) < c * τ * ‖a‖ ^ 2 := by nlinarith
  obtain ⟨ν, u, hu, hSu, hν, hdim, halign, hsep⟩ :=
    rankOne_diagonal_branch d lam c C τ G w (S τ) ha hc hC hτ hτ1 hG.le hgap
      hXsmall hblock hsmall' (hS τ) (hrem τ hτ (lt_min_iff.mp hτη).2)
  have hscalar : 4 * (K * τ ^ 2) / (c * τ * ‖a‖ ^ 2) + 2 * τ * X = L * τ := by
    dsimp [L]
    field_simp
  have halign' : ‖u - ‖a‖⁻¹ • a‖ ≤ L * τ := by
    change ‖u - ‖a‖⁻¹ • a‖ ≤ 4 * (K * τ ^ 2) / (c * τ * ‖a‖ ^ 2) + 2 * τ * X at halign
    rwa [hscalar] at halign
  have hinner : |inner ℝ w u - ‖a‖| ≤ ‖w‖ * L * τ := by
    rw [← projected_normalized_overlap d lam w ha]
    exact (inner_error_le w u (‖a‖⁻¹ • a)).trans
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left halign' (norm_nonneg w))
  have hinnerpos : 0 < inner ℝ w u := by
    have hh := projected_overlap_stable d lam w u ha
      ((mul_le_mul_of_nonneg_left halign' (norm_nonneg w)).trans_lt (by
        simpa [L, mul_assoc] using hoverlap))
    linarith
  refine ⟨ν, u, hu, hSu, ?_, hdim, halign', hinner, hinnerpos, ?_⟩
  · convert hν using 2
    ring
  · intro ρ x hx hSx hne
    have hh := hsep ρ x hx hSx hne
    change c * τ * ‖a‖ ^ 2 - 2 * (K * τ ^ 2) ≤ |ρ - ν| at hh
    change c * ‖a‖ ^ 2 * τ / 2 ≤ |ρ - ν|
    nlinarith

end Maxwell.Defect
