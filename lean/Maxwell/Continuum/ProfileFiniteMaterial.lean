import Maxwell.Continuum.ProfileEncoded
import Maxwell.Continuum.FiniteWellMaterial

/-! Literal finite material profiles have uniform error independent of the number of wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Metric Auxiliary

variable {ι : Type*} [Fintype ι]

theorem disjoint_sum_bound (s : ι → Set Space) (f : ι → Space → ℝ)
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j)) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ i x, x ∉ s i → f i x=0) (hb : ∀ i x, |f i x| ≤ B) (x : Space) :
    |∑ i, f i x| ≤ B := by
  classical
  by_cases hx : ∃ i, x ∈ s i
  · obtain ⟨i,hi⟩ := hx
    have he : (∑ j, f j x)=f i x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hz j x (fun hj => Set.disjoint_left.mp (hdisj hji) hj hi)
      · simp
    rw [he]
    exact hb i x
  · have hf (i : ι) : f i x=0 := hz i x (fun hi => hx ⟨i,hi⟩)
    simpa only [hf, Finset.sum_const_zero, abs_zero] using hB

theorem scaled_norm_of_outside {h : ℝ} (hh : 0<h) (r x : Space) (hx : x ∉ ball r h⁻¹) :
    1 ≤ ‖h • (x-r)‖ := by
  have hn : h⁻¹ ≤ ‖x-r‖ := le_of_not_gt (by simpa only [mem_ball, dist_eq_norm] using hx)
  rw [norm_smul, Real.norm_of_nonneg hh.le]
  have ht := mul_le_mul_of_nonneg_left hn hh.le
  rwa [mul_inv_cancel₀ hh.ne'] at ht

def encodedWellCoefficient (N : ℕ) (h : ℝ) (r : ι → Space) (v : ι → ℝ) (x : Space) : ℝ :=
  ∑ i, v i*(encodedRoot N (h • (x-r i)))^2

theorem encodedWellCoefficient_continuous (N : ℕ) (h : ℝ) (r : ι → Space) (v : ι → ℝ) :
    Continuous (encodedWellCoefficient N h r v) := by
  change Continuous (fun x : Space => ∑ i, v i*(encodedRoot N (h • (x-r i)))^2)
  apply continuous_finsetSum
  intro i _
  have hi : Continuous (fun x : Space => h • (x-r i)) :=
    (continuous_id.sub continuous_const).const_smul h
  exact continuous_const.mul (((encodedRoot_contDiff N).continuous.comp hi).pow 2)

theorem encodedWellCoefficient_nonneg (N : ℕ) (h : ℝ) (r : ι → Space) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (x : Space) : 0 ≤ encodedWellCoefficient N h r v x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (sq_nonneg _))

theorem encodedWellCoefficient_error (N : ℕ) {h V : ℝ} (hh : 0<h) (hV : 0≤V)
    (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (ball (r i) h⁻¹) (ball (r j) h⁻¹)) (x : Space) :
    |finiteWellCoefficient h r v x-encodedWellCoefficient N h r v x| ≤
      3*V*(1/2 : ℝ)^(N+24) := by
  have hz (i : ι) (y : Space) (hy : y ∉ ball (r i) h⁻¹) :
      v i*(Well.w (h • (y-r i))-(encodedRoot N (h • (y-r i)))^2)=0 := by
    have hn := scaled_norm_of_outside hh (r i) y hy
    rw [(Well.w_zero_iff _).mpr hn, encodedRoot_zero hn, zero_pow (by decide : (2 : ℕ) ≠ 0),
      sub_self, mul_zero]
  have hb (i : ι) (y : Space) :
      |v i*(Well.w (h • (y-r i))-(encodedRoot N (h • (y-r i)))^2)| ≤
        3*V*(1/2 : ℝ)^(N+24) := by
    rw [abs_mul]
    have hh := mul_le_mul (hv i) (encodedRoot_square_error N (h • (y-r i))) (abs_nonneg _) hV
    exact hh.trans_eq (by ring)
  have hs := disjoint_sum_bound (fun i => ball (r i) h⁻¹)
    (fun i y => v i*(Well.w (h • (y-r i))-(encodedRoot N (h • (y-r i)))^2))
    hdisj (by positivity) hz hb x
  simpa only [finiteWellCoefficient, encodedWellCoefficient, mul_sub, Finset.sum_sub_distrib] using hs

theorem encodedWellCoefficient_bound (N : ℕ) {h V : ℝ} (hh : 0<h) (hV : 0≤V)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0≤v i) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (ball (r i) h⁻¹) (ball (r j) h⁻¹)) (x : Space) :
    encodedWellCoefficient N h r v x ≤ 4*V := by
  have he := encodedWellCoefficient_error N hh hV r v
    (fun i => by simpa only [abs_of_nonneg (hv0 i)] using hv i) hdisj x
  have hi := (finiteWellCoefficient_bounds hh hV r v hv0 hv hdisj x).2
  have hp : (1/2 : ℝ)^(N+24) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith only [he, (abs_le.mp he).1, hi, mul_le_mul_of_nonneg_left hp hV]

#print axioms encodedWellCoefficient_error
#print axioms encodedWellCoefficient_bound

end Maxwell.Continuum.Profile
