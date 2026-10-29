import Maxwell.Defect.ScalarDefect
import Maxwell.Spectral.Bloch
import Maxwell.Defect.CoherentSource
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

/-! Concrete all-cell cubes in the fine Yee lattice, with the exact
conventional-cell support and interior weights used by the coherent source. -/

namespace Maxwell.Defect.ScalarDefect
open Spectral Spectral.Lattice

def cube (L : ℕ) : Finset Site :=
  Fintype.piFinset fun _ => Finset.Icc (-2 : ℤ) (20 * (L : ℤ) + 2)

def interiorPeriods (L : ℕ) : Finset Site :=
  Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) ((L : ℤ) - 1)

def supportPeriods (L : ℕ) : Finset Site :=
  Fintype.piFinset fun _ => Finset.Icc (-1 : ℤ) (L : ℤ)

theorem mem_cube (L : ℕ) (x : Site) :
    x ∈ cube L ↔ ∀ j, -2 ≤ x j ∧ x j ≤ 20 * (L : ℤ) + 2 := by
  simp [cube, Fintype.mem_piFinset]

theorem mem_interiorPeriods (L : ℕ) (x : Site) :
    x ∈ interiorPeriods L ↔ ∀ j, 0 ≤ x j ∧ x j < (L : ℤ) := by
  simp only [interiorPeriods, Fintype.mem_piFinset, Finset.mem_Icc]
  exact forall_congr' fun _ => and_congr_right fun _ => by omega

theorem mem_supportPeriods (L : ℕ) (x : Site) :
    x ∈ supportPeriods L ↔ ∀ j, -1 ≤ x j ∧ x j ≤ (L : ℤ) := by
  simp [supportPeriods, Fintype.mem_piFinset]

theorem card_interiorPeriods (L : ℕ) : (interiorPeriods L).card = L ^ 3 := by
  rw [interiorPeriods, Fintype.card_piFinset_const, Int.card_Icc]
  norm_num

theorem card_supportPeriods (L : ℕ) : (supportPeriods L).card = (L + 2) ^ 3 := by
  rw [supportPeriods, Fintype.card_piFinset_const, Int.card_Icc]
  norm_num [show (L : ℤ) + 1 + 1 = (L + 2 : ℕ) from by omega]
  omega

theorem card_supportPeriods_le (L : ℕ) (hL : 2 ≤ L) :
    (supportPeriods L).card ≤ 8 * L ^ 3 := by
  rw [card_supportPeriods]
  calc
    (L + 2) ^ 3 ≤ (2 * L) ^ 3 := Nat.pow_le_pow_left (by omega : L + 2 ≤ 2 * L) 3
    _ = 8 * L ^ 3 := by ring

theorem incidentOffset_bounds (a : Direction) (j : Fin 4) (k : Direction) :
    0 ≤ incidentOffset a j k ∧ incidentOffset a j k ≤ 1 := by
  have h : ∀ a : Direction, ∀ j : Fin 4, ∀ k : Direction,
      0 ≤ incidentOffset a j k ∧ incidentOffset a j k ≤ 1 := by decide
  exact h a j k

theorem cube_contains_interior_incident (L : ℕ) (r : Edge20) (n : Site)
    (hn : n ∈ interiorPeriods L) (j : Fin 4) :
    incidentCell (Bloch.edgeCellEquiv.symm (r, n)) j ∈ cube L := by
  apply (mem_cube L _).mpr
  intro k
  have hk := (mem_interiorPeriods L n).mp hn k
  have ho := incidentOffset_bounds r.1 j k
  have hr := ZMod.val_lt (r.2 k)
  change -2 ≤ n k * 20 + ((r.2 k).val : ℤ) - incidentOffset r.1 j k ∧
    n k * 20 + ((r.2 k).val : ℤ) - incidentOffset r.1 j k ≤ 20 * (L : ℤ) + 2
  omega

/-- Every edge component in each of the designated `L³` cells has full
unit defect weight, including edge anchors on the cell boundaries. -/
theorem cube_weight_interior (L : ℕ) (r : Edge20) (n : Site)
    (hn : n ∈ interiorPeriods L) :
    weight (cube L) (Bloch.edgeCellEquiv.symm (r, n)) = 1 := by
  have hcell := cube_contains_interior_incident L r n hn
  have hc : ∀ j, indicator (cube L) (incidentCell (Bloch.edgeCellEquiv.symm (r, n)) j) = 1 := by
    intro j
    exact ite_eq_left (hcell j)
  simp only [weight, edgeAverage, hc]
  norm_num

theorem cube_positive_period_mem (L : ℕ) (r : Edge20) (n : Site)
    (hw : 0 < weight (cube L) (Bloch.edgeCellEquiv.symm (r, n))) :
    n ∈ supportPeriods L := by
  obtain ⟨j, hj⟩ := (weight_positive_iff _ _).mp hw
  apply (mem_supportPeriods L n).mpr
  intro k
  have hk := (mem_cube L _).mp hj k
  have ho := incidentOffset_bounds r.1 j k
  have hr := ZMod.val_lt (r.2 k)
  change -2 ≤ n k * 20 + ((r.2 k).val : ℤ) - incidentOffset r.1 j k ∧
    n k * 20 + ((r.2 k).val : ℤ) - incidentOffset r.1 j k ≤ 20 * (L : ℤ) + 2 at hk
  omega

theorem cube_weight_zero_outside (L : ℕ) (r : Edge20) (n : Site)
    (hn : n ∉ supportPeriods L) :
    weight (cube L) (Bloch.edgeCellEquiv.symm (r, n)) = 0 := by
  have hh := (weight_bounds (cube L) (Bloch.edgeCellEquiv.symm (r, n))).1
  have hz : ¬ 0 < weight (cube L) (Bloch.edgeCellEquiv.symm (r, n)) :=
    fun h => hn (cube_positive_period_mem L r n h)
  linarith

theorem interiorPeriods_subset_supportPeriods (L : ℕ) :
    interiorPeriods L ⊆ supportPeriods L := by
  intro n hn
  apply (mem_supportPeriods L n).mpr
  intro j
  have hh := (mem_interiorPeriods L n).mp hn j
  omega

noncomputable def periodVector (n : Site) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j => (n j : ℝ)

theorem supportPeriods_norm_le (L : ℕ) (hL : 1 ≤ L) (n : Site)
    (hn : n ∈ supportPeriods L) : ‖periodVector n‖ ≤ 4 * (L : ℝ) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcoord : ∀ j, |(n j : ℝ)| ≤ L := by
    intro j
    have hj := (mem_supportPeriods L n).mp hn j
    have hj' : -(L : ℤ) ≤ n j ∧ n j ≤ L := by omega
    exact abs_le.mpr (by exact_mod_cast hj')
  have hs : ‖periodVector n‖ ^ 2 ≤ 3 * (L : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin 3, (L : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        change (n j : ℝ) ^ 2 ≤ (L : ℝ) ^ 2
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (n j : ℝ)) (hcoord j) 2
      _ = _ := by simp
  nlinarith [norm_nonneg (periodVector n)]

theorem cube_phase_bound (L : ℕ) (hL : 1 ≤ L) (n : Site)
    (hn : n ∈ supportPeriods L) (q : EuclideanSpace ℝ (Fin 3)) :
    |-(inner ℝ q (periodVector n))| ≤ 4 * (L : ℝ) * ‖q‖ := by
  rw [abs_neg]
  calc
    _ ≤ ‖q‖ * ‖periodVector n‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖q‖ * (4 * L) := mul_le_mul_of_nonneg_left (supportPeriods_norm_le L hL n hn)
      (norm_nonneg q)
    _ = _ := by ring

def cellWeight (L : ℕ) (n : Site) (r : Edge20) : ℚ :=
  weight (cube L) (Bloch.edgeCellEquiv.symm (r, n))

noncomputable def cellSource (L : ℕ) (φ : EuclideanSpace ℂ Edge20) (n : Site) :
    EuclideanSpace ℂ Edge20 := WithLp.toLp 2 fun r => (cellWeight L n r : ℂ) * φ r

noncomputable def cellMass (L : ℕ) (φ : EuclideanSpace ℂ Edge20) (n : Site) : ℝ :=
  ∑ r, (cellWeight L n r : ℝ) * ‖φ r‖ ^ 2

theorem cellWeight_bounds (L : ℕ) (n : Site) (r : Edge20) :
    0 ≤ (cellWeight L n r : ℝ) ∧ (cellWeight L n r : ℝ) ≤ 1 := by
  exact_mod_cast weight_bounds (cube L) (Bloch.edgeCellEquiv.symm (r, n))

theorem cellMass_nonneg (L : ℕ) (φ : EuclideanSpace ℂ Edge20) (n : Site) :
    0 ≤ cellMass L φ n := by
  apply Finset.sum_nonneg
  intro r _
  exact mul_nonneg (cellWeight_bounds L n r).1 (sq_nonneg _)

theorem cellMass_le_one (L : ℕ) (φ : EuclideanSpace ℂ Edge20) (hφ : ‖φ‖ = 1) (n : Site) :
    cellMass L φ n ≤ 1 := by
  calc
    _ ≤ ∑ r, ‖φ r‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_of_le_one_left (sq_nonneg _) (cellWeight_bounds L n r).2
    _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, hφ]; norm_num

theorem cellSource_norm_le_one (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ‖φ‖ = 1) (n : Site) : ‖cellSource L φ n‖ ≤ 1 := by
  have hs : ‖cellSource L φ n‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ r, ‖φ r‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro r _
        change ‖(cellWeight L n r : ℂ) * φ r‖ ^ 2 ≤ ‖φ r‖ ^ 2
        rw [norm_mul, mul_pow]
        have hW := cellWeight_bounds L n r
        have hnorm : ‖(cellWeight L n r : ℂ)‖ ≤ 1 := by
          rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW.1]
          exact hW.2
        have hsq : ‖(cellWeight L n r : ℂ)‖ ^ 2 ≤ 1 := by
          nlinarith [norm_nonneg (cellWeight L n r : ℂ)]
        exact mul_le_of_le_one_left (sq_nonneg _) hsq
      _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, hφ]; norm_num
  nlinarith [norm_nonneg (cellSource L φ n)]

theorem cellSource_overlap (L : ℕ) (φ : EuclideanSpace ℂ Edge20) (n : Site) :
    inner ℂ φ (cellSource L φ n) = (cellMass L φ n : ℂ) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, cellMass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  change ((cellWeight L n r : ℂ) * φ r) * star (φ r) =
    (((cellWeight L n r : ℝ) * ‖φ r‖ ^ 2 : ℝ) : ℂ)
  rw [mul_assoc, Complex.star_def, Complex.mul_conj', Complex.ofReal_mul,
    Complex.ofReal_ratCast, Complex.ofReal_pow]

theorem cellMass_interior (L : ℕ) (φ : EuclideanSpace ℂ Edge20) (hφ : ‖φ‖ = 1)
    (n : Site) (hn : n ∈ interiorPeriods L) : cellMass L φ n = 1 := by
  have hW : ∀ r, cellWeight L n r = 1 := fun r => cube_weight_interior L r n hn
  simp only [cellMass, hW, Rat.cast_one, one_mul]
  rw [← EuclideanSpace.norm_sq_eq, hφ]
  norm_num

noncomputable def cubeMass (L : ℕ) (φ : EuclideanSpace ℂ Edge20) : ℝ :=
  ∑ n ∈ supportPeriods L, cellMass L φ n

theorem cubeMass_bounds (L : ℕ) (hL : 2 ≤ L) (φ : EuclideanSpace ℂ Edge20) (hφ : ‖φ‖ = 1) :
    (L : ℝ) ^ 3 ≤ cubeMass L φ ∧ cubeMass L φ ≤ 8 * (L : ℝ) ^ 3 := by
  constructor
  · have hi : ∑ n ∈ interiorPeriods L, cellMass L φ n = (L : ℝ) ^ 3 := by
      calc
        _ = ∑ _n ∈ interiorPeriods L, (1 : ℝ) := Finset.sum_congr rfl
          (fun n hn => cellMass_interior L φ hφ n hn)
        _ = _ := by simp [card_interiorPeriods]
    rw [← hi]
    apply Finset.sum_le_sum_of_subset_of_nonneg (interiorPeriods_subset_supportPeriods L)
    intro n _ _
    exact cellMass_nonneg L φ n
  · calc
      _ ≤ ∑ _n ∈ supportPeriods L, (1 : ℝ) := Finset.sum_le_sum
        (fun n _ => cellMass_le_one L φ hφ n)
      _ = (supportPeriods L).card := by simp
      _ ≤ 8 * (L : ℝ) ^ 3 := by exact_mod_cast card_supportPeriods_le L hL

noncomputable def coherentAmplitude (L : ℕ) (φ φ₀ : EuclideanSpace ℂ Edge20)
    (q : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  inner ℂ φ (∑ n : ↥(supportPeriods L),
    Complex.exp (Complex.I * -(inner ℝ q (periodVector n))) • cellSource L φ₀ n)

set_option maxHeartbeats 800000 in
/-- The manuscript coherence bound now holds for the actual finite
scalar-cell cube weights and their concrete conventional-cell phases. -/
theorem coherentAmplitude_error (L : ℕ) (hL : 2 ≤ L)
    (φ φ₀ : EuclideanSpace ℂ Edge20) (hφ : ‖φ₀‖ = 1)
    (q : EuclideanSpace ℝ (Fin 3)) (C : ℝ) (hC : 0 ≤ C)
    (hvariation : ‖φ - φ₀‖ ≤ C * ‖q‖) :
    ‖coherentAmplitude L φ φ₀ q - (cubeMass L φ₀ : ℂ)‖ ≤
      4 * L * ‖q‖ * cubeMass L φ₀ + 8 * C * (L : ℝ) ^ 3 * ‖q‖ := by
  have hc : (Fintype.card ↥(supportPeriods L) : ℝ) ≤ 8 * (L : ℝ) ^ 3 := by
    simpa using (show ((supportPeriods L).card : ℝ) ≤ 8 * (L : ℝ) ^ 3 by
      exact_mod_cast card_supportPeriods_le L hL)
  have h := cube_fourier_overlap_error φ φ₀
    (fun n : ↥(supportPeriods L) => cellSource L φ₀ n)
    (fun n : ↥(supportPeriods L) => cellMass L φ₀ n)
    (fun n : ↥(supportPeriods L) => -(inner ℝ q (periodVector n)))
    (norm_nonneg q) hC (fun n => cellSource_norm_le_one L φ₀ hφ n)
    (fun n => cellMass_nonneg L φ₀ n) (fun n => cellSource_overlap L φ₀ n)
    (fun n => cube_phase_bound L (by omega) n n.property q) hc hvariation
  simpa only [coherentAmplitude, cubeMass, Finset.sum_coe_sort, Complex.ofReal_neg] using h

theorem sum_cube_edgeCoordinates {A : Type*} [AddCommMonoid A] (L : ℕ) (F : Edge → A)
    (hF : ∀ e, weight (cube L) e = 0 → F e = 0) :
    (∑ i, F (edgeEmbedding (cube L) i)) =
      ∑ n ∈ supportPeriods L, ∑ r : Edge20, F (Bloch.edgeCellEquiv.symm (r, n)) := by
  classical
  let e : Fin (edges (cube L)).card → Edge20 × Site :=
    fun i => Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)
  have hinj : Function.Injective e := Bloch.edgeCellEquiv.injective.comp
    (edgeEmbedding (cube L)).injective
  have hm : ∀ i, (e i).2 ∈ supportPeriods L := by
    intro i
    have hp : 0 < weight (cube L) (edgeEmbedding (cube L) i) := by
      apply (mem_edges_iff_positive _ _).mp
      change edgeEmbedding (cube L) i ∈ (edges (cube L) : Set Edge)
      rw [← range_edgeEmbedding]
      exact ⟨i, rfl⟩
    apply cube_positive_period_mem L (e i).1 (e i).2
    simpa only [e, Prod.mk.eta, Equiv.symm_apply_apply] using hp
  have hsum : (∑ i, F (edgeEmbedding (cube L) i)) =
      ∑ rn ∈ (Finset.univ : Finset Edge20) ×ˢ supportPeriods L,
        F (Bloch.edgeCellEquiv.symm rn) := by
    apply Finset.sum_of_injOn e hinj.injOn
    · intro i _
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hm i⟩
    · intro rn _ hnot
      apply hF
      have hnonpos : ¬ 0 < weight (cube L) (Bloch.edgeCellEquiv.symm rn) := by
        intro hp
        have he : Bloch.edgeCellEquiv.symm rn ∈ (edges (cube L) : Set Edge) :=
          (mem_edges_iff_positive _ _).mpr hp
        rw [← range_edgeEmbedding] at he
        obtain ⟨i, hi⟩ := he
        apply hnot
        refine ⟨i, Finset.mem_univ _, ?_⟩
        dsimp [e]
        rw [hi, Equiv.apply_symm_apply]
      linarith [(weight_bounds (cube L) (Bloch.edgeCellEquiv.symm rn)).1]
    · intro i _
      simp only [e, Equiv.symm_apply_apply]
  rw [hsum, Finset.sum_product, Finset.sum_comm]

noncomputable def coherentCoordinates (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (phase : Site → ℂ) : EuclideanSpace ℂ (Fin (edges (cube L)).card) :=
  WithLp.toLp 2 fun i =>
    (Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) *
      phase (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).2 *
      φ (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).1

/-- The source-coordinate norm is exactly the cube mass used in the
Rayleigh estimate, for every unit-modulus edge Bloch phase. -/
theorem coherentCoordinates_norm_sq (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (phase : Site → ℂ) (hphase : ∀ n, ‖phase n‖ = 1) :
    ‖coherentCoordinates L φ phase‖ ^ 2 = cubeMass L φ := by
  rw [EuclideanSpace.norm_sq_eq]
  have hs : (∑ i, ‖coherentCoordinates L φ phase i‖ ^ 2) =
      ∑ i, (weight (cube L) (edgeEmbedding (cube L) i) : ℝ) *
        ‖φ (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).1‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    change ‖(Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) *
      phase (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).2 *
      φ (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).1‖ ^ 2 = _
    rw [norm_mul, norm_mul, hphase, mul_one, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
    · rfl
    · exact_mod_cast (weight_bounds (cube L) (edgeEmbedding (cube L) i)).1
  rw [hs, sum_cube_edgeCoordinates L
    (fun e => (weight (cube L) e : ℝ) * ‖φ (Bloch.edgeCellEquiv e).1‖ ^ 2)
    (fun e he => by simp [he])]
  simp only [cubeMass, cellMass, cellWeight, Equiv.apply_symm_apply]

theorem injection_coherentCoordinates (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (phase : Site → ℂ) (e : Edge) :
    injection (cube L) (coherentCoordinates L φ phase) e =
      (weight (cube L) e : ℂ) * phase (Bloch.edgeCellEquiv e).2 * φ (Bloch.edgeCellEquiv e).1 := by
  by_cases he : e ∈ Set.range (edgeEmbedding (cube L))
  · obtain ⟨i, rfl⟩ := he
    rw [injection, defectInjection_apply_at]
    change (Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) *
      ((Real.sqrt (coordinateWeight (cube L) i : ℝ) : ℂ) *
        phase (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).2 *
        φ (Bloch.edgeCellEquiv (edgeEmbedding (cube L) i)).1) = _
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt]
    · simp only [coordinateWeight, Complex.ofReal_ratCast]
    · exact_mod_cast (weight_bounds (cube L) (edgeEmbedding (cube L) i)).1
  · have hw : weight (cube L) e = 0 := by
      have hn : ¬ 0 < weight (cube L) e := by
        intro hp
        apply he
        rw [range_edgeEmbedding]
        exact (mem_edges_iff_positive _ _).mpr hp
      linarith [(weight_bounds (cube L) e).1]
    rw [injection, defectInjection_apply_of_notMem _ _ _ _ he, hw]
    simp

end Maxwell.Defect.ScalarDefect
