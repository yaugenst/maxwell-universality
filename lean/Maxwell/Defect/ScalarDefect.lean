import Maxwell.Defect.PhysicalCompression
import Maxwell.Spectral.PeriodicYee
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Encodable.Pi
import Maxwell.Defect.Headroom

/-! A finite scalar-cell defect on the actual infinite Yee lattice. Its
support, quarter-averaged weights, and finite coordinate enumeration are
computable from the cell set. -/

namespace Maxwell.Defect.ScalarDefect
open Spectral Spectral.Lattice

def incidentOffset (a : Direction) : Fin 4 → Site :=
  let p := PeriodicYee.transverseDirections a
  ![0, unitSite p.1, unitSite p.2, unitSite p.1 + unitSite p.2]

def incidentCell (e : Edge) (j : Fin 4) : Site := e.2 - incidentOffset e.1 j

def edgeAverage (material : Site → ℚ) (e : Edge) : ℚ :=
  (∑ j : Fin 4, material (incidentCell e j)) / 4

def indicator (D : Finset Site) (c : Site) : ℚ := if c ∈ D then 1 else 0

def weight (D : Finset Site) (e : Edge) : ℚ := edgeAverage (indicator D) e

def hits (D : Finset Site) (e : Edge) : Finset (Fin 4) :=
  Finset.univ.filter fun j => incidentCell e j ∈ D

theorem weight_eq_count (D : Finset Site) (e : Edge) :
    weight D e = (hits D e).card / 4 := by
  have hc : ((hits D e).card : ℚ) =
      ∑ j : Fin 4, if incidentCell e j ∈ D then (1 : ℚ) else 0 := by
    rw [hits, Finset.card_filter]
    simp only [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> norm_num
  rw [hc]
  rfl

theorem weight_bounds (D : Finset Site) (e : Edge) :
    0 ≤ weight D e ∧ weight D e ≤ 1 := by
  have hc : (hits D e).card ≤ 4 := by
    simpa only [hits, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_le (s := (Finset.univ : Finset (Fin 4)))
        (p := fun j => incidentCell e j ∈ D)
  rw [weight_eq_count]
  constructor
  · positivity
  · have hc' : ((hits D e).card : ℚ) ≤ 4 := by exact_mod_cast hc
    linarith

theorem weight_positive_iff (D : Finset Site) (e : Edge) :
    0 < weight D e ↔ ∃ j, incidentCell e j ∈ D := by
  rw [weight_eq_count, div_pos_iff_of_pos_right (by norm_num : (0 : ℚ) < 4)]
  rw [Nat.cast_pos, Finset.card_pos]
  simp [hits, Finset.Nonempty]

theorem weight_quarter_le (D : Finset Site) (e : Edge) (he : 0 < weight D e) :
    1 / 4 ≤ weight D e := by
  have hc : 0 < (hits D e).card := by
    rw [weight_eq_count] at he
    exact_mod_cast ((div_pos_iff_of_pos_right (by norm_num : (0 : ℚ) < 4)).mp he)
  have hc' : (1 : ℚ) ≤ (hits D e).card := by exact_mod_cast hc
  rw [weight_eq_count]
  linarith

def edges (D : Finset Site) : Finset Edge :=
  (Finset.univ : Finset (Direction × Fin 4)).biUnion
    (fun aj => D.image (fun c => (aj.1, c + incidentOffset aj.1 aj.2)))

theorem mem_edges_iff (D : Finset Site) (e : Edge) :
    e ∈ edges D ↔ ∃ j, incidentCell e j ∈ D := by
  constructor
  · intro he
    obtain ⟨⟨a, j⟩, _, hce⟩ := Finset.mem_biUnion.mp he
    rcases Finset.mem_image.mp hce with ⟨c', hc', heq⟩
    subst e
    exact ⟨j, by simpa [incidentCell] using hc'⟩
  · rintro ⟨j, hj⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(e.1, j), Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
    refine ⟨incidentCell e j, hj, ?_⟩
    simp [incidentCell]

theorem mem_edges_iff_positive (D : Finset Site) (e : Edge) :
    e ∈ edges D ↔ 0 < weight D e :=
  (mem_edges_iff D e).trans (weight_positive_iff D e).symm

private abbrev edgeOrder : LinearOrder Edge :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

/-- Deterministic finite enumeration by the standard natural-number
encoding of a direction and three integer coordinates. -/
def edgeEmbedding (D : Finset Site) : Fin (edges D).card ↪ Edge := by
  letI := edgeOrder
  exact ((edges D).orderEmbOfFin rfl).toEmbedding

theorem range_edgeEmbedding (D : Finset Site) :
    Set.range (edgeEmbedding D) = (edges D : Set Edge) := by
  let := edgeOrder
  exact (edges D).range_orderEmbOfFin rfl

def coordinateWeight (D : Finset Site) : Fin (edges D).card → ℚ :=
  fun i => weight D (edgeEmbedding D i)

theorem coordinateWeight_bounds (D : Finset Site) (i : Fin (edges D).card) :
    1 / 4 ≤ coordinateWeight D i ∧ coordinateWeight D i ≤ 1 := by
  have hm : edgeEmbedding D i ∈ edges D := by
    change edgeEmbedding D i ∈ (edges D : Set Edge)
    rw [← range_edgeEmbedding]
    exact ⟨i, rfl⟩
  exact ⟨weight_quarter_le D _ ((mem_edges_iff_positive D _).mp hm), (weight_bounds D _).2⟩

noncomputable def injection (D : Finset Site) :
    EuclideanSpace ℂ (Fin (edges D).card) →L[ℂ] Field :=
  defectInjection (edgeEmbedding D) (coordinateWeight D)

theorem weight_abs_le (D : Finset Site) (e : Edge) : |(weight D e : ℝ)| ≤ 1 := by
  obtain ⟨hl, hu⟩ := weight_bounds D e
  have hl' : (0 : ℝ) ≤ weight D e := by exact_mod_cast hl
  rw [abs_of_nonneg hl']
  exact_mod_cast hu

noncomputable def multiplier (D : Finset Site) : Field →L[ℂ] Field :=
  realSequenceMultiplier (fun e => (weight D e : ℝ)) 1 (by norm_num) (weight_abs_le D)

/-- The finite source map is exactly the physical scalar-cell mass
perturbation, with all incident-edge multiplicities accounted for. -/
theorem injection_adjoint_eq_multiplier (D : Finset Site) :
    (injection D).comp (injection D).adjoint = multiplier D := by
  apply ContinuousLinearMap.ext
  intro x
  ext e
  by_cases he : e ∈ Set.range (edgeEmbedding D)
  · obtain ⟨i, rfl⟩ := he
    change defectInjection (edgeEmbedding D) (coordinateWeight D)
      ((defectInjection (edgeEmbedding D) (coordinateWeight D)).adjoint x)
      (edgeEmbedding D i) = (weight D (edgeEmbedding D i) : ℂ) * x (edgeEmbedding D i)
    rw [defectInjection_apply_at, defectInjection_adjoint_apply, ← mul_assoc,
      ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt]
    · rfl
    · exact_mod_cast (weight_bounds D (edgeEmbedding D i)).1
  · have hw : weight D e = 0 := by
      have hn : ¬ 0 < weight D e := by
        rw [← mem_edges_iff_positive]
        change e ∉ (edges D : Set Edge)
        rw [← range_edgeEmbedding]
        exact he
      linarith [(weight_bounds D e).1]
    change defectInjection (edgeEmbedding D) (coordinateWeight D)
      ((injection D).adjoint x) e = (weight D e : ℂ) * x e
    rw [defectInjection_apply_of_notMem _ _ _ _ he, hw]
    simp

def assembledMaterial (background : Site → ℚ) (D : Finset Site) (v : ℚ) (c : Site) : ℚ :=
  background c + 64 * v * indicator D c

theorem assembledMaterial_edgeAverage (background : Site → ℚ) (D : Finset Site)
    (v : ℚ) (e : Edge) :
    edgeAverage (assembledMaterial background D v) e =
      edgeAverage background e + 64 * v * weight D e := by
  simp only [edgeAverage, assembledMaterial, weight, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

def perturbedCoefficient (D : Finset Site) (m : Edge → ℝ) (v : ℝ) (e : Edge) : ℝ :=
  m e + 64 * v * (weight D e : ℝ)

noncomputable def edgeAverageReal (material : Site → ℝ) (e : Edge) : ℝ :=
  (∑ j : Fin 4, material (incidentCell e j)) / 4

def assembledMaterialReal (background : Site → ℝ) (D : Finset Site) (v : ℝ) (c : Site) : ℝ :=
  background c + 64 * v * (indicator D c : ℝ)

theorem assembledMaterialReal_edgeAverage (background : Site → ℝ) (D : Finset Site)
    (v : ℝ) (e : Edge) :
    edgeAverageReal (assembledMaterialReal background D v) e =
      perturbedCoefficient D (edgeAverageReal background) v e := by
  simp only [edgeAverageReal, assembledMaterialReal, perturbedCoefficient, weight,
    edgeAverage, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The entire two-sided strength interval preserves material headroom on
every actual scalar cell, including cells outside the defect support. -/
theorem assembledMaterialReal_headroom (background : Site → ℝ) (D : Finset Site)
    {h vstar ξlow v : ℝ} (hh : 0 < h) (hvstar : 0 < vstar)
    (hsmall : vstar < (1 / 64 : ℝ) * h / 4)
    (hξ : ξlow ≤ vstar) (hv : |v - vstar| ≤ ξlow / 4)
    (hbackground : ∀ c, 1 ≤ background c ∧ background c ≤ 25 - h) (c : Site) :
    1 ≤ assembledMaterialReal background D v c ∧
      assembledMaterialReal background D v c < 25 - h / 2 := by
  by_cases hc : c ∈ D
  · have hb := (scalar_tuning_headroom (by norm_num : (0 : ℝ) < 1 / 64) hh hvstar
      hsmall hξ hv (hbackground c)).2.2.2
    simpa [assembledMaterialReal, indicator, hc, div_eq_mul_inv, mul_comm] using hb
  · have hb : 1 ≤ background c ∧ background c < 25 - h / 2 :=
      ⟨(hbackground c).1, by linarith [(hbackground c).2]⟩
    simpa [assembledMaterialReal, indicator, hc] using hb

theorem perturbedCoefficient_bound (D : Finset Site) (m : Edge → ℝ) (v K : ℝ)
    (hm : ∀ e, |m e| ≤ K) (e : Edge) :
    |perturbedCoefficient D m v e| ≤ K + 64 * |v| := by
  unfold perturbedCoefficient
  calc
    _ ≤ |m e| + |64 * v * (weight D e : ℝ)| := abs_add_le _ _
    _ = |m e| + 64 * |v| * |(weight D e : ℝ)| := by norm_num [abs_mul]
    _ ≤ K + 64 * |v| * 1 := add_le_add (hm e)
      (mul_le_mul_of_nonneg_left (weight_abs_le D e) (by positivity))
    _ = _ := by ring

noncomputable def perturbedOperator (D : Finset Site) (m : Edge → ℝ) (v K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |m e| ≤ K) : Field →L[ℂ] Field :=
  electricOperator (perturbedCoefficient D m v) (K + 64 * |v|) (by positivity)
    (perturbedCoefficient_bound D m v K hm)

/-- The actual scalar-cell perturbation is precisely the finite-rank
operator used by the Birman--Schwinger correspondence. -/
theorem perturbedOperator_eq (D : Finset Site) (m : Edge → ℝ) (v K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |m e| ≤ K) :
    perturbedOperator D m v K hK hm = electricOperator m K hK hm -
      (v : ℂ) • (injection D).comp (injection D).adjoint := by
  rw [injection_adjoint_eq_multiplier]
  apply ContinuousLinearMap.ext
  intro x
  ext e
  change (yeeCurl.adjoint (yeeCurl x)) e - (1 / 64 : ℂ) *
      ((perturbedCoefficient D m v e : ℂ) * x e) =
    ((yeeCurl.adjoint (yeeCurl x)) e - (1 / 64 : ℂ) * ((m e : ℂ) * x e)) -
      (v : ℂ) * (((weight D e : ℝ) : ℂ) * x e)
  simp only [perturbedCoefficient, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_ratCast]
  ring

end Maxwell.Defect.ScalarDefect
