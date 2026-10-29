import Maxwell.Spectral.Lattice
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.GCongr

namespace Maxwell.Green

open Maxwell.Spectral

noncomputable def sitePoint (x : Lattice.Site) : PiLp 1 (fun _ : Fin 3 => ℝ) :=
  WithLp.toLp 1 fun i => (x i : ℝ)

noncomputable def siteDistance (x y : Lattice.Site) : ℝ :=
  ∑ i, |(x i : ℝ) - (y i : ℝ)|

theorem sitePoint_distance (x y : Lattice.Site) :
    dist (sitePoint x) (sitePoint y) = siteDistance x y := by
  rw [PiLp.dist_eq_of_L1]
  simp [sitePoint, siteDistance, Real.dist_eq]

/-- Distance from the complete source union, clipped before exponentiation.
The edge orientation does not affect physical lattice separation. -/
noncomputable def clippedDistance (source : Set Lattice.Edge) (cap : ℝ)
    (e : Lattice.Edge) : ℝ :=
  min cap (Metric.infDist (sitePoint e.2) ((fun f : Lattice.Edge => sitePoint f.2) '' source))

theorem clippedDistance_bounds (source : Set Lattice.Edge) (cap : ℝ)
    (hcap : 0 ≤ cap) (e : Lattice.Edge) :
    0 ≤ clippedDistance source cap e ∧ clippedDistance source cap e ≤ cap := by
  exact ⟨le_min hcap Metric.infDist_nonneg, min_le_left _ _⟩

theorem clippedDistance_source_zero (source : Set Lattice.Edge) (cap : ℝ)
    (hcap : 0 ≤ cap) (e : Lattice.Edge) (he : e ∈ source) :
    clippedDistance source cap e = 0 := by
  unfold clippedDistance
  have hm : sitePoint e.2 ∈ (fun f : Lattice.Edge => sitePoint f.2) '' source :=
    Set.mem_image_of_mem (fun f : Lattice.Edge => sitePoint f.2) he
  rw [Metric.infDist_zero_of_mem hm, min_eq_right hcap]

/-- Clipping preserves the unit Lipschitz constant of distance to a set. -/
theorem clippedDistance_lipschitz (source : Set Lattice.Edge) (cap : ℝ)
    (e f : Lattice.Edge) :
    |clippedDistance source cap e - clippedDistance source cap f| ≤
      siteDistance e.2 f.2 := by
  have h := Metric.lipschitz_infDist_pt (s :=
    (fun g : Lattice.Edge => sitePoint g.2) '' source)
  have hd := h.dist_le_mul (sitePoint e.2) (sitePoint f.2)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, sitePoint_distance] at hd
  have hm := abs_min_sub_min_le_max cap
    (Metric.infDist (sitePoint e.2) ((fun g : Lattice.Edge => sitePoint g.2) '' source)) cap
    (Metric.infDist (sitePoint f.2) ((fun g : Lattice.Edge => sitePoint g.2) '' source))
  simp only [sub_self, abs_zero] at hm
  exact hm.trans (max_le (by unfold siteDistance; positivity) hd)

/-- A source-to-boundary separation holds for the entire union with the
same potential and without adding the number of source coordinates. -/
theorem clippedDistance_target_lower (source : Set Lattice.Edge) (hs : source.Nonempty)
    (cap d : ℝ) (hdcap : d ≤ cap) (e : Lattice.Edge)
    (hsep : ∀ f ∈ source, d ≤ siteDistance e.2 f.2) :
    d ≤ clippedDistance source cap e := by
  apply le_min hdcap
  apply (Metric.le_infDist (hs.image _)).mpr
  rintro z ⟨f, hf, rfl⟩
  rw [sitePoint_distance]
  exact hsep f hf

theorem siteDistance_translate (x v : Lattice.Site) :
    siteDistance (x + v) x = ∑ i, |(v i : ℝ)| := by
  simp [siteDistance, Int.cast_add]

theorem unitSite_abs_sum (j : Fin 3) :
    ∑ i, |(Lattice.unitSite j i : ℝ)| = 1 := by
  fin_cases j <;> norm_num [Lattice.unitSite, Fin.sum_univ_succ, Pi.single_apply]

theorem siteDistance_unit_step (x : Lattice.Site) (j : Fin 3) :
    siteDistance (x + Lattice.unitSite j) x = 1 := by
  rw [siteDistance_translate, unitSite_abs_sum]

theorem clippedDistance_fieldPermutation (source : Set Lattice.Edge) (cap : ℝ)
    (p : Equiv.Perm Lattice.Direction) (v : Lattice.Direction → Lattice.Site)
    (r : ℝ) (hv : ∀ j, (∑ i, |(v j i : ℝ)|) ≤ r) (e : Lattice.Edge) :
    |clippedDistance source cap (Lattice.fieldPermutation p v e) -
      clippedDistance source cap e| ≤ r := by
  apply (clippedDistance_lipschitz source cap _ e).trans
  change siteDistance (e.2 + v e.1) e.2 ≤ r
  rw [siteDistance_translate]
  exact hv e.1

/-- Both shifted and unshifted component permutations in the actual Yee curl
satisfy the required potential increment bound. -/
theorem clippedDistance_yee_step (source : Set Lattice.Edge) (cap : ℝ)
    (p : Equiv.Perm Lattice.Direction) (j : Lattice.Direction → Lattice.Direction)
    (e : Lattice.Edge) :
    |clippedDistance source cap
        (Lattice.fieldPermutation p (fun d => Lattice.unitSite (j d)) e) -
      clippedDistance source cap e| ≤ 1 := by
  apply clippedDistance_fieldPermutation
  intro d
  rw [unitSite_abs_sum]

theorem clippedDistance_component_permutation (source : Set Lattice.Edge) (cap : ℝ)
    (p : Equiv.Perm Lattice.Direction) (e : Lattice.Edge) :
    clippedDistance source cap (Lattice.fieldPermutation p (fun _ => 0) e) =
      clippedDistance source cap e := by
  simp [clippedDistance, Lattice.fieldPermutation]

end Maxwell.Green
