import Maxwell.Green.CalibrationLattice
import Maxwell.Green.PlatformCalibration

/-! Explicit finite work domains for axial calibration. Their dimension
is cubic in the propagation degree and the integer separation. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000
variable {n : ℕ}

def edgeRadius (edges : Fin n → Edge) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j : Direction => (edges i).2 j |>.natAbs

theorem edgeRadius_bound (edges : Fin n → Edge) (i : Fin n) (j : Direction) :
    |(edges i).2 j| ≤ (edgeRadius edges : ℤ) := by
  have h1 := Finset.le_sup (f := fun j : Direction => ((edges i).2 j).natAbs) (Finset.mem_univ j)
  have h2 := Finset.le_sup
    (f := fun i => Finset.univ.sup fun j : Direction => ((edges i).2 j).natAbs)
    (Finset.mem_univ i)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h1.trans h2

theorem rationalSource_supported (edges : Fin n → Edge) (a : Fin n → ℚ) :
    Supported (rationalSource edges a) (edgeRadius edges) := by
  intro t ht j
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  exact edgeRadius_bound edges i j

theorem rationalSource_translated_supported (edges : Fin n → Edge) (a : Fin n → ℚ)
    (k : Site) (L : ℕ) (hk : ∀ j, |k j| ≤ (L : ℤ)) :
    Supported (rationalSource (Green.PhysicalCompression.translateEdge k ∘ edges) a)
      (edgeRadius edges + 20*L) := by
  intro t ht j
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  change |(edges i).2 j - 20*k j| ≤ _
  calc
    _ ≤ |(edges i).2 j| + |20*k j| := abs_sub _ _
    _ = |(edges i).2 j| + 20*|k j| := by rw [abs_mul]; norm_num
    _ ≤ (edgeRadius edges : ℤ) + 20*(L : ℤ) := by
      exact add_le_add (edgeRadius_bound edges i j) (mul_le_mul_of_nonneg_left (hk j) (by norm_num))
    _ = _ := by norm_num

theorem axial_coordinates (B : Matrix Direction Direction ℤ) (d : ℕ) (j : Direction) :
    ∀ i, |((d : ℤ) • B.mulVec (unitSite j)) i| ≤
      ((Maxwell.Green.placementBoxFactor B * d : ℕ) : ℤ) := by
  have hz : ∀ i, |((d : ℤ) • unitSite j) i| ≤ (d : ℤ) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [unitSite]
    · simp [unitSite, hij]
  intro i
  simpa only [Matrix.mulVec_smul] using
    Maxwell.Green.placement_uniform_coordinate_bound B ((d : ℤ) • unitSite j) d hz i

/-- The source, final output, and every intermediate stencil value fit in
this explicitly sized box for an axial spacing `d`. -/
def axialWorkRadius (edges : Fin n → Edge) (B : Matrix Direction Direction ℤ)
    (d N : ℕ) : ℕ := edgeRadius edges + 20*(Maxwell.Green.placementBoxFactor B*d) + 4*N + 2

theorem axial_denseInverse_physical (edges : Fin n → Edge) (a : Fin n → ℚ)
    (B : Matrix Direction Direction ℤ) (d : ℕ) (j : Direction)
    (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (N : ℕ) :
    let k := (d : ℤ) • B.mulVec (unitSite j)
    let v := rationalSource (Green.PhysicalCompression.translateEdge k ∘ edges) a
    let Q := cubeEmbedding (axialWorkRadius edges B d N)
    embed (rationalSource Q (denseInverse (stencilMatrix Q m z) s (coefficients Q v) N)) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed v) := by
  dsimp only
  exact denseInverse_physical m K hK hm z s _ _
    (rationalSource_translated_supported edges a _ _ (axial_coordinates B d j)) N

theorem axialWork_dimension (edges : Fin n → Edge) (B : Matrix Direction Direction ℤ)
    (d N : ℕ) :
    (cubeEdges (axialWorkRadius edges B d N)).card =
      3 * (2*(edgeRadius edges + 20*(Maxwell.Green.placementBoxFactor B*d) + 4*N + 2)+1)^3 :=
  cubeEdges_card _

end Maxwell.Defect.FiniteStencil
