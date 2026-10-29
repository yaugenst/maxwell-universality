import Maxwell.Certificate.PointWitness.ConventionalPhysical
import Maxwell.Spectral.FourLExclusion
import Maxwell.Spectral.FoldingInverse

/-! Actual conventional-torus exclusion from the same four primitive local
certificates and the finite global cover. Reciprocal coordinates prove that
no nonzero displacement in the conventional torus reaches the selected edge. -/
namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open FourierBinding FourLGeometry GlobalCover ReciprocalCover
open Maxwell.Green (torusCube)
noncomputable section
set_option maxHeartbeats 800000

def edgeCartesian (q : Momentum) : Momentum := center 0+(fun j => q j/(2*Real.pi))

def sectorOffset (b : Folding.Coset) : Translation := ![0,b.1.val,b.2.val]

def sectorCartesian (q : Momentum) (b : Folding.Coset) : Momentum :=
  edgeCartesian q+(fun j => (sectorOffset b j : ℝ))

theorem sectorCartesian_binding (q : Momentum) (b : Folding.Coset) :
    boundaryMomentum (sectorCartesian q b) = Folding.sectorMomentum (boundaryMomentum (edgeCartesian q)) b := by
  ext j
  fin_cases j <;> simp [sectorCartesian,sectorOffset,boundaryMomentum,Folding.sectorMomentum,
    Folding.sectorTranslation,timeReversalMomentum] <;> ring

theorem conventionalCartesian_binding (q : Momentum) :
    Folding.conventionalMomentum (boundaryMomentum (edgeCartesian q)) = conventionalPointMomentum+q := by
  have hpi : (2*Real.pi : ℝ) ≠ 0 := by positivity
  ext j
  fin_cases j <;> simp [Folding.conventionalMomentum,boundaryMomentum,edgeCartesian,
    center,point,cartesianMomentum,conventionalPointMomentum,pointPrimitiveMomentum,timeReversalMomentum] <;>
      field_simp <;> ring

theorem sectorCartesian_not_selected (q : Momentum)
    (hq : q ∈ torusCube (-Real.pi) (2*Real.pi)) (hne : q ≠ 0) (b : Folding.Coset) :
    ¬ SelectedClass (sectorCartesian q b) := by
  rintro ⟨n,hn⟩
  let m : Translation := ![n 0,2*n 1-n 0-b.1.val,2*n 2-n 0-b.2.val]
  have he (j : Fin 3) : q j/(2*Real.pi) = (m j : ℝ) := by
    have hj := congrFun hn j
    fin_cases j <;>
      simp [sectorCartesian,edgeCartesian,sectorOffset,reciprocalShift,m] at hj ⊢ <;>
      linarith
  apply hne
  ext j
  have hj := hq j
  have heq : q j=(m j : ℝ)*(2*Real.pi) := (div_eq_iff (by positivity)).mp (he j)
  have hp := Real.pi_pos
  have hlo : (-1:ℝ) < (m j : ℝ) := by nlinarith [hj.1]
  have hhi : (m j : ℝ) < (1:ℝ) := by nlinarith [hj.2]
  have hlo' : (-1:ℤ) < m j := by exact_mod_cast hlo
  have hhi' : m j < (1:ℤ) := by exact_mod_cast hhi
  have hm : m j=0 := by omega
  simpa only [hm,Int.cast_zero,zero_mul,Pi.zero_apply] using heq

theorem pointRealEdgeExclusion_of_local_and_cover
    (hn : NegativeCenters) (hp : ComparatorCenters)
    (hcenter : ∀ a : Fin 4, a ≠ 0 →
      (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
        (PrimitiveYee.fiber Concrete.material (boundaryMomentum (center a)))-
          (pointEnergy:ℂ) • 1).IsInvertible)
    (hpuncture : ∀ (a : Fin 4) (q : Momentum), 0 < YeeTaylor.radius q →
      YeeTaylor.radius q ≤ 1/20 → (YeeTaylorRemainder.centeredOperator (point a) q-
        (pointEnergy:ℂ) • 1).IsInvertible) : PointRealEdgeExclusion := by
  intro q hq hne
  have hsector (b : Folding.Coset) :
      (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
        (PrimitiveYee.fiber Concrete.material
          (Folding.sectorMomentum (boundaryMomentum (edgeCartesian q)) b))-
            (pointEnergy:ℂ) • 1).IsInvertible := by
    rw [← sectorCartesian_binding]
    exact primitive_edge_invertible hn hp hcenter hpuncture _
      (sectorCartesian_not_selected q hq hne b)
  have hf := FoldingInverse.conventional_invertible_of_primitive
    (boundaryMomentum (edgeCartesian q)) pointEnergy hsector
  rw [conventionalCartesian_binding] at hf
  have hr : ConventionalAnalytic.realMomentum conventionalPointMomentum+
      ConventionalAnalytic.realMomentum q =
      ConventionalAnalytic.realMomentum (conventionalPointMomentum+q) := by
    ext j
    simp [ConventionalAnalytic.realMomentum]
  simpa only [conventionalPointOperator,hr,ConventionalAnalytic.operator_real] using hf

end
end Maxwell.Certificate.PointWitness
