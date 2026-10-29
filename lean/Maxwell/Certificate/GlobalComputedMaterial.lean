import Maxwell.Certificate.MaterialWitness.BaseChecked
import Maxwell.Certificate.DyadicKernelActionSound
import Maxwell.Spectral.GlobalComparison

namespace Maxwell.Certificate.GlobalComputedMaterial
open DyadicKernel Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section

/-- The integer shift is measured in units of 1/256: 0 for the clean
crystal, 157 for the global comparator, and 448 for local isolation. -/
def material (numerator : ℤ) : PeriodicYee.Cell20 → ℝ :=
  fun r => Concrete.baseMaterial r + (numerator:ℝ)/256

def denominator (numerator : ℤ) (e : Electric) : Rectangle :=
  ⟨(64*MaterialWitness.baseDen e+numerator)*2^44,0,0⟩

def field (numerator : ℤ) : Action.VectorField :=
  Action.VectorField.build fun r => Triple.ofFn fun j => denominator numerator (j,r)

theorem denominator_contains (numerator : ℤ) (e : Electric) :
    (denominator numerator e).toDyadic.Contains 52 (edgeAverage (material numerator) e:ℂ) := by
  have hb : (MaterialWitness.baseDen e:ℝ)/4 = edgeAverage Concrete.baseMaterial e := by
    rw [← MaterialWitness.baseDen_binding]
    exact PointInertia.baseEdgeInteger_cast e
  have he : edgeAverage (material numerator) e =
      (MaterialWitness.baseDen e:ℝ)/4+(numerator:ℝ)/256 := by
    rw [hb]
    simp only [material,edgeAverage]
    ring
  rw [he]
  constructor <;> norm_num [denominator,Rectangle.toDyadic,DyadicRectangle.Contains]
  ring_nf

theorem denominator_positive (numerator : ℤ) (hn : 0 ≤ numerator) (e : Electric) :
    0 < (denominator numerator e).re-((denominator numerator e).radius:ℤ) := by
  have hb := (GlobalComparison.base_edge_bounds e).1
  rw [← PointInertia.baseEdgeInteger_cast,MaterialWitness.baseDen_binding] at hb
  have hbase : (4:ℤ) ≤ MaterialWitness.baseDen e := by
    have hh : (4:ℝ) ≤ (MaterialWitness.baseDen e:ℝ) := by linarith
    exact_mod_cast hh
  simp only [denominator,Nat.cast_zero,sub_zero]
  positivity

theorem field_contains (numerator : ℤ) (r : Action.Cell) (j : Fin 3) :
    ((field numerator).get r).toVector j |>.Contains 52 (edgeAverage (material numerator) (j,r):ℂ) := by
  rw [field,Action.VectorField.get_build,← Triple.toDyadic_get,Triple.get_ofFn]
  exact denominator_contains numerator (j,r)

private theorem allFin_true {n : ℕ} {p : Fin n → Bool} (h : ∀ i, p i=true) :
    Action.allFin n p=true := List.all_eq_true.mpr (fun i _ => h i)

theorem materialValid (numerator : ℤ) (hn : 0 ≤ numerator) :
    Action.materialValid (field numerator)=true := by
  apply allFin_true
  intro x
  apply allFin_true
  intro y
  apply allFin_true
  intro z
  apply allFin_true
  intro j
  apply decide_eq_true
  simp only [field,Action.VectorField.get_build,Triple.get_ofFn]
  exact denominator_positive numerator hn (j,x,y,z)

theorem material_base : material 0 = Concrete.baseMaterial := by
  ext r
  simp [material]

theorem material_comparator : material 157 = GlobalComparison.comparatorMaterial := by
  ext r
  norm_num [material,GlobalComparison.comparatorMaterial]

end
end Maxwell.Certificate.GlobalComputedMaterial
