import Maxwell.Certificate.PointWitness.NormDefs
namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee

def blockDotI (v w : Electric → ℤ) (j : Fin 3) (x : Fin 20) : ℤ :=
  ∑ y : Fin 10, ∑ z : Fin 10, v (j,(x,y,z)) * w (j,(x,y,z))
def dotI (v w : Electric → ℤ) : ℤ := ∑ j, ∑ x, blockDotI v w j x

theorem dotI_eq_sum (v w : Electric → ℤ) : dotI v w = ∑ e, v e * w e := by
  simp only [dotI, blockDotI, Fintype.sum_prod_type]

end Maxwell.Certificate.PointWitness
