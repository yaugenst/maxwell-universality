import Maxwell.Certificate.IntegerAction
namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee

def blockNormI (v : Electric → ℤ) (j : Fin 3) (x : Fin 20) : ℤ :=
  ∑ y : Fin 10, ∑ z : Fin 10, v (j,(x,y,z)) * v (j,(x,y,z))
def squareNormI (v : Electric → ℤ) : ℤ := ∑ j, ∑ x, blockNormI v j x

theorem squareNormI_eq_sum (v : Electric → ℤ) : squareNormI v = ∑ e, v e * v e := by
  simp only [squareNormI, blockNormI, Fintype.sum_prod_type]
end Maxwell.Certificate.PointWitness
