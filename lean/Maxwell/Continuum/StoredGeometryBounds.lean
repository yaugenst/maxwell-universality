import Maxwell.Continuum.StoredGeometryMediator

/-! Uniform widths for computed physical centers. Loop widths do not grow
with the number of records: every center is recomputed from the fixed
physical parameters and one or two stored coordinate words. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1800000

theorem arrayValue_bits {n : ℕ} (values : Vector ℕ n) (W : ℕ)
    (hfit : ∀i,(values.get i).bits.length≤W) (i : ℕ) : (arrayValue values i).bits.length≤W := by
  unfold arrayValue
  split
  · exact hfit _
  · simp

theorem terminalCoordinate_bits {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (W : ℕ)
    (hfit : ∀i,(values.get i).bits.length≤W) (hs : (constants 982).bits.length≤W)
    (hscale : ∀j:Fin 3,(constants (983+j.val)).bits.length≤W) (cursor : ℕ) (j : Fin 3) :
    (terminalCoordinate values constants cursor j).bits.length≤2*W+2 := by
  have hx := arrayValue_bits values W hfit (cursor+j.val)
  have hsum := bits_add_le (arrayValue values (cursor+j.val)) (arrayValue values (cursor+j.val))
  have hmul := bits_mul_le (constants (983+j.val))
    (arrayValue values (cursor+j.val)+arrayValue values (cursor+j.val))
  have hout := bits_add_le (constants 982)
    (constants (983+j.val)*(arrayValue values (cursor+j.val)+arrayValue values (cursor+j.val)))
  have he : 2*arrayValue values (cursor+j.val)=arrayValue values (cursor+j.val)+arrayValue values (cursor+j.val) := by omega
  simp only [terminalCoordinate,he]
  have := hscale j
  omega

theorem mediatorCoordinate_bits {n : ℕ} (values : Vector ℕ n) (constants : ℕ→ℕ) (W : ℕ)
    (hfit : ∀i,(values.get i).bits.length≤W) (hs : (constants 982).bits.length≤W)
    (hscale : ∀j:Fin 3,(constants (983+j.val)).bits.length≤W) (cursor : ℕ) (j : Fin 3) :
    (mediatorCoordinate values constants cursor j).bits.length≤2*W+2 := by
  have hx := arrayValue_bits values W hfit (cursor+j.val)
  have hy := arrayValue_bits values W hfit (cursor+3+j.val)
  have hsum := bits_add_le (arrayValue values (cursor+j.val)) (arrayValue values (cursor+3+j.val))
  have hmul := bits_mul_le (constants (983+j.val))
    (arrayValue values (cursor+j.val)+arrayValue values (cursor+3+j.val))
  have hout := bits_add_le (constants 982)
    (constants (983+j.val)*(arrayValue values (cursor+j.val)+arrayValue values (cursor+3+j.val)))
  unfold mediatorCoordinate
  have := hscale j
  omega

#print axioms terminalCoordinate_bits
#print axioms mediatorCoordinate_bits
end Maxwell.Continuum.GeometryOutput
