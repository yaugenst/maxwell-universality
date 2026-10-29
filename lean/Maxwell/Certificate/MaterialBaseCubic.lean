import Maxwell.Certificate.MaterialBaseSymmetry

namespace Maxwell.Certificate.Material
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def quarterShift (x : Fin 20) : Fin 20 := ⟨(x.val+5)%20, Nat.mod_lt _ (by decide)⟩

theorem base_swap01 : ∀ x y z, baseValue ![y,x,z] = baseValue ![x,y,z] := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide +kernel

theorem base_swap12 : ∀ x y z, baseValue ![x,z,y] = baseValue ![x,y,z] := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide +kernel

/-- Reflection of the scalar cells includes the actual diamond glide.
The reflected node coordinate is `-x`; cell centers require `-x-1`. -/
theorem base_glide0 : ∀ x y z,
    baseValue ![invertCell x,quarterShift y,quarterShift z] = baseValue ![x,y,z] := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide +kernel

end Maxwell.Certificate.Material
