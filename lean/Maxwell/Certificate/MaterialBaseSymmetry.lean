import Maxwell.Certificate.Material

namespace Maxwell.Certificate.Material
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem base_inversion : ∀ x y z,
    baseValue ![invertCell x, invertCell y, invertCell z] = baseValue ![x,y,z] := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide +kernel

theorem base_fcc_periodicity : ∀ x y z,
    baseValue ![x, halfShift y, halfShift z] = baseValue ![x,y,z] ∧
    baseValue ![halfShift x, y, halfShift z] = baseValue ![x,y,z] ∧
    baseValue ![halfShift x, halfShift y, z] = baseValue ![x,y,z] := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide +kernel

end Maxwell.Certificate.Material
