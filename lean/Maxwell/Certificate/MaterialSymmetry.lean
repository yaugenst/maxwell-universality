import Maxwell.Certificate.MaterialBaseSymmetry

namespace Maxwell.Certificate.Material
theorem cellValue_inversion (x y z : Fin 20) :
    cellValue ![invertCell x, invertCell y, invertCell z] = cellValue ![x,y,z] := by
  simp [cellValue, base_inversion, numerator_inversion]

theorem cellValue_fcc_periodicity (x y z : Fin 20) :
    cellValue ![x, halfShift y, halfShift z] = cellValue ![x,y,z] ∧
    cellValue ![halfShift x, y, halfShift z] = cellValue ![x,y,z] ∧
    cellValue ![halfShift x, halfShift y, z] = cellValue ![x,y,z] := by
  have hb := base_fcc_periodicity x y z
  have hn := numerator_fcc_periodicity x y z
  simp [cellValue, hb.1, hb.2.1, hb.2.2, hn.1, hn.2.1, hn.2.2]

end Maxwell.Certificate.Material
