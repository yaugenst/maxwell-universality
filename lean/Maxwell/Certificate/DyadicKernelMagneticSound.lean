import Maxwell.Certificate.DyadicKernelMagnetic
import Maxwell.Certificate.DyadicKernelRows
import Maxwell.Certificate.DyadicMagnetic

namespace Maxwell.Certificate.DyadicKernel

def Triple.toVector (a : Triple) : Fin 3 → DyadicRectangle :=
  ![a.x.toDyadic,a.y.toDyadic,a.z.toDyadic]

def Rectangle.ofDyadic : DyadicRectangle → Rectangle
  | ⟨r,i,e⟩ => ⟨r,i,e⟩

def Triple.ofVector (a : Fin 3 → DyadicRectangle) : Triple :=
  ⟨Rectangle.ofDyadic (a 0),Rectangle.ofDyadic (a 1),Rectangle.ofDyadic (a 2)⟩

theorem Triple.toVector_ofVector (a : Fin 3 → DyadicRectangle) :
    (Triple.ofVector a).toVector = a := by
  ext i
  fin_cases i <;> rfl

theorem magneticCheck_sound (a : MagneticRow) (h : magneticCheck a = true) :
    DyadicRectangle.magneticCheck a.symbol.toVector a.weighted.toVector
      a.field.toVector a.result.toVector = true := by
  apply decide_eq_true
  simp only [magneticCheck, Bool.and_eq_true_iff] at h
  intro j
  fin_cases j
  · have hh := h.1.1
    rw [dotCheck_eq 52 52] at hh
    exact hh
  · have hh := h.1.2
    rw [dotCheck_eq 52 52] at hh
    exact hh
  · have hh := h.2
    rw [dotCheck_eq 52 52] at hh
    exact hh

theorem magneticCheck_of_vector (d w u v : Fin 3 → DyadicRectangle)
    (h : magneticCheck ⟨Triple.ofVector d, Triple.ofVector w,
      Triple.ofVector u, Triple.ofVector v⟩ = true) :
    DyadicRectangle.magneticCheck d w u v = true := by
  simpa only [Triple.toVector_ofVector] using magneticCheck_sound _ h

theorem magneticCheck_of_block {n m : ℕ} (a : Fin n → Fin m → MagneticRow)
    (rows : List MagneticRow)
    (hrows : rows = (List.ofFn (fun i => List.ofFn (a i))).flatten)
    (h : rows.all magneticCheck = true) (i : Fin n) (j : Fin m) :
    magneticCheck (a i j) = true := by
  apply List.all_eq_true.mp h
  rw [hrows]
  exact List.mem_flatten.mpr ⟨List.ofFn (a i), List.mem_ofFn.mpr ⟨i,rfl⟩,
    List.mem_ofFn.mpr ⟨j,rfl⟩⟩

end Maxwell.Certificate.DyadicKernel
