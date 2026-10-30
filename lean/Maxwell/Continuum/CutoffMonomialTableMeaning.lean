import Maxwell.Continuum.CutoffMonomialLayout

/-! The literal memory writes store the next cached Chebyshev/accumulator
row and leave all other rows, including the zero sentinel, unchanged. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem Table.setD_getD_eq {n : ℕ} (b : Table n) (i : ℕ) (hi : i<n) (x : Parts)
    (hx : x.Width (addressValue b.width)) : (b.setD i x).getD i=x := by
  rw [Table.setD,dite_eq_left hi]
  simp only [Table.getD,dite_eq_left hi]
  exact b.set_get ⟨i,hi⟩ x hx

theorem Table.setD_getD_ne {n : ℕ} (b : Table n) (i j : ℕ) (x : Parts) (hij : i≠j) :
    (b.setD i x).getD j=b.getD j := by
  by_cases hj : j<n
  · simp only [Table.getD,dite_eq_left hj]
    exact b.setD_get_ne i ⟨j,hj⟩ x hij
  · simp only [Table.getD,dite_eq_right hj]

theorem Table.setD_width {n : ℕ} (b : Table n) (i : ℕ) (x : Parts) : (b.setD i x).width=b.width := by
  unfold Table.setD
  split_ifs <;> rfl

end Maxwell.Continuum.RationalDataflow.PartArray

namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost

theorem monomialRowTable_coordinates {D : ℕ} (a b : Table (4*(D+1)))
    (r : Fin D) (v : ℕ→Parts)
    (hfit : ∀i∈[1,6,7],(monomialRowState a r.val v i).Width (addressValue b.width)) :
    (monomialRowTable a b r.val v).getD (4*r.val+4)=monomialRowState a r.val v 1 ∧
    (monomialRowTable a b r.val v).getD (4*r.val+5)=monomialRowState a r.val v 6 ∧
    (monomialRowTable a b r.val v).getD (4*r.val+6)=monomialRowState a r.val v 7 := by
  have h4 : 4*r.val+4<4*(D+1) := by omega
  have h5 : 4*r.val+5<4*(D+1) := by omega
  have h6 : 4*r.val+6<4*(D+1) := by omega
  simp only [monomialRowTable,monomialWritePlan,rowWriteTable]
  refine ⟨?_,?_,?_⟩
  · rw [Table.setD_getD_ne _ _ _ _ (by omega),Table.setD_getD_ne _ _ _ _ (by omega)]
    exact b.setD_getD_eq _ h4 _ (hfit 1 (by simp))
  · rw [Table.setD_getD_ne _ _ _ _ (by omega)]
    apply Table.setD_getD_eq _ _ h5
    simpa only [Table.setD_width] using hfit 6 (by simp)
  · apply Table.setD_getD_eq _ _ h6
    simpa only [Table.setD_width] using hfit 7 (by simp)

theorem monomialRowTable_other_row {D : ℕ} (a b : Table (4*(D+1)))
    (r s : Fin D) (hrs : r≠s) (v : ℕ→Parts) (lane : ℕ) (hl : lane∈[4,5,6]) :
    (monomialRowTable a b r.val v).getD (4*s.val+lane)=b.getD (4*s.val+lane) := by
  have hne : r.val≠s.val := fun h => hrs (Fin.ext h)
  have hix : 4*s.val+lane<4*(D+1) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    omega
  simp only [monomialRowTable,Table.getD,dite_eq_left hix]
  apply rowWriteTable_get_unchanged
  intro x hx
  simp only [monomialWritePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hx with rfl | rfl | rfl <;> simp only <;> omega

theorem monomialRowTable_sentinel {D : ℕ} (a b : Table (4*(D+1)))
    (row : ℕ) (v : ℕ→Parts) : (monomialRowTable a b row v).getD 1=b.getD 1 := by
  have hix : 1<4*(D+1) := by omega
  simp only [monomialRowTable,Table.getD,dite_eq_left hix]
  apply rowWriteTable_get_unchanged
  intro x hx
  simp only [monomialWritePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp only <;> omega

theorem monomialRowTable_next_row {D : ℕ} (a b : Table (4*(D+1))) (coeff : ℕ→Parts)
    (j : ℕ) (h : MonomialStored a (monomialState D coeff j)) (r : Fin D) (v : ℕ→Parts)
    (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2)
    (hfit : ∀i∈[1,6,7],(monomialRowState a r.val v i).Width (addressValue b.width)) :
    (monomialRowTable a b r.val v).getD (4*r.val+4)=(monomialState D coeff (j+1)).older.get r ∧
    (monomialRowTable a b r.val v).getD (4*r.val+5)=(monomialState D coeff (j+1)).current.get r ∧
    (monomialRowTable a b r.val v).getD (4*r.val+6)=(monomialState D coeff (j+1)).total.get r := by
  have hs := monomialRowState_coordinates a coeff j h r v h4 h5
  have ht := monomialRowTable_coordinates a b r v hfit
  exact ⟨ht.1.trans hs.1,ht.2.1.trans hs.2.1,ht.2.2.trans hs.2.2⟩

#print axioms monomialRowTable_next_row
end Maxwell.Continuum.Calibration.RawCutoff
