import Maxwell.Continuum.CutoffMonomialRowMachine
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! The padded cached arrays store the literal two Chebyshev rows and their
weighted accumulator. Every row-update input is identified with that state. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def MonomialStored {D : ℕ} (a : Table (4*(D+1))) (v : MonomialState D) : Prop :=
  a.getD 1=Parts.literal 0 ∧ ∀r : Fin D,
    a.getD (4*r.val+4)=v.older.get r ∧
    a.getD (4*r.val+5)=v.current.get r ∧
    a.getD (4*r.val+6)=v.total.get r

theorem MonomialStored.previous {D : ℕ} {a : Table (4*(D+1))} {v : MonomialState D}
    (h : MonomialStored a v) (r : Fin D) :
    a.getD (4*r.val+1)=if _hr : r.val=0 then Parts.literal 0 else v.current.get ⟨r.val-1,by omega⟩ := by
  split_ifs with hr
  · simpa only [hr,Nat.mul_zero,Nat.zero_add] using h.1
  · have he : 4*(r.val-1)+5=4*r.val+1 := by omega
    simpa only [he] using (h.2 ⟨r.val-1,by omega⟩).2.1

theorem monomialLoaded_eq {n : ℕ} (a : Table n) (row : ℕ) (v : ℕ→Parts) :
    monomialLoaded a row v=
      Function.update (Function.update (Function.update (Function.update v
        0 (a.getD (4*row+4))) 1 (a.getD (4*row+5))) 2 (a.getD (4*row+1))) 3 (a.getD (4*row+6)) := rfl

theorem monomialLoaded_stored {D : ℕ} (a : Table (4*(D+1))) (q : MonomialState D)
    (h : MonomialStored a q) (r : Fin D) (v : ℕ→Parts) :
    monomialLoaded a r.val v=
      Function.update (Function.update (Function.update (Function.update v
        0 (q.older.get r)) 1 (q.current.get r))
          2 (if _hr : r.val=0 then Parts.literal 0 else q.current.get ⟨r.val-1,by omega⟩))
            3 (q.total.get r) := by
  rw [monomialLoaded_eq,(h.2 r).1,(h.2 r).2.1,h.previous r,(h.2 r).2.2]

theorem monomialRowState_coordinates {D : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts)
    (j : ℕ) (h : MonomialStored a (monomialState D coeff j)) (r : Fin D) (v : ℕ→Parts)
    (h4 : v 4=coeff j) (h5 : v 5=Parts.literal 2) :
    monomialRowState a r.val v 1=(monomialState D coeff (j+1)).older.get r ∧
    monomialRowState a r.val v 6=(monomialState D coeff (j+1)).current.get r ∧
    monomialRowState a r.val v 7=(monomialState D coeff (j+1)).total.get r := by
  change monomialRowControl.evaluate (monomialLoaded a r.val v) 1=_ ∧
    monomialRowControl.evaluate (monomialLoaded a r.val v) 6=_ ∧
    monomialRowControl.evaluate (monomialLoaded a r.val v) 7=_
  have hr := monomialRowControl_result (monomialLoaded a r.val v)
  rw [hr.1,hr.2.1,hr.2.2,monomialLoaded_stored a _ h r v]
  simp (disch := decide) only [Function.update_self,Function.update_of_ne,h4,h5]
  exact ⟨rfl,by simp only [monomialState,vector_get_ofFn],by simp only [monomialState,vector_get_ofFn]⟩

def monomialStorageWidth (D W : ℕ) : ℕ := D*(W+2*D+3)+W+8*D+16

theorem monomialState_row_width (D W : ℕ) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (j : ℕ) (hj : j≤D) (r : Fin D) :
    ((monomialState D coeff j).older.get r).Width (monomialStorageWidth D W) ∧
    ((monomialState D coeff j).current.get r).Width (monomialStorageWidth D W) ∧
    ((monomialState D coeff j).total.get r).Width (monomialStorageWidth D W) := by
  have rows := monomialState_rows D coeff j
  have hr := rawChebyshevState_width D j
  refine ⟨?_,?_,?_⟩
  · rw [rows.1]
    exact (hr.1 r).mono (by unfold monomialStorageWidth;omega)
  · rw [rows.2]
    exact (hr.2 r).mono (by unfold monomialStorageWidth;omega)
  · exact (monomialState_total_width D W coeff hw j hj r).mono
      (by unfold monomialStorageWidth;omega)

theorem monomialState_row_valid (D : ℕ) (coeff : ℕ→Parts)
    (hv : ∀j,(coeff j).Valid) (j : ℕ) (r : Fin D) :
    ((monomialState D coeff j).older.get r).Valid ∧
    ((monomialState D coeff j).current.get r).Valid ∧
    ((monomialState D coeff j).total.get r).Valid := by
  have rows := monomialState_rows D coeff j
  have hr := rawChebyshevState_valid D j
  refine ⟨?_,?_,monomialState_total_valid D coeff j (fun k _ => hv k) r⟩
  · rw [rows.1]; exact hr.1 r
  · rw [rows.2]; exact hr.2 r

theorem monomialLoaded_width {D W : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hw : ∀j<D,(coeff j).Width W) (j : ℕ) (hj : j≤D)
    (h : MonomialStored a (monomialState D coeff j)) (r : Fin D) (v : ℕ→Parts)
    (hv : WidthBank (Finset.range 8) (monomialStorageWidth D W) v) :
    WidthBank (Finset.range 8) (monomialStorageWidth D W) (monomialLoaded a r.val v) := by
  rw [monomialLoaded_stored a _ h r v]
  have hr := monomialState_row_width D W coeff hw j hj r
  apply (((hv.update 0 hr.1).update 1 hr.2.1).update 2 ?_).update 3 hr.2.2
  split_ifs with hzero
  · exact (Parts.literal_width RationalWords.width_zero').mono (by unfold monomialStorageWidth;omega)
  · exact (monomialState_row_width D W coeff hw j hj ⟨r.val-1,by omega⟩).2.1

theorem monomialLoaded_good {D : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts)
    (hc : ∀j,(coeff j).Valid) (j : ℕ)
    (h : MonomialStored a (monomialState D coeff j)) (r : Fin D) (v : ℕ→Parts)
    (hv : Good (Finset.range 8) v) : Good (Finset.range 8) (monomialLoaded a r.val v) := by
  rw [monomialLoaded_stored a _ h r v]
  have hr := monomialState_row_valid D coeff hc j r
  apply (((hv.update 0 hr.1).update 1 hr.2.1).update 2 ?_).update 3 hr.2.2
  split_ifs with hzero
  · exact Parts.literal_valid _
  · exact (monomialState_row_valid D coeff hc j ⟨r.val-1,by omega⟩).2.1

#print axioms monomialRowState_coordinates
#print axioms monomialLoaded_width
end Maxwell.Continuum.Calibration.RawCutoff
