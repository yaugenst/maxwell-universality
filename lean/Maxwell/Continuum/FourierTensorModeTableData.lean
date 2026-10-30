import Maxwell.Continuum.FourierTensorModeResetData
import Maxwell.Continuum.FourierTensorModeWrite
import Maxwell.Continuum.RationalDataflowSharedMapState
import Maxwell.Continuum.FourierTensorAliasData

/-! Exact contents of the generated five-column input table. A descending
five-write row agrees with the actual filled-array countdown invariant. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def fields (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) : Fin 5→Parts :=
  ![values P R a j r v 4,values P R a j r v 5,values P R a j r v 6,
    values P R a j r v 9,values P R a j r v 10]

def entryEquiv (n : ℕ) : Fin n×Fin 5≃Fin (5*n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 5))

def entries (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3) (v : ℕ→Parts) :
    Fin (5*RowArithmetic.rowCount R)→Parts := fun i =>
  fields P R a j ((entryEquiv _).symm i).1 v ((entryEquiv _).symm i).2

theorem entries_row (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) (k : Fin 5) :
    entries P R a j v ⟨5*r.val+k.val,by have := r.isLt;have := k.isLt;omega⟩=fields P R a j r v k := by
  have he : (⟨5*r.val+k.val,by have := r.isLt;have := k.isLt;omega⟩:Fin (5*RowArithmetic.rowCount R))=
      entryEquiv _ (r,k) := by
    apply Fin.ext
    simp [entryEquiv,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he,entries,Equiv.symm_apply_apply]

theorem fields_frequency (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) (k : Fin 3) :
    fields P R a j r v ⟨k.val,by omega⟩=RowArithmetic.output P (RowArithmetic.loaded R a j r v) (4+k.val) := by
  fin_cases k
  · exact ModeDecode.output_row P R a j r v 4 (by decide)
  · exact ModeDecode.output_row P R a j r v 5 (by decide)
  · exact ModeDecode.output_row P R a j r v 6 (by decide)

theorem filled_write_step (P R : ℕ) (a : Table (2*aliasArraySize R))
    (b : Table (5*RowArithmetic.rowCount R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) :
    written P R a (b.filled (entries P R a j v) (5*(r.val+1))) j r v=
      b.filled (entries P R a j v) (5*r.val) := by
  have valid (k : ℕ) (hk : k<5) : 5*r.val+k<5*RowArithmetic.rowCount R := by have := r.isLt;omega
  have step (k : Fin 5) :
      (b.filled (entries P R a j v) (5*r.val+k.val+1)).setD (5*r.val+k.val)
        (fields P R a j r v k)=b.filled (entries P R a j v) (5*r.val+k.val) := by
    rw [Table.setD,dite_eq_left (valid k.val k.isLt),←entries_row P R a j r v k,Table.filled_step]
  have h4 := step 4
  have h3 := step 3
  have h2 := step 2
  have h1 := step 1
  have h0 := step 0
  change (b.filled (entries P R a j v) (5*r.val+4+1)).setD (5*r.val+4) (values P R a j r v 10)=b.filled _ (5*r.val+4) at h4
  change (b.filled (entries P R a j v) (5*r.val+3+1)).setD (5*r.val+3) (values P R a j r v 9)=b.filled _ (5*r.val+3) at h3
  change (b.filled (entries P R a j v) (5*r.val+2+1)).setD (5*r.val+2) (values P R a j r v 6)=b.filled _ (5*r.val+2) at h2
  change (b.filled (entries P R a j v) (5*r.val+1+1)).setD (5*r.val+1) (values P R a j r v 5)=b.filled _ (5*r.val+1) at h1
  change (b.filled (entries P R a j v) (5*r.val+0+1)).setD (5*r.val+0) (values P R a j r v 4)=b.filled _ (5*r.val+0) at h0
  simp only [Nat.add_assoc,Nat.reduceAdd,Nat.add_zero] at h4 h3 h2 h1 h0
  simp only [show 5*(r.val+1)=5*r.val+5 by omega,written,writePlan,rowWriteTable,
    h4,h3,h2,h1,Nat.add_zero,h0]

#print axioms filled_write_step
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
