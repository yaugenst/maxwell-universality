import Maxwell.Continuum.CutoffMonomialPassMeaning

/-! The unused fourth lane of each cached polynomial row stores the input
profile coefficient. Actual recurrence writes preserve every such lane. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost
set_option maxHeartbeats 1500000

def MonomialCoefficientsStored {D : ℕ} (a : Table (4*(D+1))) (coeff : ℕ→Parts) : Prop :=
  ∀r : Fin D,a.getD (4*r.val+7)=coeff r.val

theorem monomialRowTable_coefficient {D : ℕ} (a b : Table (4*(D+1)))
    (row : ℕ) (v : ℕ→Parts) (r : Fin D) :
    (monomialRowTable a b row v).getD (4*r.val+7)=b.getD (4*r.val+7) := by
  have hix : 4*r.val+7<4*(D+1) := by omega
  simp only [monomialRowTable,Table.getD,dite_eq_left hix]
  apply rowWriteTable_get_unchanged
  intro x hx
  simp only [monomialWritePlan,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp only <;> omega

theorem monomialPassTable_coefficient {D : ℕ} (a b : Table (4*(D+1)))
    (v : ℕ→Parts) (k : ℕ) (r : Fin D) :
    (monomialPassTable a b v k).getD (4*r.val+7)=b.getD (4*r.val+7) := by
  induction k with
  | zero => rfl
  | succ k ih => exact (monomialRowTable_coefficient a _ _ _ r).trans ih

theorem MonomialCoefficientsStored.pass {D : ℕ} (a b : Table (4*(D+1)))
    (coeff : ℕ→Parts) (h : MonomialCoefficientsStored b coeff) (v : ℕ→Parts) (k : ℕ) :
    MonomialCoefficientsStored (monomialPassTable a b v k) coeff := by
  intro r
  exact (monomialPassTable_coefficient a b v k r).trans (h r)

#print axioms MonomialCoefficientsStored.pass
end Maxwell.Continuum.Calibration.RawCutoff
