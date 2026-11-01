import Maxwell.Continuum.CalibrationSeedRootTableLoop
import Maxwell.Continuum.CalibrationFourierTableData

/-! The produced dense table is the literal root-applied finite seed,
including its cube radius and coefficient ordering. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem outputCoordinate_surjective (M D : ℕ) (i : Fin (2*aliasArraySize (3*M+D))) :
    ∃row j p,outputCoordinate M D row j p=i := by
  obtain ⟨⟨p,k⟩,rfl⟩ := (GlobalPower.realIndex (3*M+D)).surjective i
  have hk : k.val<3*ArrayDecodeMachine.aliasRowCount (3*M+D) := by
    simpa only [aliasArraySize,ArrayDecodeMachine.aliasRowCount,Nat.mul_comm] using k.isLt
  let row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D)) := ⟨k.val/3,by omega⟩
  let j : Fin 3 := ⟨k.val%3,Nat.mod_lt _ (by decide)⟩
  refine ⟨row,j,p,?_⟩
  apply (GlobalPower.realIndex (3*M+D)).congr_arg
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change 3*(k.val/3)+k.val%3=k.val
    omega

theorem entryParts_value (M N : ℕ) [NeZero M] (scale : ℚ) (W ell : ℕ)
    (a : PartArray.Table (2*(2*rootDegree scale W ell+1)^3))
    (correct : CacheCorrect (rootDegree scale W ell) a
      (fun ν=>rectangleRational (computedRootCoefficient scale W ell ν)))
    (entryValid : ∀i,(a.get i).Valid) (u : Fin 3→ℕ) (j : Fin 3) (p : Fin 2)
    (v : ℕ→Parts) (good : Good slots (resetParts v))
    (seed : (v (28+j.val)).value=seedComponent N j) :
    (entryParts M (rootDegree scale W ell) a u j p v).value=
      scalarPart ((FourierData.rootApply scale W ell (Supercell.finiteSeed M N)).field
        (outputAlias M (rootDegree scale W ell) u) j) p := by
  have hj := j.isLt
  apply terms_rootApply M N scale W ell a correct entryValid u j p (resetParts v) good
  · simpa [resetParts,resetList_values,show 28+j.val≠24 by omega,
      show 28+j.val≠25 by omega,show 28+j.val≠26 by omega,show 28+j.val≠27 by omega] using seed
  · simp [resetParts,resetList_values,Parts.literal,Parts.value]

theorem TableState.samples {M N B : ℕ} [NeZero M] {scale : ℚ} {W ell : ℕ}
    {a : PartArray.Table (2*(2*rootDegree scale W ell+1)^3)} {v : ℕ→Parts} {s : Store}
    (h : TableState M (rootDegree scale W ell) B a v 0 s)
    (correct : CacheCorrect (rootDegree scale W ell) a
      (fun ν=>rectangleRational (computedRootCoefficient scale W ell ν)))
    (entryValid : ∀i,(a.get i).Valid) (good : Good slots (resetParts v))
    (seed : ∀j,(v (28+j.val)).value=seedComponent N j)
    (i : Fin (2*aliasArraySize (3*M+rootDegree scale W ell))) :
    (h.table.get i).value=GlobalPower.sample (3*M+rootDegree scale W ell)
      (FourierData.rootApply scale W ell (Supercell.finiteSeed M N)).field i := by
  obtain ⟨row,j,p,rfl⟩ := outputCoordinate_surjective M (rootDegree scale W ell) i
  rw [h.correct row (Nat.zero_le _) j p,entryParts_value M N scale W ell a correct entryValid _ j p v good (seed j)]
  exact (sample_outputCoordinate M (rootDegree scale W ell) row j p _).symm

theorem TableState.rootApply {M N B : ℕ} [NeZero M] {scale : ℚ} {W ell : ℕ}
    {a : PartArray.Table (2*(2*rootDegree scale W ell+1)^3)} {v : ℕ→Parts} {s : Store}
    (h : TableState M (rootDegree scale W ell) B a v 0 s)
    (correct : CacheCorrect (rootDegree scale W ell) a
      (fun ν=>rectangleRational (computedRootCoefficient scale W ell ν)))
    (entryValid : ∀i,(a.get i).Valid) (good : Good slots (resetParts v))
    (seed : ∀j,(v (28+j.val)).value=seedComponent N j) :
    GlobalPower.tableData (3*M+rootDegree scale W ell) h.table=
      FourierData.rootApply scale W ell (Supercell.finiteSeed M N) := by
  apply GlobalPower.tableData_eq
  · change M*3+rootDegree scale W ell=3*M+rootDegree scale W ell
    rw [Nat.mul_comm M 3]
  · exact h.samples correct entryValid good seed

#print axioms TableState.rootApply
end Maxwell.Continuum.Calibration.SeedRoot
