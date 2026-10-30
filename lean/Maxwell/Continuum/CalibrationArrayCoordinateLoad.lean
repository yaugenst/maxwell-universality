import Maxwell.Continuum.CalibrationArrayDecodeMachine
import Maxwell.Continuum.CalibrationRawFreeStaging

/-! The decoded unsigned cube coordinates are copied into the actual
signed-pair rational bank. Radius subtraction is represented by the two
numerator channels, so this transfer performs no rational normalization. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def coordinateLoad : List NatAssign.Instruction :=
  [.copy 317 (positivePort 13),.copy 311 (negativePort 13),.literal (denominatorPort 13) 1,
   .copy 319 (positivePort 14),.copy 311 (negativePort 14),.literal (denominatorPort 14) 1,
   .copy 320 (positivePort 15),.copy 311 (negativePort 15),.literal (denominatorPort 15) 1,
   .copy 316 (positivePort 23),.literal (negativePort 23) 0,.literal (denominatorPort 23) 1]

def loadedParts (v : ℕ → Parts) (n : ℕ → ℕ) : ℕ → Parts :=
  Function.update (Function.update (Function.update (Function.update v
    13 ⟨n 317,n 311,1⟩) 14 ⟨n 319,n 311,1⟩) 15 ⟨n 320,n 311,1⟩) 23 ⟨n 316,0,1⟩

theorem coordinateLoad_values (n : ℕ → ℕ) :
    NatAssign.values coordinateLoad n=writeParts (writeParts (writeParts (writeParts n
      13 ⟨n 317,n 311,1⟩) 14 ⟨n 319,n 311,1⟩) 15 ⟨n 320,n 311,1⟩) 23 ⟨n 316,0,1⟩ := by
  simp [coordinateLoad,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,writeParts,
    positivePort,negativePort,denominatorPort]

theorem writeParts_agrees (n : ℕ → ℕ) (v : ℕ → Parts) (S : Finset ℕ)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) (target : ℕ) (p : Parts) :
    ∀ k ∈ ids S, writeParts n target p k=dataValues (Function.update v target p) k := by
  intro k hk
  rw [← writeParts_dataValues]
  by_cases hp : k=positivePort target
  · subst k; simp [writeParts]
  · by_cases hm : k=negativePort target
    · subst k; simp [writeParts]
    · by_cases hd : k=denominatorPort target
      · subst k; simp [writeParts]
      · simp only [writeParts,Function.update_of_ne hp,Function.update_of_ne hm,
          Function.update_of_ne hd,hn k hk]

theorem coordinateLoad_agrees (n : ℕ → ℕ) (v : ℕ → Parts) (S : Finset ℕ)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) :
    ∀ k ∈ ids S, NatAssign.values coordinateLoad n k=dataValues (loadedParts v n) k := by
  rw [coordinateLoad_values]
  exact writeParts_agrees _ _ S (writeParts_agrees _ _ S (writeParts_agrees _ _ S
    (writeParts_agrees n v S hn 13 _) 14 _) 15 _) 23 _

theorem loadedParts_coordinates (v : ℕ → Parts) (n : ℕ → ℕ)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R)
    (hcoords : ∀ k, ![n 317,n 319,n 320] k=decodedCoordinates R i.val k) :
    ∀ k, RawFree.coordinates (loadedParts v n) k=RawFree.coordinatePart R i k := by
  intro k
  rw [coordinatePart_decode]
  have h := congrArg (fun x : ℕ => (⟨x,R,1⟩ : Parts)) (hcoords k)
  fin_cases k <;> simpa [RawFree.coordinates,loadedParts,hR] using h

theorem loadedParts_polarization (v : ℕ → Parts) (n : ℕ → ℕ)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hp : n 316=decodedPolarization i.val) :
    (loadedParts v n 23).value=((arrayPolarizationAt R i).val : ℚ) := by
  simp only [loadedParts,Function.update_self,Parts.value,Nat.cast_zero,sub_zero,Nat.cast_one,div_one,
    hp,arrayPolarizationAt_decode]

theorem coordinateLoad_executes (allIds : Finset ℕ)
    (hIds : ∀ k ∈ allIds, 4≤k) (hdecode : ports ⊆ allIds)
    (hparts : ids RawFree.stageRegisters ⊆ allIds)
    (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.stageRegisters, n k=dataValues v k)
    (B : ℕ) (hB : 1≤B) (hw : ∀ k ∈ allIds, (n k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code coordinateLoad) cost s t ∧
      cost≤2^96*(B+2)^2 ∧
      NatAssign.Bank allIds (NatAssign.values coordinateLoad n) t.val ∧
      RationalDataflow.Ready RawFree.stageRegisters (loadedParts v n) t ∧
      BinaryPrecision.Frame ({0,1,2,3} ∪ allIds) s.val t.val := by
  have d (i : ℕ) (hi : i ∈ ports) : i ∈ allIds := hdecode hi
  have valid : ∀ a ∈ coordinateLoad, a.Valid allIds := by
    simp [coordinateLoad,NatAssign.Instruction.Valid,d 311 (by decide),d 316 (by decide),
      d 317 (by decide),d 319 (by decide),d 320 (by decide),
      positivePort,negativePort,denominatorPort]
    and_intros <;> apply hparts <;> decide
  have literals : ∀ a ∈ coordinateLoad, a.literalWidth≤B := by
    simpa [coordinateLoad,NatAssign.Instruction.literalWidth] using hB
  obtain ⟨cost,t,he,hcost,bank,blank,frame⟩ := fixedBankStage_executes allIds hIds
    coordinateLoad valid (by decide) n B hw literals input tape s hs hz
  refine ⟨cost,t,he,?_,bank,⟨?_,blank⟩,frame⟩
  · exact hcost
  · intro k hk
    have hh := bank k (hparts hk)
    simpa only [coordinateLoad_agrees n v RawFree.stageRegisters hn k hk] using hh

#print axioms coordinateLoad_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
