import Maxwell.Continuum.CalibrationArrayDecodeLoad
import Maxwell.Continuum.CalibrationNeighborControl

/-! The same runtime alias decoder feeds column coordinates and its
polarization into disjoint rational registers for matrix-table emission. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def columnLoad : List NatAssign.Instruction :=
  [.copy 317 (positivePort 28),.copy 311 (negativePort 28),.literal (denominatorPort 28) 1,
   .copy 319 (positivePort 29),.copy 311 (negativePort 29),.literal (denominatorPort 29) 1,
   .copy 320 (positivePort 30),.copy 311 (negativePort 30),.literal (denominatorPort 30) 1,
   .copy 316 (positivePort 24),.literal (negativePort 24) 0,.literal (denominatorPort 24) 1]

def columnParts (v : ℕ → Parts) (n : ℕ → ℕ) : ℕ → Parts :=
  Function.update (Function.update (Function.update (Function.update v
    28 ⟨n 317,n 311,1⟩) 29 ⟨n 319,n 311,1⟩) 30 ⟨n 320,n 311,1⟩) 24 ⟨n 316,0,1⟩

theorem columnLoad_values (n : ℕ → ℕ) :
    NatAssign.values columnLoad n=writeParts (writeParts (writeParts (writeParts n
      28 ⟨n 317,n 311,1⟩) 29 ⟨n 319,n 311,1⟩) 30 ⟨n 320,n 311,1⟩) 24 ⟨n 316,0,1⟩ := by
  simp [columnLoad,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,writeParts,
    positivePort,negativePort,denominatorPort]

theorem columnLoad_agrees (n : ℕ → ℕ) (v : ℕ → Parts) (S : Finset ℕ)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) :
    ∀ k ∈ ids S, NatAssign.values columnLoad n k=dataValues (columnParts v n) k := by
  rw [columnLoad_values]
  exact writeParts_agrees _ _ S (writeParts_agrees _ _ S (writeParts_agrees _ _ S
    (writeParts_agrees n v S hn 28 _) 29 _) 30 _) 24 _

theorem columnParts_coordinates (v : ℕ → Parts) (n : ℕ → ℕ)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R)
    (hcoords : ∀ k, ![n 317,n 319,n 320] k=decodedCoordinates R i.val k) :
    ∀ k, RawFree.columnCoordinates (columnParts v n) k=RawFree.coordinatePart R i k := by
  intro k
  rw [coordinatePart_decode]
  have h := congrArg (fun x : ℕ => (⟨x,R,1⟩ : Parts)) (hcoords k)
  fin_cases k <;> simpa [RawFree.columnCoordinates,columnParts,hR] using h

theorem columnParts_polarization (v : ℕ → Parts) (n : ℕ → ℕ)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hp : n 316=decodedPolarization i.val) :
    (columnParts v n 24).value=((arrayPolarizationAt R i).val : ℚ) := by
  simp only [columnParts,Function.update_self,Parts.value,Nat.cast_zero,sub_zero,Nat.cast_one,div_one,
    hp,arrayPolarizationAt_decode]

theorem columnParts_good (v : ℕ → Parts) (n : ℕ → ℕ) (S : Finset ℕ) (hg : Good S v) :
    Good S (columnParts v n) :=
  (((hg.update 28 (by change 0<1; decide : (⟨n 317,n 311,1⟩:Parts).Valid)).update
    29 (by change 0<1; decide : (⟨n 319,n 311,1⟩:Parts).Valid)).update
    30 (by change 0<1; decide : (⟨n 320,n 311,1⟩:Parts).Valid)).update
    24 (by change 0<1; decide : (⟨n 316,0,1⟩:Parts).Valid)

theorem nat_update_width (n : ℕ → ℕ) (S : Finset ℕ) (B target x : ℕ)
    (hn : ∀ k ∈ S, (n k).bits.length≤B) (hx : x.bits.length≤B) :
    ∀ k ∈ S, (Function.update n target x k).bits.length≤B := by
  intro k hk
  by_cases he : k=target
  · subst k; simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne he] using hn k hk

theorem writeParts_width (n : ℕ → ℕ) (S : Finset ℕ) (B target : ℕ) (p : Parts)
    (hn : ∀ k ∈ S, (n k).bits.length≤B) (hp : p.Width B) :
    ∀ k ∈ S, (writeParts n target p k).bits.length≤B :=
  nat_update_width _ S B _ _ (nat_update_width _ S B _ _ (nat_update_width n S B _ _ hn hp.1)
    hp.2.1) hp.2.2

theorem load_parts_width (n : ℕ → ℕ) (B : ℕ) (hB : 1≤B)
    (hn : ∀ k ∈ ports, (n k).bits.length≤B) :
    (⟨n 317,n 311,1⟩:Parts).Width B ∧ (⟨n 319,n 311,1⟩:Parts).Width B ∧
    (⟨n 320,n 311,1⟩:Parts).Width B ∧ (⟨n 316,0,1⟩:Parts).Width B :=
  ⟨⟨hn 317 (by decide),hn 311 (by decide),by simpa using hB⟩,
    ⟨hn 319 (by decide),hn 311 (by decide),by simpa using hB⟩,
    ⟨hn 320 (by decide),hn 311 (by decide),by simpa using hB⟩,
    ⟨hn 316 (by decide),by simp,by simpa using hB⟩⟩

theorem columnLoad_width (n : ℕ → ℕ) (S : Finset ℕ) (hS : ports ⊆ S) (B : ℕ) (hB : 1≤B)
    (hn : ∀ k ∈ S, (n k).bits.length≤B) :
    ∀ k ∈ S, (NatAssign.values columnLoad n k).bits.length≤B := by
  obtain ⟨h0,h1,h2,h3⟩ := load_parts_width n B hB (fun k hk => hn k (hS hk))
  rw [columnLoad_values]
  exact writeParts_width _ S B _ _ (writeParts_width _ S B _ _
    (writeParts_width _ S B _ _ (writeParts_width _ S B _ _ hn h0) h1) h2) h3

theorem coordinateLoad_width (n : ℕ → ℕ) (S : Finset ℕ) (hS : ports ⊆ S) (B : ℕ) (hB : 1≤B)
    (hn : ∀ k ∈ S, (n k).bits.length≤B) :
    ∀ k ∈ S, (NatAssign.values coordinateLoad n k).bits.length≤B := by
  obtain ⟨h0,h1,h2,h3⟩ := load_parts_width n B hB (fun k hk => hn k (hS hk))
  rw [coordinateLoad_values]
  exact writeParts_width _ S B _ _ (writeParts_width _ S B _ _
    (writeParts_width _ S B _ _ (writeParts_width _ S B _ _ hn h0) h1) h2) h3

theorem columnLoad_executes (allIds : Finset ℕ)
    (hIds : ∀ k ∈ allIds, 4≤k) (hdecode : ports ⊆ allIds)
    (hparts : ids RawFree.neighborRegisters ⊆ allIds)
    (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.neighborRegisters, n k=dataValues v k)
    (B : ℕ) (hB : 1≤B) (hw : ∀ k ∈ allIds, (n k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code columnLoad) cost s t ∧
      cost≤2^96*(B+2)^2 ∧ NatAssign.Bank allIds (NatAssign.values columnLoad n) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (columnParts v n) t ∧
      BinaryPrecision.Frame ({0,1,2,3} ∪ allIds) s.val t.val := by
  have d (i : ℕ) (hi : i ∈ ports) : i ∈ allIds := hdecode hi
  have valid : ∀ a ∈ columnLoad, a.Valid allIds := by
    simp [columnLoad,NatAssign.Instruction.Valid,d 311 (by decide),d 316 (by decide),
      d 317 (by decide),d 319 (by decide),d 320 (by decide),positivePort,negativePort,denominatorPort]
    and_intros <;> apply hparts <;> decide
  have literals : ∀ a ∈ columnLoad, a.literalWidth≤B := by
    simpa [columnLoad,NatAssign.Instruction.literalWidth] using hB
  obtain ⟨cost,t,he,hcost,bank,blank,frame⟩ := fixedBankStage_executes allIds hIds
    columnLoad valid (by decide) n B hw literals input tape s hs hz
  refine ⟨cost,t,he,hcost,bank,⟨?_,blank⟩,frame⟩
  intro k hk
  have hh := bank k (hparts hk)
  simpa only [columnLoad_agrees n v RawFree.neighborRegisters hn k hk] using hh

#print axioms columnLoad_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
