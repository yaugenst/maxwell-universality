import Maxwell.Continuum.CalibrationArrayColumnLoad

/-! Exact register meanings for the two runtime Fourier-index decodes.
The row index is held in natural port 321 while the column is decoded. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def columnNaturals (n : ℕ → ℕ) : ℕ → ℕ := NatAssign.values columnLoad (output n)
def rowStart (n : ℕ → ℕ) : ℕ → ℕ := Function.update (columnNaturals n) 310 (n 321)
def matrixNaturals (n : ℕ → ℕ) : ℕ → ℕ := NatAssign.values coordinateLoad (output (rowStart n))
def matrixParts (v : ℕ → Parts) (n : ℕ → ℕ) : ℕ → Parts :=
  loadedParts (columnParts v (output n)) (output (rowStart n))
def matrixDecodeCode : Code := .seq code (.seq (NatAssign.code columnLoad)
  (.seq (NatAssign.code [.copy 321 310]) (.seq code (NatAssign.code coordinateLoad))))

theorem rational_port_outside_all (S : Finset ℕ) (k : ℕ) (hk : k ∈ ids S) : k ∉ ports := by
  rcases Finset.mem_union.mp hk with hp | hw
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    have h0 := positivePort_ge i
    have h1 := negativePort_ge i
    have h2 := denominatorPort_ge i
    simp only [ports,Finset.mem_Icc]
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hw
    simp only [ports,Finset.mem_Icc]
    omega

theorem output_agrees_all (S : Finset ℕ) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) :
    ∀ k ∈ ids S, output n k=dataValues v k := by
  intro k hk
  rw [output_outside n k (rational_port_outside_all S k hk),hn k hk]

theorem columnLoad_small (n : ℕ → ℕ) (k : ℕ) (hk : k<1000) :
    NatAssign.values columnLoad n k=n k := by
  rw [columnLoad_values]
  simp (disch := omega) only [writeParts,positivePort,negativePort,denominatorPort,Function.update_of_ne]

theorem columnNaturals_small (n : ℕ → ℕ) (k : ℕ) (hk : k<1000) :
    columnNaturals n k=output n k := columnLoad_small (output n) k hk

theorem rowStart_index (n : ℕ → ℕ) : rowStart n 310=n 321 := Function.update_self _ _ _
theorem rowStart_radius (n : ℕ → ℕ) : rowStart n 311=n 311 := by
  rw [rowStart,Function.update_of_ne (by decide : (311:ℕ)≠310),columnNaturals_small n 311 (by decide),output_radius]

theorem rowStart_agrees (S : Finset ℕ) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) :
    ∀ k ∈ ids S, rowStart n k=dataValues (columnParts v (output n)) k := by
  intro k hk
  have ho := rational_port_outside_all S k hk
  have hne : k≠310 := fun he => ho (he ▸ (by decide : 310∈ports))
  rw [rowStart,Function.update_of_ne hne]
  exact columnLoad_agrees (output n) v S (output_agrees_all S n v hn) k hk

theorem matrixNaturals_agrees (S : Finset ℕ) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) :
    ∀ k ∈ ids S, matrixNaturals n k=dataValues (matrixParts v n) k :=
  coordinateLoad_agrees (output (rowStart n)) (columnParts v (output n)) S
    (output_agrees_all S _ _ (rowStart_agrees S n v hn))

theorem matrixParts_good (S : Finset ℕ) (n : ℕ → ℕ) (v : ℕ → Parts) (hg : Good S v) :
    Good S (matrixParts v n) := by
  have h := columnParts_good v (output n) S hg
  apply Good.update (Good.update (Good.update (Good.update h 13 ?_) 14 ?_) 15 ?_) 23 ?_
  all_goals change 0<1; decide

theorem matrixParts_row (n : ℕ → ℕ) (v : ℕ → Parts) (R : ℕ) (i j : Fin (aliasArraySize R))
    (hR : n 311=R) (hi : n 321=i.val) (_hj : n 310=j.val) :
    (∀ k, RawFree.coordinates (matrixParts v n) k=RawFree.coordinatePart R i k) ∧
    (matrixParts v n 23).value=((arrayPolarizationAt R i).val : ℚ) := by
  constructor
  · apply loadedParts_coordinates
    · rw [output_radius,rowStart_radius,hR]
    · intro k
      simpa only [rowStart_radius,rowStart_index,hR,hi] using output_coordinates (rowStart n) k
  · apply loadedParts_polarization
    rw [output_polarization,rowStart_index,hi]

theorem matrixParts_column (n : ℕ → ℕ) (v : ℕ → Parts) (R : ℕ) (i j : Fin (aliasArraySize R))
    (hR : n 311=R) (_hi : n 321=i.val) (hj : n 310=j.val) :
    (∀ k, RawFree.columnCoordinates (matrixParts v n) k=RawFree.coordinatePart R j k) ∧
    (matrixParts v n 24).value=((arrayPolarizationAt R j).val : ℚ) := by
  have hc := columnParts_coordinates v (output n) R j (by rw [output_radius,hR])
    (fun k => by simpa only [hR,hj] using output_coordinates n k)
  have hp := columnParts_polarization v (output n) R j (by rw [output_polarization,hj])
  constructor
  · intro k
    have he : RawFree.columnCoordinates (matrixParts v n) k=
        RawFree.columnCoordinates (columnParts v (output n)) k := by
      fin_cases k <;> simp [RawFree.columnCoordinates,matrixParts,loadedParts]
    exact he.trans (hc k)
  · simpa [matrixParts,loadedParts] using hp

theorem matrixParts_input (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ)
    (hk : k<13 ∨ 15<k ∧ k<23 ∨ 24<k ∧ k<28 ∨ 30<k) : matrixParts v n k=v k := by
  simp (disch := omega) [matrixParts,loadedParts,columnParts]

theorem data_width_all (S : Finset ℕ) (n : ℕ → ℕ) (v : ℕ → Parts) (B : ℕ)
    (hn : ∀ k ∈ ids S, n k=dataValues v k) (hw : ∀ k ∈ ids S, (n k).bits.length≤B) :
    WidthBank S B v := by
  intro i hi
  have hp := hw (positivePort i) (cell_mem hi (by simp [cellPorts]))
  have hm := hw (negativePort i) (cell_mem hi (by simp [cellPorts]))
  have hd := hw (denominatorPort i) (cell_mem hi (by simp [cellPorts]))
  rw [hn _ (cell_mem hi (by simp [cellPorts])),dataValues_positive] at hp
  rw [hn _ (cell_mem hi (by simp [cellPorts])),dataValues_negative] at hm
  rw [hn _ (cell_mem hi (by simp [cellPorts])),dataValues_denominator] at hd
  exact ⟨hp,hm,hd⟩

#print axioms matrixParts_row
#print axioms matrixParts_column

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
