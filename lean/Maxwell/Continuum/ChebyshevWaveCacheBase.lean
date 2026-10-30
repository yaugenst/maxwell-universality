import Maxwell.Continuum.ChebyshevWaveCacheData

/-! The rational entry bank is prepared from its actual stored frequency
and the computed grid word. The reciprocal grid is represented by its
literal denominator, without a host-supplied rational. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def baseInstructions : List RationalDataflow.Instruction :=
  [.literal 0 0,.literal 1 0,.literal 2 0,.literal 3 0,.literal 4 0,
   .literal 5 0,.literal 6 0,.literal 7 0,.literal 8 0,.literal 9 0,
   .literal 11 1,.literal 12 0,.literal 13 0,.literal 14 (-1),.literal 15 1]
def baseCleared (v : ℕ→Parts) : ℕ→Parts := evaluate baseInstructions v
def baseValues (grid : ℕ) (v : ℕ→Parts) : ℕ→Parts := Function.update (baseCleared v) 11 ⟨1,0,grid⟩
def baseCode : Code := .seq (program baseInstructions) (NaturalChannel.code .denominator 681 11)
def baseCost (W grid : ℕ) : ℕ := 15*operationCost (W+1)+31*grid.bits.length+46

theorem baseInstructions_valid : ∀a∈baseInstructions,a.Valid ids := by
  simp [baseInstructions,RationalDataflow.Instruction.Valid,ids]

theorem baseCleared_eq (v : ℕ→Parts) (i : ℕ) : baseCleared v i=
    if i=11 ∨ i=15 then Parts.literal 1 else if i=14 then Parts.literal (-1) else
      if i<10 ∨ i=12 ∨ i=13 then Parts.literal 0 else v i := by
  by_cases hi : i<16
  · interval_cases i <;> simp [baseCleared,baseInstructions,evaluate,RationalDataflow.Instruction.update]
  · simp (disch := omega) [baseCleared,baseInstructions,evaluate,RationalDataflow.Instruction.update]
    split_ifs <;> first | omega | rfl

theorem baseValues_eq (grid : ℕ) (v : ℕ→Parts) (i : ℕ) : baseValues grid v i=
    if i=11 then ⟨1,0,grid⟩ else if i=15 then Parts.literal 1 else
      if i=14 then Parts.literal (-1) else if i<10 ∨ i=12 ∨ i=13 then Parts.literal 0 else v i := by
  by_cases hi : i=11
  · simp [baseValues,hi]
  · simp [baseValues,baseCleared_eq,hi]

theorem baseValues_good (grid : ℕ) (hgrid : 0<grid) (v : ℕ→Parts) (hv : (v 10).Valid) :
    Good ids (baseValues grid v) := by
  intro i hi
  have hil : i<16 := Finset.mem_range.mp hi
  rw [baseValues_eq]
  split_ifs with h11 h15 h14 hzero
  · exact hgrid
  · exact Parts.literal_valid 1
  · exact Parts.literal_valid (-1)
  · exact Parts.literal_valid 0
  · have he : i=10 := by omega
    simpa only [he] using hv

theorem baseValues_width (grid W : ℕ) (v : ℕ→Parts) (hv : (v 10).Width W)
    (hgrid : grid.bits.length≤W) (hW : 1≤W) : WidthBank ids W (baseValues grid v) := by
  intro i hi
  have hil : i<16 := Finset.mem_range.mp hi
  rw [baseValues_eq]
  split_ifs with h11 h15 h14 hzero
  · exact ⟨by simpa using hW,by simp,hgrid⟩
  · exact (show (Parts.literal 1).Width 1 by unfold Parts.Width Parts.literal;decide).mono hW
  · exact (show (Parts.literal (-1)).Width 1 by unfold Parts.Width Parts.literal;decide).mono hW
  · exact (show (Parts.literal 0).Width 1 by unfold Parts.Width Parts.literal;decide).mono hW
  · have he : i=10 := by omega
    simpa only [he] using hv

theorem baseValues_input (grid : ℕ) (v : ℕ→Parts) :
    SumInput grid (v 10).value 0 0 (baseValues grid v) := by
  constructor <;> simp [baseValues_eq,Parts.value,Parts.literal]

theorem baseValues_one (grid : ℕ) (v : ℕ→Parts) : baseValues grid v 15=⟨1,0,1⟩ := by
  simp [baseValues_eq,Parts.literal]

theorem baseInstructions_width (W : ℕ) : programWidth baseInstructions (fun _ => W)≤W+1 := by
  simp [baseInstructions,programWidth,RationalDataflow.Instruction.resultWidth,Parts.literal]

theorem base_executes (grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s)
    (hgrid : Word s.val 681 grid) :
    ∃cost t,Executes input tape baseCode cost s t ∧ cost≤baseCost W grid ∧
      Ready ids (baseValues grid v) t ∧ BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val := by
  have ht := inferred_widthTrace ids baseInstructions baseInstructions_valid (fun _ => W) v hw _
    (hw.mono (by omega)) (baseInstructions_width W)
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := program_executes ids baseInstructions baseInstructions_valid
    v (W+1) ht input tape s hs
  change Ready ids (baseCleared v) s0 at b0
  have grid0 := word_of_eq (f0.tapes 681 (RationalDataflow.outside_workspace ids 681 (by decide))) hgrid
  obtain ⟨c1,t,e1,h1,b1,f1⟩ := NaturalChannel.executes ids .denominator 681 11 (by decide) (by decide)
    (baseCleared v) grid.bits input tape s0 b0 grid0
  rw [addressValue_bits] at b1
  have he : Function.update (baseCleared v) 11
      (NaturalChannel.replace .denominator (baseCleared v 11) grid)=baseValues grid v := by
    simp [baseValues,NaturalChannel.replace,baseCleared_eq,Parts.literal]
  rw [he] at b1
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,f0.trans (f1.mono ?_)⟩
  · have h0' : c0≤15*operationCost (W+1)+1 := by simpa only [show baseInstructions.length=15 by rfl] using h0
    have hc : dataValues (baseCleared v) (NaturalChannel.port .denominator 11)=1 := by
      simp [NaturalChannel.port,dataValues_denominator,baseCleared_eq,Parts.literal]
    rw [hc] at h1
    change c1≤6+31*grid.bits.length+39 at h1
    unfold baseCost
    omega
  · exact Finset.singleton_subset_iff.mpr
      (Finset.mem_union_right _ (NaturalChannel.port_mem .denominator ids 11 (by decide)))

#print axioms base_executes
#print axioms baseValues_input
end Maxwell.Continuum.Profile.WaveMachine.Runtime
