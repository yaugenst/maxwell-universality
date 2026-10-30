import Maxwell.Continuum.CalibrationRootFrequencyMachine
import Maxwell.Continuum.CalibrationRootComponent
import Maxwell.Continuum.RationalDataflowBankCongruence

/-! The reusable coefficient-call state has one retained rational scale.
All other shared operands are reset with charged instructions, so widths
do not multiply across the outer coefficient traversal. -/
namespace Maxwell.Continuum.RationalDataflow.RootReset
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def bank : Finset ℕ := Finset.range 13
def active : List ℕ := [0,1,2,3,4,5,6,7,8,10,11,12]
def instructions : List Instruction := active.map (fun i => .literal i 0)
def control : Control := Control.prepend instructions .done
def parts (scale : Parts) : ℕ→Parts := fun i => if i=9 then scale else Parts.literal 0

def naturalPlan : List NatAssign.Instruction :=
  [.literal 330 0,.literal 332 0,.literal 333 0,.literal 334 0,.literal 335 0,
   .literal 336 0,.literal 337 0,.literal 338 0,.literal 339 0,.literal 340 0,
   .literal 341 0,.literal 342 0,.literal 343 0,.literal 344 0]
def naturalValues (n : ℕ→ℕ) := NatAssign.values naturalPlan n
def naturals (grid : ℕ) : ℕ→ℕ := fun i => if i=331 then grid else 0

theorem valid : control.Valid bank := by
  simp [control,instructions,active,Control.prepend,Control.Valid,Instruction.Valid,bank]

theorem admissible (v : ℕ→Parts) : control.AdmissibleTrace v := by
  simp [control,instructions,active,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]

theorem literals (W : ℕ) (hW : 1≤W) : control.LiteralsFit W := by
  have hz : (Parts.literal 0).Width W :=
    (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hW
  simpa only [control,instructions,active,List.map_cons,List.map_nil,Control.prepend,List.foldr_cons,
    List.foldr_nil,Control.LiteralsFit,Instruction.LiteralFits,and_true,and_self] using hz

theorem steps : control.steps=12 := rfl

theorem output (v : ℕ→Parts) (i : ℕ) (hi : i∈bank) : control.evaluate v i=parts (v 9) i := by
  have hh : i<13 := Finset.mem_range.mp hi
  interval_cases i <;>
    simp [control,instructions,active,Control.prepend,Control.evaluate,Instruction.update,parts]

theorem parts_width (scale : Parts) (I : ℕ) (hI : 1≤I) (hscale : scale.Width I) :
    WidthBank bank I (parts scale) := by
  intro i _
  unfold parts
  split_ifs
  · exact hscale
  · exact (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hI

theorem parts_good (scale : Parts) (hscale : scale.Valid) : Good bank (parts scale) := by
  intro i _
  unfold parts
  split_ifs
  · exact hscale
  · exact Parts.literal_valid 0

theorem natural_valid : ∀a∈naturalPlan,a.Valid RootFrequency.ids := by
  simp [naturalPlan,NatAssign.Instruction.Valid,RootFrequency.ids]

theorem natural_output (n : ℕ→ℕ) (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (i : ℕ) (hi : i∈RootFrequency.ids) : naturalValues n i=naturals (n 331) i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · have hh := hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl <;>
      simp [naturalValues,naturalPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,naturals,hz _ hi]
  · rcases Finset.mem_Icc.mp hi with ⟨hlo,hhi⟩
    interval_cases i <;>
      simp [naturalValues,naturalPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,naturals]

theorem naturals_width (grid B : ℕ) (hg : grid.bits.length≤B) :
    ∀i∈RootFrequency.ids,(naturals grid i).bits.length≤B := by
  intro i _
  unfold naturals
  split_ifs
  · exact hg
  · exact Nat.zero_le _

theorem rational_executes (v : ℕ→Parts) (W I : ℕ) (hW : 1≤W) (hI : 1≤I)
    (hw : WidthBank bank W v) (hg : Good bank v) (hscale : (v 9).Width I)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready bank v s) :
    ∃cost t,Executes input tape control.code cost s t ∧
      cost≤12*operationCost (4096*(W+1))+1 ∧ Ready bank (parts (v 9)) t ∧
      Good bank (parts (v 9)) ∧ WidthBank bank I (parts (v 9)) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  have trace : control.WidthTrace bank (4096*(W+1)) v := by
    simpa only [steps,show 2^12=4096 by rfl] using
      control.automatic_widthTrace bank valid v W hw (literals W hW)
  obtain ⟨c,t,e,hc,b,f⟩ := control.executes bank valid v (4096*(W+1)) trace hg
    (admissible v) input tape s hs
  have b' : Ready bank (parts (v 9)) t := b.congr (output v)
  exact ⟨c,t,e,by simpa only [steps] using hc,b',parts_good _ (hg 9 (by decide)),
    parts_width _ I hI hscale,f⟩

theorem natural_executes (n : ℕ→ℕ) (W : ℕ)
    (hw : ∀i∈RootFrequency.ids,(n i).bits.length≤W)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank RootFrequency.ids n s.val)
    (hblank : ∀i,i<5 → RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (NatAssign.code naturalPlan) cost s t ∧ cost≤stageCost W ∧
      NatAssign.Bank RootFrequency.ids (naturals (n 331)) t.val ∧
      (∀i,i<5 → RationalAccumulator.Blank t.val i) ∧
      BinaryPrecision.Frame RootFrequency.changed s.val t.val := by
  obtain ⟨c,t,e,hc,b,z,f⟩ := RootFrequency.stage_executes naturalPlan natural_valid (by decide)
    n W hw (by simp [naturalPlan,NatAssign.Instruction.literalWidth]) input tape s hb hblank
  refine ⟨c,t,e,hc,?_,z,f⟩
  intro i hi
  rw [←natural_output n hz i hi]
  exact b i hi

#print axioms rational_executes
#print axioms natural_executes
end Maxwell.Continuum.RationalDataflow.RootReset
