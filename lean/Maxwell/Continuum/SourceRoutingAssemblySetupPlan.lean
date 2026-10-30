import Maxwell.Continuum.SourceRoutingTreeWorkspace
import Maxwell.Cost.ChildPermutation.Prepare
import Maxwell.Cost.ColorAssemble.Complexity

/-! Six runtime control words describe a label-assembly node. All local
metadata are loaded by one fixed instruction list and an actual clock copy. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def controls : Finset ℕ := Finset.Icc 800 805
def ids : Finset ℕ := controls∪NodeCleanup.banks.toFinset
def initial (q : ℕ→ℕ) (i : ℕ) : ℕ := if i∈controls then q i else 0
def layout (q : ℕ→ℕ) : ChildPermutation.Layout :=
  ⟨q 802,q 800,q 805,q 803,0,q 804,0⟩
def setup : List NatAssign.Instruction :=
  [.copy 802 80,.copy 800 100,.copy 803 122,.copy 804 124,.copy 805 85,.literal 86 1,.copy 801 96]
def setupValues (q : ℕ→ℕ) : ℕ→ℕ := Function.update (NatAssign.values setup (initial q)) 83 (q 801)
def setupCode : Code := .seq (NatAssign.code setup) (.call (WordTransfer.clone 801 83))
def setupWork : Finset ℕ := NatAssign.changes setup∪{83}
def live : List ℕ := [80,81,83,85,86,87,96,100,120,121,122,123,124,125,126,127,128]

theorem setup_valid : ∀a∈setup,a.Valid ids := by
  simp [setup,NatAssign.Instruction.Valid,ids,controls,NodeCleanup.banks]

theorem initial_bank (q : ℕ→ℕ) (s : BitRAMState) (hc : NodeVisit.Clean s)
    (hi : ∀i∈controls,RationalAccumulator.Word s i (q i)) :
    NatAssign.Bank ids (initial q) s := by
  intro i hids
  by_cases hin : i∈controls
  · simpa [initial,hin] using hi i hin
  · have hid : i∈NodeCleanup.banks := List.mem_toFinset.mp ((Finset.mem_union.mp hids).resolve_left hin)
    simpa [initial,hin] using (RationalAccumulator.zero_word_iff_blank s i).mpr (hc.2 i hid)

theorem setup_unwritten (q : ℕ→ℕ) (i : ℕ) (hi : i∈NodeCleanup.banks) (hl : i∉live) : setupValues q i=0 := by
  have hc : i∉controls := by
    simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [controls,Finset.mem_Icc];omega
  simp only [live,List.mem_cons,List.not_mem_nil,or_false,not_or] at hl
  rcases hl with ⟨h0,_,h2,h3,h4,_,h6,h7,_,_,h10,_,h12,_,_,_,_⟩
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    initial,Function.update,h0,h2,h3,h4,h6,h7,h10,h12,hc]

theorem setup_before (q : ℕ→ℕ) (s : BitRAMState) (hb : NatAssign.Bank ids (setupValues q) s) :
    ChildPermutation.Before (layout q) (q 801).bits s := by
  have word (i : ℕ) (hi : i∈ids) := hb i hi
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact word 80 (by decide)
  · exact word 81 (by decide)
  · exact word 83 (by decide)
  · exact word 85 (by decide)
  · have h : RationalAccumulator.Word s 86 1 := word 86 (by decide)
    simpa only [RationalAccumulator.Word,BankArray.Word,show (1 : ℕ).bits=[true] by decide] using h
  · exact word 100 (by decide)
  · intro i
    fin_cases i
    · exact word 122 (by decide)
    · exact word 123 (by decide)
    · exact word 124 (by decide)
    · exact word 125 (by decide)

#print axioms setup_before
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
