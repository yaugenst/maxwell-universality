import Maxwell.Continuum.SourceRoutingPortIndices
import Maxwell.Continuum.NaturalBankDivMod
import Maxwell.Continuum.NatAssignOutputWidth

/-! The fixed natural arithmetic instruction stream for the two incidence
port addresses. Division is an executed bit routine. -/

namespace Maxwell.Cost.RoutingPorts.Complete.PortArithmetic
open Structured Maxwell.Continuum.RationalDataflow
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def ports : Finset ℕ := {710,730,731,733,734,735,736,737} ∪ Finset.Icc 760 768
def ids : Finset ℕ := NaturalQuotient.workPorts ∪ ports
def prepare : List NatAssign.Instruction := [.literal 736 2,.copy 710 737,.add 710 737]
def finish : List NatAssign.Instruction :=
  [.copy 760 730,.multiply 736 730,.add 763 730,.multiply 737 730,
    .copy 761 768,.multiply 736 768,.add 762 768,.add 768 730,
    .copy 766 731,.multiply 736 731,.add 765 731,.multiply 737 731,.add 767 731]
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values prepare v
def divided (v : ℕ→ℕ) (source divisor q r : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v q (v source/v divisor)) r (v source%v divisor)
def v1 (v : ℕ→ℕ) : ℕ→ℕ := divided (prepared v) 734 710 760 761
def v2 (v : ℕ→ℕ) : ℕ→ℕ := divided (v1 v) 735 736 762 763
def v3 (v : ℕ→ℕ) : ℕ→ℕ := divided (v2 v) 733 736 764 765
def v4 (v : ℕ→ℕ) : ℕ→ℕ := divided (v3 v) 764 737 766 767
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (v4 v)
def code : Code := .seq (NatAssign.code prepare)
  (.seq (NaturalDivMod.code 734 710 760 761)
    (.seq (NaturalDivMod.code 735 736 762 763)
      (.seq (NaturalDivMod.code 733 736 764 765)
        (.seq (NaturalDivMod.code 764 737 766 767) (NatAssign.code finish)))))

theorem ids_lower (i : ℕ) (hi : i∈ids) : 10 ≤ i := by
  simp only [ids,ports,NaturalQuotient.workPorts,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega
theorem prepare_valid : ∀a∈prepare,a.Valid ids := by
  simp [prepare,NatAssign.Instruction.Valid,ids,ports]
theorem finish_valid : ∀a∈finish,a.Valid ids := by
  simp [finish,NatAssign.Instruction.Valid,ids,ports]

theorem source_value (v : ℕ→ℕ) : output v 730=PortIndices.sourceIndex (v 710) (v 734) (v 735) := by
  simp [output,finish,v4,v3,v2,v1,divided,prepared,prepare,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    PortIndices.sourceIndex]
  ring
theorem target_value (v : ℕ→ℕ) : output v 731=PortIndices.targetIndex (v 710) (v 733) := by
  simp [output,finish,v4,v3,v2,v1,divided,prepared,prepare,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    PortIndices.targetIndex,show ∀n : ℕ,n+n=2*n by omega]
  ring

theorem divided_width (v : ℕ→ℕ) (source divisor q r B : ℕ)
    (hsource : source∈ids) (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(divided v source divisor q r i).bits.length≤B := by
  intro i hi
  by_cases hr : i=r
  · subst i
    simp only [divided,Function.update_self]
    exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le _ _)).trans (hw source hsource)
  · by_cases hq : i=q
    · subst i
      simp only [divided,Function.update_of_ne hr,Function.update_self]
      exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self _ _)).trans (hw source hsource)
    · simpa only [divided,Function.update_of_ne hr,Function.update_of_ne hq] using hw i hi

theorem divided_zero (v : ℕ→ℕ) (source divisor q r : ℕ) (hq : 700 ≤ q) (hr : 700 ≤ r)
    (hz : ∀i∈NaturalQuotient.workPorts,v i=0) :
    ∀i∈NaturalQuotient.workPorts,divided v source divisor q r i=0 := by
  intro i hi
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  simpa only [divided,Function.update_of_ne (show i≠r by omega),
    Function.update_of_ne (show i≠q by omega)] using hz i hi

theorem prepared_zero (v : ℕ→ℕ) (hz : ∀i∈NaturalQuotient.workPorts,v i=0) :
    ∀i∈NaturalQuotient.workPorts,prepared v i=0 := by
  intro i hi
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  simpa [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,show i≠736 by omega,show i≠737 by omega] using hz i hi

theorem prepared_width (v : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(prepared v i).bits.length≤8*(B+1) := by
  have hh := NatAssign.values_width_bound ids prepare prepare_valid v B hw (by
    simp [prepare,NatAssign.Instruction.literalWidth,show (2 : ℕ).bits.length=2 by decide]
    exact hB)
  intro i hi
  exact (Nat.le_succ _).trans (hh i hi)

theorem output_width (v : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hw : ∀i∈ids,(v i).bits.length≤B) :
    ∀i∈ids,(output v i).bits.length≤2^17*(B+2) := by
  have h0 := prepared_width v B hB hw
  have h1 := divided_width (prepared v) 734 710 760 761 _ (by decide) h0
  have h2 := divided_width (v1 v) 735 736 762 763 _ (by decide) h1
  have h3 := divided_width (v2 v) 733 736 764 765 _ (by decide) h2
  have h4 := divided_width (v3 v) 764 737 766 767 _ (by decide) h3
  have hf := NatAssign.values_width_bound ids finish finish_valid (v4 v) (8*(B+1)) h4
    (by simp [finish,NatAssign.Instruction.literalWidth])
  intro i hi
  have h := hf i hi
  change (output v i).bits.length+1≤2^13*(8*(B+1)+1) at h
  omega

#print axioms source_value
#print axioms target_value
#print axioms output_width

end Maxwell.Cost.RoutingPorts.Complete.PortArithmetic
