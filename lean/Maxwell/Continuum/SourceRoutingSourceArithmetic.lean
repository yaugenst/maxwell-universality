import Maxwell.Continuum.SourceRoutingTreeArithmetic
import Maxwell.Continuum.SourceRoutingMetadata

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.SourceArithmetic
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def sourcePorts : Finset ℕ := {709,711,716,717}
def ids : Finset ℕ := Division.ids∪sourcePorts
def work : Finset ℕ := {0,1,2,3}∪ids

theorem ids_lower (i : ℕ) (hi : i∈ids) : 10 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Division.ids_lower i hi
  · simp only [sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega

theorem work_disjoint (i : ℕ) (hi : i∈Workspace.ids) (hlo : 4 ≤ i) : i∉work := by
  have hd:=Division.work_disjoint i hi hlo
  have extra : Disjoint Workspace.ids sourcePorts := by decide
  intro hm
  rcases Finset.mem_union.mp hm with hm|hm
  · exact hd ((show ({0,1,2,3} : Finset ℕ)⊆Division.work by decide) hm)
  · rcases Finset.mem_union.mp hm with hm|hm
    · exact hd (Finset.mem_union_right _ hm)
    · exact Finset.disjoint_left.mp extra hi hm

theorem stage (instructions : List NatAssign.Instruction)
    (hv : ∀a∈instructions,a.Valid ids) (v : ℕ→ℕ) (B : ℕ)
    (hw : ∀i∈ids,(v i).bits.length ≤ B) (hl : ∀a∈instructions,a.literalWidth ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hc : PrivateVisit.Clean s) :
    ∃steps t,Executes input tape (NatAssign.code instructions) steps s t ∧
      steps ≤ 3000*8^instructions.length*(B+2)^2 ∧
      NatAssign.Bank ids (NatAssign.values instructions v) t.val ∧ PrivateVisit.Clean t ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hcost,bt,zt,ft⟩:=NatAssign.executes ids
    (fun i hi => by have hh:=ids_lower i hi;omega) instructions hv v input tape s hs (Workspace.scratch hc)
  have subset : NatAssign.changes instructions⊆work := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · obtain ⟨a,ha,heq⟩:=List.mem_map.mp (List.mem_toFinset.mp hi)
      have ht : a.target∈ids := by
        have hh:=hv a ha
        cases a <;> simp only [NatAssign.Instruction.Valid,NatAssign.Instruction.target] at hh ⊢
        · exact hh
        · exact hh.2.1
        · exact hh.2.1
        · exact hh.2.1
      exact Finset.mem_union_right _ (heq ▸ ht)
  have frame:=ft.mono subset
  exact ⟨steps,t,he,hcost.trans (NatAssign.price_bound ids instructions hv v B hw hl),bt,
    Workspace.of_frame hc zt frame work_disjoint,frame⟩

def seed (n w forward backward i : ℕ) : ℕ :=
  if i=709 then n else if i=711 then w else if i=716 then forward else if i=717 then backward else 0

theorem seed_bank {n : ℕ} (l : Layout n) (s : Store) (hm : Metadata l s.val)
    (hz : ∀i∈Division.ids,RationalAccumulator.Blank s.val i) :
    NatAssign.Bank ids (seed n n.bits.length l.forward l.backward) s.val := by
  intro i hi
  by_cases a : i=709
  · subst i;simpa only [seed,ite_true] using hm.count
  by_cases b : i=711
  · subst i;simpa only [seed,show ¬(711 : ℕ)=709 by decide,ite_false,ite_true] using hm.width
  by_cases c : i=716
  · subst i;simpa only [seed,show ¬(716 : ℕ)=709 by decide,show ¬(716 : ℕ)=711 by decide,ite_false,ite_true] using hm.forward
  by_cases d : i=717
  · subst i;simpa only [seed,show ¬(717 : ℕ)=709 by decide,show ¬(717 : ℕ)=711 by decide,
      show ¬(717 : ℕ)=716 by decide,ite_false,ite_true] using hm.backward
  have member : i∈Division.ids := by
    rcases Finset.mem_union.mp hi with hi|hi
    · exact hi
    · simp only [sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  simpa [seed,a,b,c,d] using
    (RationalAccumulator.zero_word_iff_blank s.val i).mpr (hz i member)

#print axioms stage
#print axioms seed_bank
end Maxwell.Cost.RoutingPorts.Complete.Tree.SourceArithmetic
