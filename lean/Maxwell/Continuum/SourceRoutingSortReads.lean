import Maxwell.Continuum.SourceRoutingSortLayout

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def readCode : Code := .seq (BankArray.readCanonicalCode 711 1201 1215 718 1208)
  (BankArray.readCanonicalCode 711 1210 1215 718 1209)

theorem read_inputs {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (fit : Fits p.width saved)
    (i : Fin (q*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (intermediate p round i) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (stored : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved)) :
    ∃steps t,Executes input tape readCode steps s t ∧ steps ≤ 2^22*(p.bound round+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (beforeSelect p round saved i) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧
      t.val.memory=s.val.memory ∧ ArchiveFrame {1208,1209} s.val t.val := by
  have sourceWidth : p.source.bits.length ≤ p.bound round := by dsimp only [Plan.bound];omega
  have cursor : intermediate p round i 1201=i.val := intermediate_other p round i 1201 (by decide)
  have base : intermediate p round i 1215=p.source := intermediate_other p round i 1215 (by decide)
  have index : intermediate p round i 1210=(neighbor round i).val :=
    congrArg Prod.fst (partner_neighbor i (seed_setup p round i.val))
  have blankSelf : intermediate p round i 1208=0 := intermediate_other p round i 1208 (by decide)
  have blankNeighbor : afterSelf p round saved i 1209=0 := intermediate_other p round i 1209 (by decide)
  obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,f0⟩:=GeometryArithmetic.read
    711 1201 1215 718 1208 (by decide) (by decide) (by decide) (by decide) (by decide)
    p.width p.source (p.bound round) p.clock saved i p.width_positive p.clock_length (fit i)
    (p.width_bound round) ((p.index_fit i).trans (p.width_bound round)) sourceWidth
    input tape (intermediate p round i) s bank ready privateBlank blankSelf metadata.width
    (by simpa only [cursor] using bank 1201 (by decide))
    (by simpa only [base] using bank 1215 (by decide)) metadata.clock stored
  have metaA:=metadata.frame f0 (by decide)
  obtain ⟨c1,t,e1,h1,bt,zt,t1249,mt,f1⟩:=GeometryArithmetic.read
    711 1210 1215 718 1209 (by decide) (by decide) (by decide) (by decide) (by decide)
    p.width p.source (p.bound round) p.clock saved (neighbor round i) p.width_positive p.clock_length (fit _)
    (p.width_bound round) ((p.index_fit _).trans (p.width_bound round)) sourceWidth
    input tape (afterSelf p round saved i) a ba za a1249 blankNeighbor metaA.width
    (by simpa only [Function.update_of_ne (by decide : (1210 : ℕ)≠1208),index] using ba 1210 (by decide))
    (by simpa only [Function.update_of_ne (by decide : (1215 : ℕ)≠1208),base] using ba 1215 (by decide))
    metaA.clock (by rw [ma];exact stored)
  exact ⟨c0+c1,t,e0.seq e1,by omega,bt,zt,t1249,metaA.frame f1 (by decide),mt.trans ma,
    (f0.mono (by decide)).trans (f1.mono (by decide))⟩

theorem beforeSelect_width {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(beforeSelect p round saved i j).bits.length ≤ 2^20*(p.bound round+1) := by
  have bound : p.width ≤ 2^20*(p.bound round+1) := (p.width_bound round).trans (by omega)
  intro j hj
  by_cases h9 : j=1209
  · subst j;simpa only [beforeSelect,Function.update_self] using (fit (neighbor round i)).trans bound
  · by_cases h8 : j=1208
    · subst j;simpa only [beforeSelect,afterSelf,Function.update_of_ne h9,Function.update_self] using (fit i).trans bound
    · simpa only [beforeSelect,afterSelf,Function.update_of_ne h8,Function.update_of_ne h9] using
        intermediate_width p round i j hj

theorem beforeSelect_zero {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,beforeSelect p round saved i j=0 := by
  have zero:=partnerProgram.evaluate_zero partner_valid (seed p round i.val) (seed_zero p round i.val)
  intro j hj
  have different : j≠1208 ∧ j≠1209 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  simpa only [beforeSelect,afterSelf,intermediate,Function.update_of_ne different.1,
    Function.update_of_ne different.2] using zero j hj

theorem beforeSelect_one {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    beforeSelect p round saved i 1219=1 := intermediate_other p round i 1219 (by decide)

theorem selected_value {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) :
    selectProgram.evaluate (beforeSelect p round saved i) 1212=(SortArrays.step round saved).get i := by
  rw [select_result _ (beforeSelect_one p round saved i),step_value]
  have flag : beforeSelect p round saved i 1211=maximumFlag round (finProdFinEquiv.symm i) :=
    congrArg Prod.snd (partner_neighbor i (seed_setup p round i.val))
  rw [flag]
  rfl

theorem step_fits {q : ℕ} (width : ℕ) (round : ℕ) (saved : SortArrays.Keys q) (fit : Fits width saved) :
    Fits width (SortArrays.step round saved) := by
  intro i
  rw [step_value]
  split_ifs
  · rcases le_total (saved.get i) (saved.get (neighbor round i)) with h|h
    · simpa only [max_eq_right h] using fit (neighbor round i)
    · simpa only [max_eq_left h] using fit i
  · rcases le_total (saved.get i) (saved.get (neighbor round i)) with h|h
    · simpa only [min_eq_left h] using fit i
    · simpa only [min_eq_right h] using fit (neighbor round i)

#print axioms read_inputs
#print axioms selected_value
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
