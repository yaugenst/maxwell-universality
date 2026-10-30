import Maxwell.Continuum.SourceRoutingHistoryLoop

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing GeometryArithmetic
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def counterPrepare : List NatAssign.Instruction := [.copy 1200 1230,.multiply 1220 1230]
def counterCleanup : List NatAssign.Instruction := [.literal 1230 0]
def counterCode : Code := .seq (NatAssign.code counterPrepare)
  (.seq (.call (WordTransfer.clone 1230 1241)) (NatAssign.code counterCleanup))

theorem counter_values {q : ℕ} (p : Plan q) :
    NatAssign.values counterPrepare (GeometrySort.seed (p.layer 0) 1 0)=
      Function.update (GeometrySort.seed (p.layer 0) 1 0) 1230 (2*q) := by
  funext j
  simp [counterPrepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,GeometrySort.seed]

theorem counter_cleanup_values {q : ℕ} (p : Plan q) :
    NatAssign.values counterCleanup (Function.update (GeometrySort.seed (p.layer 0) 1 0) 1230 (2*q))=
      GeometrySort.seed (p.layer 0) 1 0 := by
  funext j
  by_cases same : j=1230
  · subst j;simp [counterCleanup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,GeometrySort.seed]
  · simp [counterCleanup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,same]

theorem counter_executes {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : Runtime p initial 0 s)
    (blank : Blank s.val 1241) :
    ∃steps t,Executes input tape counterCode steps s t ∧ steps ≤ 2^50*(p.bound+3)^2 ∧
      Runtime p initial 0 t ∧ Word t.val 1241 (2*q) ∧
      ArchiveFrame loopWork s.val t.val ∧ t.val.memory=s.val.memory := by
  have seedWidth (j : ℕ) (hj : j∈GeometryArithmetic.ids) :
      (GeometrySort.seed (p.layer 0) 1 0 j).bits.length ≤ p.bound :=
    (GeometrySort.seed_width (p.layer 0) 1 0 (Nat.zero_le _) j hj).trans (p.layer_bound 0 (Nat.zero_le _))
  have countWidth : (2*q).bits.length ≤ p.bound := by
    have h:=Maxwell.Continuum.RationalWords.bits_mono (Nat.le_succ (2*q))
    change (2*q).bits.length ≤ (2*q+1).bits.length at h
    dsimp only [Plan.bound];omega
  let values:=Function.update (GeometrySort.seed (p.layer 0) 1 0) 1230 (2*q)
  have valuesWidth (j : ℕ) (hj : j∈GeometryArithmetic.ids) : (values j).bits.length ≤ p.bound := by
    dsimp only [values]
    by_cases h : j=1230
    · simpa only [h,Function.update_self] using countWidth
    · simpa only [Function.update_of_ne h] using seedWidth j hj
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩:=stage counterPrepare
    (by simp [counterPrepare,NatAssign.Instruction.Valid,GeometryArithmetic.ids,GeometryArithmetic.controls])
    (GeometrySort.seed (p.layer 0) 1 0) p.bound seedWidth
    (by simp [counterPrepare,NatAssign.Instruction.literalWidth]) input tape s state.bank state.ready
  have ba' : NatAssign.Bank GeometryArithmetic.ids values a.val := by simpa only [counter_values] using ba
  have valueWord : Word a.val 1230 (2*q) := by simpa only [values,Function.update_self] using ba' 1230 (by decide)
  have aBlank : Blank a.val 1241 := RationalAccumulator.blank_of_eq (f0.tapes 1241 (by decide)) blank
  obtain ⟨co,hco⟩:=valueWord
  obtain ⟨origin,ho⟩:=aBlank
  obtain ⟨b,eb,btapes,fb⟩:=WordCall.clone 1230 1241 (by decide) input tape (2*q).bits co origin a hco ho
  have keepb (j : ℕ) (hj : j≠1241) : b.val.tapes j=a.val.tapes j := by simp [btapes,hj]
  have bankb : NatAssign.Bank GeometryArithmetic.ids values b.val := by
    intro j hj
    apply RationalAccumulator.word_of_eq (keepb j _) (ba' j hj)
    simp only [GeometryArithmetic.ids,GeometryArithmetic.controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  have frameb : BinaryPrecision.Frame ({1241} : Finset ℕ) a.val b.val :=
    ⟨fb.1,fb.2.1,fb.2.2.1,fb.2.2.2.1,fb.2.2.2.2.1,fun j hj => keepb j (by simpa using hj)⟩
  have readyb : GeometryArray.Ready b.val := by
    rcases za with ⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,h37⟩
    have keep (j : ℕ) (hj : j≠1241) (h : Blank a.val j) : Blank b.val j :=
      RationalAccumulator.blank_of_eq (keepb j hj) h
    exact ⟨⟨keep 0 (by decide) h0,keep 1 (by decide) h1,keep 2 (by decide) h2,
      keep 3 (by decide) h3,keep 5 (by decide) h5,keep 6 (by decide) h6,
      keep 8 (by decide) h8,keep 9 (by decide) h9⟩,
      keep 7 (by decide) h7,keep 37 (by decide) h37⟩
  obtain ⟨c1,t,e1,h1,bt,zt,f1⟩:=stage counterCleanup
    (by simp [counterCleanup,NatAssign.Instruction.Valid,GeometryArithmetic.ids,GeometryArithmetic.controls])
    values p.bound valuesWidth (by simp [counterCleanup,NatAssign.Instruction.literalWidth])
    input tape b bankb readyb
  have smallWork : ({0,1,2,3}∪GeometryArithmetic.ids : Finset ℕ)⊆loopWork := by
    intro j hj
    simp only [loopWork,stepWork,GeometrySort.loopWork,GeometrySort.stepWork,GeometryArithmetic.work,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto
  have frame : ArchiveFrame loopWork s.val t.val :=
    ((ArchiveFrame.of_binary f0).mono smallWork).trans
      (((ArchiveFrame.of_binary frameb).mono Finset.subset_union_left).trans
        ((ArchiveFrame.of_binary f1).mono smallWork))
  have memory : t.val.memory=s.val.memory := f1.memory.trans (fb.2.2.1.trans f0.memory)
  refine ⟨_,t,e0.seq (eb.seq e1),?_,⟨state.bound,?_,zt,
    RationalAccumulator.blank_of_eq (f1.tapes 1249 (by decide))
      (RationalAccumulator.blank_of_eq (keepb 1249 (by decide))
        (RationalAccumulator.blank_of_eq (f0.tapes 1249 (by decide)) state.privateBlank)),
    RationalAccumulator.blank_of_eq (f1.tapes 1240 (by decide))
      (RationalAccumulator.blank_of_eq (keepb 1240 (by decide))
        (RationalAccumulator.blank_of_eq (f0.tapes 1240 (by decide)) state.counterBlank)),
    RationalAccumulator.word_of_eq (frame.tapes 709 (by decide) (by decide)) state.count,
    state.metadata.frame frame (by decide),by rw [memory];exact state.stored⟩,
    ⟨origin,(f1.tapes 1241 (by decide)).trans (by simp [btapes])⟩,frame,memory⟩
  · change c0 ≤ 3000*8^2*(p.bound+2)^2 at h0
    change c1 ≤ 3000*8^1*(p.bound+2)^2 at h1
    nlinarith
  · simpa only [values,counter_cleanup_values] using bt

#print axioms counter_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
