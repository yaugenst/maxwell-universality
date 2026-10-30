import Maxwell.Continuum.SourceRoutingHistoryAdvance

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

structure Runtime {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (k : ℕ) (s : Store) : Prop where
  bound : k ≤ 2*q
  bank : NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.layer k) (k+1) 0) s.val
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  counterBlank : Blank s.val 1240
  count : Word s.val 709 (q*q)
  metadata : GeometrySort.Metadata (p.layer k) s.val
  stored : Stored p initial k s.val.memory

def stepCode : Code := .seq GeometrySort.generateCode (NatAssign.code advance)
def stepWork : Finset ℕ := GeometrySort.loopWork
def stepCost {q : ℕ} (p : Plan q) : ℕ := 2^206*(q*q+1)*(p.bound+3)^2

theorem Runtime.step {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} (fit : GeometrySort.Fits p.width initial)
    (i : Fin (2*q)) (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : Runtime p initial i.val s) :
    ∃steps t,Executes input tape stepCode steps s t ∧ steps ≤ stepCost p ∧
      Runtime p initial (i.val+1) t ∧ ArchiveFrame stepWork s.val t.val ∧
      MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,a1240,_,da,f0,m0⟩:=GeometrySort.generate_keys
    (p.layer i.val) (i.val+1) (SortArrays.run initial i.val) (run_fits p initial fit i.val)
    input tape s state.bank state.ready state.privateBlank state.metadata
    (state.stored i.val le_rfl) state.count state.counterBlank
  obtain ⟨c1,t,e1,h1,bt,zt,t1249,f1⟩:=advance_executes p i.val i.isLt.le input tape a ba za a1249
  have aCount : Word a.val 709 (q*q) :=
    RationalAccumulator.word_of_eq (f0.tapes 709 (by decide) (by decide)) state.count
  have mt:=ma.frame (ArchiveFrame.of_binary f1) (by decide)
  have storage : Stored p initial (i.val+1) a.val.memory := state.stored.next (by
    simpa only [run_succ,Plan.layer,GeometrySort.Plan.width,Plan.width] using da) m0
  refine ⟨c0+c1,t,e0.seq e1,?_,⟨i.isLt,bt,zt,t1249,
    RationalAccumulator.blank_of_eq (f1.tapes 1240 (by decide)) a1240,
    RationalAccumulator.word_of_eq (f1.tapes 709 (by decide)) aCount,⟨mt.width,mt.clock⟩,?_⟩,
    f0.trans ((ArchiveFrame.of_binary f1).mono (by
      intro j hj
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hj))),?_⟩
  · have base:=(GeometrySort.generateCost_polynomial (p.layer i.val) (i.val+1)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (p.layer_bound i.val i.isLt.le) 3) 2))
    have one : (p.bound+3)^2 ≤ (q*q+1)*(p.bound+3)^2 := Nat.le_mul_of_pos_left _ (by omega)
    dsimp only [stepCost]
    nlinarith only [h0,h1,base,one]
  · rw [f1.memory];exact storage
  · rw [f1.memory];exact layer_frame p i.isLt m0

theorem Runtime.counter_frame {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {k : ℕ} {s t : Store}
    (state : Runtime p initial k s) (memory : t.val.memory=s.val.memory)
    (keep : ∀j,j≠1241→t.val.tapes j=s.val.tapes j) : Runtime p initial k t := by
  have word (j : ℕ) (hj : j≠1241) (n : ℕ) (h : Word s.val j n) : Word t.val j n :=
    RationalAccumulator.word_of_eq (keep j hj) h
  have blank (j : ℕ) (hj : j≠1241) (h : Blank s.val j) : Blank t.val j :=
    RationalAccumulator.blank_of_eq (keep j hj) h
  refine ⟨state.bound,?_,?_,blank 1249 (by decide) state.privateBlank,
    blank 1240 (by decide) state.counterBlank,word 709 (by decide) _ state.count,?_,?_⟩
  · intro j hj
    apply word j _ _ (state.bank j hj)
    simp only [GeometryArithmetic.ids,GeometryArithmetic.controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  · rcases state.ready with ⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,h37⟩
    exact ⟨⟨blank 0 (by decide) h0,blank 1 (by decide) h1,blank 2 (by decide) h2,
      blank 3 (by decide) h3,blank 5 (by decide) h5,blank 6 (by decide) h6,
      blank 8 (by decide) h8,blank 9 (by decide) h9⟩,
      blank 7 (by decide) h7,blank 37 (by decide) h37⟩
  · exact ⟨word 711 (by decide) _ state.metadata.width,
      BankArray.word_of_eq (keep 718 (by decide)) state.metadata.clock⟩
  · rw [memory];exact state.stored

theorem Runtime.counted {q : ℕ} {p : Plan q} {initial : SortArrays.Keys q} {k : ℕ} {s t : Store}
    (state : Runtime p initial k s) (frame : CountedShifted.Frame 1241 s t) : Runtime p initial k t :=
  state.counter_frame frame.2.2.1 frame.2.2.2.2.2.1

#print axioms Runtime.step
#print axioms Runtime.counted
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
