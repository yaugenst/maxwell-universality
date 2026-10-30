import Maxwell.Continuum.SourceRoutingGeometryArithmetic

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArray
open RationalAccumulator (Blank)

theorem Ready.of_tapes {s t : BitRAMState} (ready : Ready s)
    (keep : ∀j,j<40→t.tapes j=s.tapes j) : Ready t := by
  have blank (j : ℕ) (hj : j<40) (h : Blank s j) : Blank t j :=
    RationalAccumulator.blank_of_eq (keep j hj) h
  rcases ready with ⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,h37⟩
  exact ⟨⟨blank 0 (by decide) h0,blank 1 (by decide) h1,blank 2 (by decide) h2,
    blank 3 (by decide) h3,blank 5 (by decide) h5,blank 6 (by decide) h6,
    blank 8 (by decide) h8,blank 9 (by decide) h9⟩,
    blank 7 (by decide) h7,blank 37 (by decide) h37⟩
end Maxwell.Cost.RoutingPorts.Complete.GeometryArray

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def loadCode (source target : ℕ) : Code :=
  .seq (.call (TapeOps.clear target)) (.call (WordTransfer.clone source target))

theorem load_executes (source target : ℕ) (targetControl : target∈controls) (different : source≠target)
    (v : ℕ→ℕ) (value : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (word : Word s.val source value) :
    ∃steps t,Executes input tape (loadCode source target) steps s t ∧
      steps ≤ 6*(v target).bits.length+15*value.bits.length+21 ∧
      NatAssign.Bank ids (Function.update v target value) t.val ∧ GeometryArray.Ready t.val ∧
      Blank t.val 1249 ∧ BinaryPrecision.Frame {target} s.val t.val := by
  have targetBounds:=Finset.mem_Icc.mp targetControl
  obtain ⟨origin,ho⟩:=bank target (Finset.mem_union_left _ targetControl)
  obtain ⟨co,hco⟩:=word
  obtain ⟨a,ea,atapes,af⟩:=WordCall.clear target input tape (v target).bits origin s ho
  have sourceA : a.val.tapes source=BitTape.shifted value.bits co := by simpa [atapes,different] using hco
  have blankA : a.val.tapes target={BitTape.blank with head:=origin+(v target).bits.length} := by simp [atapes]
  obtain ⟨t,et,ttapes,tf⟩:=WordCall.clone source target different input tape value.bits co
    (origin+(v target).bits.length) a sourceA blankA
  have keep (j : ℕ) (hj : j≠target) : t.val.tapes j=s.val.tapes j := by simp [ttapes,atapes,hj]
  refine ⟨_,t,ea.seq et,by omega,?_,ready.of_tapes (fun j hj => keep j (by omega)),
    RationalAccumulator.blank_of_eq (keep 1249 (by omega)) privateBlank,
    ⟨tf.1.trans af.1,tf.2.1.trans af.2.1,tf.2.2.1.trans af.2.2.1,
      tf.2.2.2.1.trans af.2.2.2.1,tf.2.2.2.2.1.trans af.2.2.2.2.1,
      fun j hj => keep j (by simpa only [Finset.mem_singleton] using hj)⟩⟩
  intro j hj
  by_cases same : j=target
  · subst j
    rw [Function.update_self]
    exact ⟨origin+(v target).bits.length,by simp [ttapes]⟩
  · rw [Function.update_of_ne same]
    exact RationalAccumulator.word_of_eq (keep j same) (bank j hj)

#print axioms load_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
