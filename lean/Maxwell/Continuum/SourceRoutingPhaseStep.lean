import Maxwell.Continuum.SourceRoutingPhaseCleanup

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def stepWork : Finset ℕ := {37}∪GeometryArithmetic.work
def stepCode : Code := .seq readCode (.seq code (.seq storeCode (NatAssign.code cleanup)))
def stepCost {q : ℕ} (p : Plan q) : ℕ := 2^112*(p.bound+3)^2

theorem step_executes {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q)
    (colors : RowColoring target) (i : Fin (q*q)) (saved : Fin 5→Vector (List Bool) (q*q))
    (forward : saved 0=IncidenceEncoding.words p.width (targets target))
    (colorArray : saved 1=IncidenceEncoding.words p.width (labels colors))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (seed p i.val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (stored : GeometryArrays.Stored s.val.memory p.base p.width saved) :
    ∃steps t,Executes input tape stepCode steps s t ∧ steps ≤ stepCost p ∧
      NatAssign.Bank GeometryArithmetic.ids (seed p (i.val+1)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧
      GeometryArrays.Stored t.val.memory p.base p.width (updateArrays colors p.width saved i) ∧
      ArchiveFrame stepWork s.val t.val ∧ MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,m0,f0⟩:=read_inputs p colors i saved forward colorArray
    input tape s bank ready privateBlank metadata stored
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,f1⟩:=executes (beforeArithmetic p colors i)
    (before_zero p colors i) (before_positive p colors i) p.bound (before_width p colors i)
    input tape a ba za a1249
  have mb:=ma.frame (ArchiveFrame.of_binary f1) (by decide)
  have sb : GeometryArrays.Stored b.val.memory p.base p.width saved := by rw [f1.memory,m0];exact stored
  obtain ⟨c2,c,e2,h2,bc,zc,c1249,mc,sc,f2,m2⟩:=store_all p colors i saved
    (output (beforeArithmetic p colors i)) (output_writes p colors i) input tape b bb zb b1249 mb sb
  obtain ⟨c3,t,e3,h3,bt,zt,t1249,f3⟩:=cleanup_executes p colors i input tape c bc zc c1249
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bt,zt,t1249,
    mc.frame (ArchiveFrame.of_binary f3) (by decide),?_,?_,?_⟩
  · have h1' := h1.trans (Nat.mul_le_mul_left (2^110)
      (Nat.pow_le_pow_left (show p.bound+2 ≤ p.bound+3 by omega) 2))
    dsimp only [stepCost]
    omega
  · rw [f3.memory];exact sc
  · exact (f0.mono (by decide)).trans
      (((ArchiveFrame.of_binary f1).mono Finset.subset_union_right).trans
        ((f2.mono Finset.subset_union_left).trans
          ((ArchiveFrame.of_binary f3).mono Finset.subset_union_right)))
  · exact (MemoryFrame.of_eq p m0).trans
      ((MemoryFrame.of_eq p f1.memory).trans (m2.trans (MemoryFrame.of_eq p f3.memory)))

#print axioms step_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
