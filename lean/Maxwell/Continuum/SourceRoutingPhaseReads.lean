import Maxwell.Continuum.SourceRoutingPhaseLayout

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def afterLabels {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (i : Fin (q*q)) : ℕ→ℕ := Function.update (seed p i.val) 1202 ((labels colors).get i)
def beforeArithmetic {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (i : Fin (q*q)) : ℕ→ℕ := Function.update (afterLabels p colors i) 1203 ((targets target).get i)

theorem label_value {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (i : Fin (q*q)) :
    (labels colors).get i=q*(colors.color (port i)).val := SortArrays.get_ofFn _ _
theorem target_value {q : ℕ} (target : Equiv.Perm (Port q)) (i : Fin (q*q)) :
    (targets target).get i=(finProdFinEquiv (target (port i))).val := SortArrays.get_ofFn _ _
theorem label_fit {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target) (i : Fin (q*q)) :
    ((labels colors).get i).bits.length ≤ p.width := by
  apply Maxwell.Continuum.RationalWords.bits_mono
  rw [label_value]
  exact Nat.mul_le_mul_left q (colors.color (port i)).isLt.le
theorem target_fit {q : ℕ} (p : Plan q) (target : Equiv.Perm (Port q)) (i : Fin (q*q)) :
    ((targets target).get i).bits.length ≤ p.width := by rw [target_value];exact p.index_fit _

def readCode : Code := .seq (BankArray.readCanonicalCode 711 1201 1215 718 1202)
  (BankArray.readCanonicalCode 711 1201 716 718 1203)

theorem read_inputs {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (i : Fin (q*q)) (saved : Fin 5→Vector (List Bool) (q*q))
    (forward : saved 0=IncidenceEncoding.words p.width (targets target))
    (colorArray : saved 1=IncidenceEncoding.words p.width (labels colors))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (seed p i.val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (stored : GeometryArrays.Stored s.val.memory p.base p.width saved) :
    ∃steps t,Executes input tape readCode steps s t ∧ steps ≤ 2^22*(p.bound+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (beforeArithmetic p colors i) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧ t.val.memory=s.val.memory ∧
      ArchiveFrame {1202,1203} s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,f0⟩:=GeometryArithmetic.read
    711 1201 1215 718 1202 (by decide) (by decide) (by decide) (by decide) (by decide)
    p.width (p.base 1) p.bound p.clock (labels colors) i p.width_positive p.clock_length
    (label_fit p colors i) p.width_bound ((p.index_fit i).trans p.width_bound) (p.base_bound 1)
    input tape (seed p i.val) s bank ready privateBlank rfl metadata.width (bank 1201 (by decide))
    (bank 1215 (by decide)) metadata.clock (by simpa only [colorArray] using stored 1)
  have metaA:=metadata.frame f0 (by decide)
  obtain ⟨c1,t,e1,h1,bt,zt,t1249,mt,f1⟩:=GeometryArithmetic.read
    711 1201 716 718 1203 (by decide) (by decide) (by decide) (by decide) (by decide)
    p.width (p.base 0) p.bound p.clock (targets target) i p.width_positive p.clock_length
    (target_fit p target i) p.width_bound ((p.index_fit i).trans p.width_bound) (p.base_bound 0)
    input tape (afterLabels p colors i) a ba za a1249 rfl metaA.width (ba 1201 (by decide))
    metaA.forward metaA.clock (by simpa only [ma,forward] using stored 0)
  exact ⟨c0+c1,t,e0.seq e1,by omega,bt,zt,t1249,metaA.frame f1 (by decide),mt.trans ma,
    (f0.mono (by decide)).trans (f1.mono (by decide))⟩

#print axioms read_inputs
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
