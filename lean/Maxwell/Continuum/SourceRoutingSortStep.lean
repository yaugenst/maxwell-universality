import Maxwell.Continuum.SourceRoutingSortStore

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2600000

def stepWork : Finset ℕ := {37}∪GeometryArithmetic.work
def stepCode : Code := .seq partnerProgram.code
  (.seq readCode (.seq selectProgram.code (.seq storeCode (NatAssign.code cleanup))))
def stepCost {q : ℕ} (p : Plan q) (round : ℕ) : ℕ := 2^200*(p.bound round+3)^2

theorem select_cost_polynomial (B : ℕ) : controlCost selectProgram.steps (2^20*(B+1)) ≤ 2^172*(B+3)^2 := by
  calc
    _ ≤ controlCost 6 (2^20*(B+1)) := controlCost_steps _ _ _ select_steps
    _ = 2^128*(2^20*(B+1)+2)^2 := rfl
    _ ≤ 2^128*(2^21*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = (2^128*(2^21)^2)*(B+3)^2 := by ring
    _ ≤ 2^172*(B+3)^2 := Nat.mul_le_mul_right _ (by decide)

theorem step_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (old : Vector (List Bool) (q*q))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (seed p round i.val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved))
    (destination : BitArray.Represents s.val.memory p.destination p.width old) :
    ∃steps t,Executes input tape stepCode steps s t ∧ steps ≤ stepCost p round ∧
      NatAssign.Bank GeometryArithmetic.ids (seed p round (i.val+1)) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧
      BitArray.Represents t.val.memory p.source p.width (IncidenceEncoding.words p.width saved) ∧
      BitArray.Represents t.val.memory p.destination p.width
        (old.set i (IncidenceEncoding.word p.width ((SortArrays.step round saved).get i))) ∧
      ArchiveFrame stepWork s.val t.val ∧
      Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=partner_cost (seed_setup p round i.val) p.positive
    (seed_zero p round i.val) (p.bound round) (by dsimp only [Plan.bound];omega)
    (seed_width p round i.val i.isLt.le) input tape s bank ready privateBlank
  have ma:=metadata.frame (ArchiveFrame.of_binary f0) (by decide)
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,mb,m1,f1⟩:=read_inputs p round saved fit i input tape a ba za a1249 ma
    (by rw [f0.memory];exact source)
  obtain ⟨c2,c,e2,h2,bc,zc,c1249,f2⟩:=selectProgram.executes select_valid (beforeSelect p round saved i)
    (beforeSelect_zero p round saved i) (select_admissible _ (beforeSelect_one p round saved i))
    (2^20*(p.bound round+1)) (beforeSelect_width p round saved fit i) (select_literals _)
    input tape b bb zb b1249
  have memoryC : c.val.memory=s.val.memory := f2.memory.trans (m1.trans f0.memory)
  have mc:=mb.frame (ArchiveFrame.of_binary f2) (by decide)
  obtain ⟨c3,d,e3,h3,bd,zd,d1249,md,sd,dd,f3,m3⟩:=store_key p round saved fit i old input tape c bc zc c1249 mc
    (by rw [memoryC];exact source) (by rw [memoryC];exact destination)
  obtain ⟨c4,t,e4,h4,bt,zt,t1249,f4⟩:=cleanup_executes p round saved fit i input tape d bd zd d1249
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,bt,zt,t1249,
    md.frame (ArchiveFrame.of_binary f4) (by decide),?_,?_,?_,?_⟩
  · have first:=h0.trans (Nat.mul_le_mul_left (2^170)
      (Nat.pow_le_pow_left (show p.bound round+2 ≤ p.bound round+3 by omega) 2))
    have selection:=h2.trans (select_cost_polynomial (p.bound round))
    dsimp only [stepCost]
    omega
  · rw [f4.memory];exact sd
  · rw [f4.memory];exact dd
  · exact ((ArchiveFrame.of_binary f0).mono Finset.subset_union_right).trans
      ((f1.mono (by decide)).trans
        (((ArchiveFrame.of_binary f2).mono Finset.subset_union_right).trans
          ((f3.mono Finset.subset_union_left).trans
            ((ArchiveFrame.of_binary f4).mono Finset.subset_union_right))))
  · simpa only [f4.memory,memoryC] using m3

#print axioms step_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
