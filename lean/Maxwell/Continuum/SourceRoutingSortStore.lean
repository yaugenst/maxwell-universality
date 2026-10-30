import Maxwell.Continuum.SourceRoutingSortCleanup

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def storeCode : Code := BankArray.writeCanonicalCode 711 1201 1216 718 1212

theorem store_key {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (old : Vector (List Bool) (q*q))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (selected p round saved i) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved))
    (destination : BitArray.Represents s.val.memory p.destination p.width old) :
    ∃steps t,Executes input tape storeCode steps s t ∧ steps ≤ 2^20*(p.bound round+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (selected p round saved i) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧
      BitArray.Represents t.val.memory p.source p.width (IncidenceEncoding.words p.width saved) ∧
      BitArray.Represents t.val.memory p.destination p.width
        (old.set i (IncidenceEncoding.word p.width ((SortArrays.step round saved).get i))) ∧
      ArchiveFrame {37} s.val t.val ∧
      Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory t.val.memory := by
  have index : selected p round saved i 1201=i.val := selected_other p round saved i 1201 (by decide)
  have base : selected p round saved i 1216=p.destination := selected_other p round saved i 1216 (by decide)
  have value : selected p round saved i 1212=(SortArrays.step round saved).get i := selected_value p round saved i
  have destinationWidth : p.destination.bits.length ≤ p.bound round := by dsimp only [Plan.bound];omega
  obtain ⟨steps,t,he,hc,bt,zt,t1249,mt,st,ft⟩:=GeometryArithmetic.write
    711 1201 1216 718 1212 (by decide) (by decide) (by decide) (by decide) (by decide)
    p.width p.destination (p.bound round) ((SortArrays.step round saved).get i) p.clock old i
    p.width_positive p.clock_length (step_fits p.width round saved fit i) (p.width_bound round)
    ((p.index_fit i).trans (p.width_bound round)) destinationWidth input tape (selected p round saved i)
    s bank ready privateBlank metadata.width (by simpa only [index] using bank 1201 (by decide))
    (by simpa only [base] using bank 1216 (by decide)) metadata.clock
    (by simpa only [value] using bank 1212 (by decide)) destination
  refine ⟨steps,t,he,hc,bt,zt,t1249,metadata.frame ft (by decide),?_,st,ft,?_⟩
  · rw [mt]
    exact IncidenceEncoding.represents_write_disjoint source p.destination p.width i
      (IncidenceEncoding.word p.width ((SortArrays.step round saved).get i))
      (IncidenceEncoding.word_length _ _) p.separated
  · intro address outside
    rw [mt]
    apply MemoryWord.writeBits_outside
    rw [IncidenceEncoding.word_length]
    have bound:=Nat.mul_le_mul_right p.width i.isLt
    rcases outside with before|after
    · left;omega
    · right;simp only [Nat.succ_mul] at bound;omega

#print axioms store_key
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
