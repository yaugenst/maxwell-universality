import Maxwell.Continuum.SourceRoutingPhaseMemory

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem store {q : ℕ} (p : Plan q) (indexBank baseBank sourceBank : ℕ)
    (hiBank : 40 ≤ indexBank) (hbBank : 40 ≤ baseBank) (hsBank : 40 ≤ sourceBank)
    (slot : Fin 5) (index : Fin (q*q)) (value : ℕ) (fit : value.bits.length ≤ p.width)
    (saved : Fin 5→Vector (List Bool) (q*q)) (v : ℕ→ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (stored : GeometryArrays.Stored s.val.memory p.base p.width saved)
    (iw : Word s.val indexBank index.val) (bw : Word s.val baseBank (p.base slot))
    (vw : Word s.val sourceBank value) :
    ∃steps t,Executes input tape (BankArray.writeCanonicalCode 711 indexBank baseBank 718 sourceBank) steps s t ∧
      steps ≤ 2^20*(p.bound+3)^2 ∧ NatAssign.Bank GeometryArithmetic.ids v t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ Metadata p t.val ∧
      GeometryArrays.Stored t.val.memory p.base p.width
        (Function.update saved slot ((saved slot).set index (IncidenceEncoding.word p.width value))) ∧
      ArchiveFrame {37} s.val t.val ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (p.base slot+index.val*p.width)
        (IncidenceEncoding.word p.width value) := by
  obtain ⟨steps,t,he,hcost,bt,zt,t1249,mt,_,ft⟩:=GeometryArithmetic.write
    711 indexBank baseBank 718 sourceBank (by decide) hiBank hbBank (by decide) hsBank
    p.width (p.base slot) p.bound value p.clock (saved slot) index
    p.width_positive p.clock_length fit p.width_bound ((p.index_fit index).trans p.width_bound) (p.base_bound slot)
    input tape v s bank ready privateBlank metadata.width iw bw metadata.clock vw (stored slot)
  refine ⟨steps,t,he,hcost,bt,zt,t1249,metadata.frame ft (by decide),?_,ft,mt⟩
  rw [mt]
  exact GeometryArrays.write stored p.separated slot index (IncidenceEncoding.word p.width value)
    (IncidenceEncoding.word_length _ _)

structure Writes {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (i : Fin (q*q)) (v : ℕ→ℕ) : Prop where
  firstIndex : v 1201=i.val
  middleIndex : v 1210=(middleAddress colors i).val
  lastIndex : v 1211=(lastAddress colors i).val
  firstValue : v 1204=firstValue colors i
  middleValue : v 1207=middleValue target i
  lastValue : v 1206=lastValue target i
  firstBase : v 1216=p.base 2
  middleBase : v 1217=p.base 3
  lastBase : v 1218=p.base 4

def storeCode : Code := .seq (BankArray.writeCanonicalCode 711 1201 1216 718 1204)
  (.seq (BankArray.writeCanonicalCode 711 1210 1217 718 1207)
    (BankArray.writeCanonicalCode 711 1211 1218 718 1206))

theorem store_all {q : ℕ} {target : Equiv.Perm (Port q)} (p : Plan q) (colors : RowColoring target)
    (i : Fin (q*q)) (saved : Fin 5→Vector (List Bool) (q*q)) (v : ℕ→ℕ) (writes : Writes p colors i v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) (metadata : Metadata p s.val)
    (stored : GeometryArrays.Stored s.val.memory p.base p.width saved) :
    ∃steps t,Executes input tape storeCode steps s t ∧ steps ≤ 2^22*(p.bound+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids v t.val ∧ GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      Metadata p t.val ∧ GeometryArrays.Stored t.val.memory p.base p.width (updateArrays colors p.width saved i) ∧
      ArchiveFrame {37} s.val t.val ∧ MemoryFrame p s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,ma,sa,f0,m0⟩:=store p 1201 1216 1204 (by decide) (by decide) (by decide)
    2 i (firstValue colors i) (p.coordinate_fit (colors.color (port i))) saved v input tape s bank ready privateBlank metadata stored
    (by simpa only [writes.firstIndex] using bank 1201 (by decide))
    (by simpa only [writes.firstBase] using bank 1216 (by decide))
    (by simpa only [writes.firstValue] using bank 1204 (by decide))
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,mb,sb,f1,m1⟩:=store p 1210 1217 1207 (by decide) (by decide) (by decide)
    3 (middleAddress colors i) (middleValue target i) (p.coordinate_fit (target (port i)).2)
    _ v input tape a ba za a1249 ma sa
    (by simpa only [writes.middleIndex] using ba 1210 (by decide))
    (by simpa only [writes.middleBase] using ba 1217 (by decide))
    (by simpa only [writes.middleValue] using ba 1207 (by decide))
  obtain ⟨c2,t,e2,h2,bt,zt,t1249,mt,st,f2,m2⟩:=store p 1211 1218 1206 (by decide) (by decide) (by decide)
    4 (lastAddress colors i) (lastValue target i) (p.coordinate_fit (target (port i)).1)
    _ v input tape b bb zb b1249 mb sb
    (by simpa only [writes.lastIndex] using bb 1211 (by decide))
    (by simpa only [writes.lastBase] using bb 1218 (by decide))
    (by simpa only [writes.lastValue] using bb 1206 (by decide))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by omega,bt,zt,t1249,mt,?_,f0.trans (f1.trans f2),?_⟩
  · simpa only [updateArrays,Function.update_of_ne (by decide : (3 : Fin 5)≠2),
      Function.update_of_ne (by decide : (4 : Fin 5)≠2),
      Function.update_of_ne (by decide : (4 : Fin 5)≠3)] using st
  · have aFrame : MemoryFrame p s.val.memory a.val.memory := by
      rw [m0];exact write_memoryFrame p 2 (by decide) i (firstValue colors i) _
    have bFrame : MemoryFrame p a.val.memory b.val.memory := by
      rw [m1];exact write_memoryFrame p 3 (by decide) (middleAddress colors i) (middleValue target i) _
    have tFrame : MemoryFrame p b.val.memory t.val.memory := by
      rw [m2];exact write_memoryFrame p 4 (by decide) (lastAddress colors i) (lastValue target i) _
    exact aFrame.trans (bFrame.trans tFrame)

#print axioms store_all
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
