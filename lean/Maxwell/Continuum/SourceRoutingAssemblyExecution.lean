import Maxwell.Continuum.SourceRoutingAssemblyFrames
import Maxwell.Continuum.SourceRoutingAssemblyCost

/-! The complete reusable reverse-pass node includes metadata setup,
actual child-clock calculation, label assembly and reclamation of every word. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq setupCode (.seq ChildPermutation.prepareCode
  (.seq ColorAssemble.passCode (WordCleanup.code live)))

theorem executes (q : ℕ→ℕ) (k B : ℕ) (hB : 1 ≤ B)
    (hn : q 801=2*2^k) (hw : q 802=k+2) (hq : ∀i∈controls,(q i).bits.length ≤ B)
    (data : ColorAssemble.Data k) (hsep : ColorAssemble.Separated (layout q) k)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NodeVisit.Clean s.val)
    (hi : ∀i∈controls,RationalAccumulator.Word s.val i (q i))
    (hcolors : BitArray.Represents s.val.memory (layout q).colors 1 (ColorPass.colorWords data.colors))
    (hl : BitArray.Represents s.val.memory (layout q).leftForward (layout q).childWidth
      (DoublingPass.words (layout q).childWidth data.left))
    (hr : BitArray.Represents s.val.memory (layout q).rightForward (layout q).childWidth
      (DoublingPass.words (layout q).childWidth data.right)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^44*(q 801+1)*(B+2)^2 ∧
      ColorAssemble.Represents (layout q) t.val.memory data (ColorAssemble.finalOutput (layout q) data) ∧
      NodeVisit.Clean t.val ∧ Node.Frame s.val t.val ∧
      ColorAssemble.MemoryFrame (layout q) k s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,b0,z0,f0⟩:=setup_executes q B hB hq input tape s hs hi
  obtain ⟨c1,b,cc,e1,h1,s1,hcc,f1⟩:=prepared q k hn hw input tape a b0 z0
  have clock : (q 801).bits.length=(layout q).parentWidth := by
    simpa only [layout,hw] using NodeSetup.clock_length q k hn
  obtain ⟨c2,c,h2,e2,cfg2,work2,z126,rep2,f2,m2⟩:=ColorAssemble.prepares k input tape (layout q)
    data (q 801).bits cc hw clock hcc hsep b s1.count s1.zero126 s1.config s1.workspace
    (by simpa only [f1.2.1,f0.memory] using hcolors)
    (by simpa only [f1.2.1,f0.memory] using hl)
    (by simpa only [f1.2.1,f0.memory] using hr)
  have s2:=s1.pass cfg2 work2 z126 f2
  obtain ⟨c3,t,e3,h3,zt,f3⟩:=cleanup_executes q k (q 801).bits cc input tape c s2
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,?_,zt,
    frame_trans (setup_frame f0) (frame_trans (metadata_frame f1)
      (frame_trans (pass_frame f2) (cleanup_frame f3))),?_⟩
  · have p1:=prepare_cost q k B hn hq
    have p2:=pass_cost q k B hn hw hq
    have p3:=cleanup_cost q k B hB hn hw hq (q 801).bits cc clock hcc
    have small : B+2 ≤ (q 801+1)*(B+2)^2 := by nlinarith
    have square : (B+2)^2 ≤ (q 801+1)*(B+2)^2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith only [h0,h1,h2,h3,p1,p2,p3,small,square]
  · simpa only [f3.memory] using rep2
  · intro p hp
    exact (congrFun f3.memory p).trans ((m2 p hp).trans ((congrFun f1.2.1 p).trans (congrFun f0.memory p)))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
