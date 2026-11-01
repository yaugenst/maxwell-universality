import Maxwell.Continuum.StoredReadoutPrepare
import Maxwell.Continuum.StoredGeometryEmit
import Maxwell.Cost.Structured.MemoryFootprint
import Maxwell.Cost.Structured.InputPositions

/-! A complete list of original-vertex placements is serialized directly
from the packed array, after charged offset setup and counter loading. -/
namespace Maxwell.Continuum.GeometryOutput.Readout
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code : Code:=.seq prepareCode (.seq (EmitNatural.code 989)
  (.seq (WordReplace.code 989 972) (terminalLoopCode 972)))
def work : Finset ℕ:=Finset.range 10∪{971,972,976,977,978,987,989}
def stream {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ) (first count : ℕ) : List Bool:=
  Codec.nat count++terminalStream data constants (3*first) count

def costBound (B count : ℕ) : ℕ:=2^22*(B+2)^2+(20*B+24)+(21*B+21)+
  ((count+1)*(13*B+15)+count*(2^30*(B+3)^2))

theorem code_memory : code.protectsMemory=true:=by decide +kernel

theorem executes {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (g : Context data base width B clock constants v s)
    (hw : 0<width) (hB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (hfit : ∀i,(data.get i).bits.length≤width)
    (hb : constants 960=base) (hv : constants 961=width) (ho : constants 970=1)
    (first count : ℕ) (hfirst : first.bits.length≤B) (hcount : count.bits.length≤B)
    (hthree : constants 969=3) (hspan : 3*first+3*count≤n)
    (hc : ∀j<count,∀k,(terminalCoordinate data constants (3*first+3*j) k).bits.length≤B)
    (firstWord : Word s.val 503 first) (countWord : Word s.val 500 count)
    (old : List Bool) (hold : BankArray.Word s.val 972 old) (hOld : old.length≤B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape code cost s t ∧ cost≤costBound B count ∧
      Context data base width B clock constants w t ∧ w 971=3*first+3*count ∧
      t.val.output=(stream data constants first count).reverse++s.val.output ∧
      OutputFrame work s.val t.val ∧
      ∃last : List Bool,last.length=count.bits.length ∧BankArray.Word t.val 972 last:=by
  have cursor : (3*first).bits.length≤B:=by
    have hh : (3*first).bits.length≤n.bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (by omega : 3*first≤n)
    exact hh.trans hn
  obtain ⟨c0,a,e0,h0,ga,f0⟩:=prepare_executes g first count hfirst hcount cursor hthree
    firstWord countWord input tape
  obtain ⟨b,e1,gb,out1,f1⟩:=ga.emit 989 (by decide) input tape
  have countEq : prepared v first count 989=count:=by simp only [prepared,Function.update_self]
  have startEq : prepared v first count 971=3*first:=by
    simp only [prepared,Function.update_of_ne (by decide : (971:ℕ)≠989),Function.update_self]
  obtain ⟨c2,c,e2,h2,gc,counter,f2⟩:=loadCounter_executes gb 989 972 (by decide) (by decide)
    old (BankArray.word_of_eq ((congrFun f1.2.2.2.2 972).trans (f0.tapes 972 (by decide))) hold)
    hOld input tape
  rw [countEq] at counter
  obtain ⟨origin,word⟩:=counter
  obtain ⟨c3,t,word',w,e3,h3,gt,ix,out3,word3,len3,f3⟩:=terminalLoop_executes gc hw hB hlen hn hfit hb hv ho
    (3*first) count 972 (by decide) startEq hspan hc input tape count.bits origin (addressValue_bits _) word
  refine ⟨c0+(20*(prepared v first count 989).bits.length+24)+(c2+c3),t,w,?_,?_,gt,ix,?_,?_,word',len3,origin,word3⟩
  · convert e0.seq (e1.seq (e2.seq e3)) using 1 <;> first | rfl | omega
  · rw [countEq]
    unfold costBound
    nlinarith only [h0,h2,h3,hcount,Nat.zero_le count]
  · rw [out3,f2.output,out1,countEq,f0.output]
    simp only [stream,List.reverse_append,List.append_assoc]
  · have run:=e0.seq (e1.seq (e2.seq e3))
    have positions:=run.protectsInputPositions (by decide +kernel)
    refine ⟨run.protectsMemory code_memory,positions.1,positions.2,?_⟩
    intro i hi
    have keep : 10 ≤ i ∧i≠971 ∧i≠972 ∧i≠976 ∧i≠977 ∧i≠978 ∧i≠987 ∧i≠989:=by
      simpa only [work,Finset.mem_union,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton,not_or,not_lt] using hi
    exact (f3 i keep.1 (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)).trans
      ((f2.tapes i keep.1 (by simpa only [Finset.mem_singleton] using keep.2.2.1)).trans ((congrFun f1.2.2.2.2 i).trans
        (f0.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton];omega))))

#print axioms executes
end Maxwell.Continuum.GeometryOutput.Readout
