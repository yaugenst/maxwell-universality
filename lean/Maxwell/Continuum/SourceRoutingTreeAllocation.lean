import Maxwell.Continuum.SourceRoutingTreeAllocationPlan

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Allocation
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq (NatAssign.code prepare)
  (.seq (PhysicalMaterial.FixedSubtract.code 801 1)
    (.seq (NatAssign.code finish) (.seq PrivateZero.code (NatAssign.code restore))))
def work : Finset ℕ := Division.work∪({37}∪PrivateZero.banks)
def cost (v : ℕ→ℕ) (B : ℕ) : ℕ :=
  3000*8^2*(B+2)^2+29*(4*(B+1))+31+3000*8*(4*(B+1)+2)^2+
    2^31*(length v+1)*(16*(B+1)+2)^2+3000*8^2*(16*(B+1)+2)^2

theorem executes (v : ℕ→ℕ) (B : ℕ) (hn : 0<v 813) (htwo : v 819=2)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s)
    (hzero : PrivateZero.Clean s) (h839 : Blank s.val 839) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost v B ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧
      PrivateZero.Clean t ∧ Blank t.val 839 ∧
      (∀p,v 800 ≤ p→p<v 800+length v→t.val.memory p=false) ∧
      Memory.Frame (v 800) (length v) s.val.memory t.val.memory ∧ ArchiveFrame work s.val t.val := by
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩:=Arithmetic.stage prepare prepare_valid v B hv
    (by simp [prepare,NatAssign.Instruction.literalWidth]) input tape s hs hc
  have wa:=prepared_width v B hv
  have aExtra:=PrivateZero.clean_of_binary hzero f0 Arithmetic.work_subset
  obtain ⟨c1,b,e1,h1,bb,zb,f1⟩:=Arithmetic.decrement 801 (by decide) (prepared v)
    (by change 0<v 819*v 813;rw [htwo];omega) input tape a ba za
  have bExtra:=PrivateZero.clean_of_binary aExtra f1 (by decide)
  obtain ⟨c2,c,e2,h2,bc,zc,f2⟩:=Arithmetic.stage finish finish_valid (decreased v) (4*(B+1))
    (decreased_width v B hv) (by simp [finish,NatAssign.Instruction.literalWidth]) input tape b bb zb
  have cExtra:=PrivateZero.clean_of_binary bExtra f2 Arithmetic.work_subset
  have before : BinaryPrecision.Frame Division.work s.val c.val :=
    (f0.mono Arithmetic.work_subset).trans ((f1.mono (by decide)).trans (f2.mono Arithmetic.work_subset))
  have c839:=RationalAccumulator.blank_of_eq
    ((f2.tapes 839 (by decide)).trans ((f1.tapes 839 (by decide)).trans (f0.tapes 839 (by decide)))) h839
  obtain ⟨c3,d,e3,h3,zd,dExtra,_words,zeros,m3,f3⟩:=PrivateZero.executes (zeroValues v) (16*(B+1))
      (by omega) (fun i hi => zero_width v B hv i ((show ZeroHeap.controls⊆Division.ids by decide) hi))
      input tape c zc cExtra (fun i hi => bc i ((show ZeroHeap.controls⊆Division.ids by decide) hi))
  have bd:=PrivateZero.bank_of_frame bc f3
  obtain ⟨c4,t,e4,h4,bt,zt,f4⟩:=Arithmetic.stage restore restore_valid (zeroValues v) (16*(B+1))
      (zero_width v B hv) (by
        simp [restore,NatAssign.Instruction.literalWidth,show (2 : ℕ).bits.length=2 by decide]
        omega) input tape d bd zd
  have tExtra:=PrivateZero.clean_of_binary dExtra f4 Arithmetic.work_subset
  have t839:=RationalAccumulator.blank_of_eq (f4.tapes 839 (by decide))
      (RationalAccumulator.blank_of_eq (f3.tapes 839 (by omega) (by omega) (by decide)) c839)
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,bt,zt,tExtra,t839,?_,?_,
      ((ArchiveFrame.of_binary before).mono Finset.subset_union_left).trans
        ((f3.archive.mono Finset.subset_union_right).trans
          ((ArchiveFrame.of_binary (f4.mono Arithmetic.work_subset)).mono Finset.subset_union_left))⟩
  · have hw:=wa 801 (by decide)
    change c0 ≤ 3000*8^2*(B+2)^2 at h0
    change c2 ≤ 3000*8*(4*(B+1)+2)^2 at h2
    change c4 ≤ 3000*8^2*(16*(B+1)+2)^2 at h4
    rw [zero_length] at h3
    dsimp only [cost]
    omega
  · intro p hlo hhi
    rw [f4.memory]
    exact zeros p (by simpa only [zero_base] using hlo) (by simpa only [zero_base,zero_length] using hhi)
  · simpa only [zero_base,zero_length,before.memory,f4.memory] using m3

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Allocation
