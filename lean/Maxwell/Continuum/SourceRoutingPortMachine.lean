import Maxwell.Continuum.SourceRoutingPortPlan

/-! Bounded execution of the fixed incidence-to-port arithmetic program. -/

namespace Maxwell.Cost.RoutingPorts.Complete.PortArithmetic
open Structured Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000

theorem scratch_five {s t : BitRAMState}
    (hs : ∀i,i<5→Blank s i) (ht : NatAssign.Scratch t)
    (hf : BinaryPrecision.Frame ({0,1,2,3}∪ids) s t) : ∀i,i<5→Blank t i := by
  intro i hi
  by_cases hlo : i<4
  · exact ht i hlo
  · have he : i=4 := by omega
    subst i
    exact RationalAccumulator.blank_of_eq (hf.tapes 4 (by decide)) (hs 4 (by decide))

theorem widen_frame {s t : BitRAMState}
    (hf : BinaryPrecision.Frame ({0,1,2,3}∪ids) s t) :
    BinaryPrecision.Frame ({0,1,2,3,4}∪ids) s t := hf.mono (by decide)

theorem executes (v : ℕ→ℕ) (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (hhalf : 0<v 710) (B : ℕ) (hB : 2≤B) (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank ids v s.val)
    (hz : ∀i,i<5→Blank s.val i) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤2^120*(B+2)^2 ∧
      NatAssign.Bank ids (output v) t.val ∧ (∀i,i<5→Blank t.val i) ∧
      BinaryPrecision.Frame ({0,1,2,3,4}∪ids) s.val t.val := by
  obtain ⟨c0,a,e0,hc0,ba,za,fa⟩ := fixedBankStage_executes ids
    (fun i hi => by have := ids_lower i hi; omega) prepare prepare_valid (by decide) v B hw
    (by simp [prepare,NatAssign.Instruction.literalWidth,show (2 : ℕ).bits.length=2 by decide]; exact hB)
    input tape s hs (fun i hi => hz i (by omega))
  change NatAssign.Bank ids (prepared v) a.val at ba
  have za' := scratch_five hz za fa
  have wa := prepared_width v B hB hw
  have zeroa := prepared_zero v hzero
  have posa : 0<prepared v 710 := by
    simpa [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target] using hhalf
  obtain ⟨c1,b,e1,hc1,bb,zb,fb⟩ := NaturalDivMod.executes ids ids_lower (by decide)
    734 710 760 761 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (prepared v) zeroa posa (8*(B+1)) wa input tape a ba za'
  change NatAssign.Bank ids (v1 v) b.val at bb
  have wb := divided_width (prepared v) 734 710 760 761 _ (by decide) wa
  have zerob := divided_zero (prepared v) 734 710 760 761 (by decide) (by decide) zeroa
  have posb : 0<v1 v 736 := by
    simp [v1,divided,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]
  obtain ⟨c2,c,e2,hc2,bc,zc,fc⟩ := NaturalDivMod.executes ids ids_lower (by decide)
    735 736 762 763 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (v1 v) zerob posb (8*(B+1)) wb input tape b bb zb
  change NatAssign.Bank ids (v2 v) c.val at bc
  have wc := divided_width (v1 v) 735 736 762 763 _ (by decide) wb
  have zeroc := divided_zero (v1 v) 735 736 762 763 (by decide) (by decide) zerob
  have posc : 0<v2 v 736 := by
    simp [v2,v1,divided,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]
  obtain ⟨c3,d,e3,hc3,bd,zd,fd⟩ := NaturalDivMod.executes ids ids_lower (by decide)
    733 736 764 765 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (v2 v) zeroc posc (8*(B+1)) wc input tape c bc zc
  change NatAssign.Bank ids (v3 v) d.val at bd
  have wd := divided_width (v2 v) 733 736 764 765 _ (by decide) wc
  have zerod := divided_zero (v2 v) 733 736 764 765 (by decide) (by decide) zeroc
  have posd : 0<v3 v 737 := by
    simp [v3,v2,v1,divided,prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]
    omega
  obtain ⟨c4,e,e4,hc4,be,ze,fe⟩ := NaturalDivMod.executes ids ids_lower (by decide)
    764 737 766 767 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (v3 v) zerod posd (8*(B+1)) wd input tape d bd zd
  change NatAssign.Bank ids (v4 v) e.val at be
  have we := divided_width (v3 v) 764 737 766 767 _ (by decide) wd
  obtain ⟨c5,t,e5,hc5,bt,zt,ft⟩ := fixedBankStage_executes ids
    (fun i hi => by have := ids_lower i hi; omega) finish finish_valid (by decide)
    (v4 v) (8*(B+1)) we (by simp [finish,NatAssign.Instruction.literalWidth])
    input tape e be (fun i hi => ze i (by omega))
  refine ⟨c0+(c1+(c2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),?_,
    bt,scratch_five ze zt ft,(widen_frame fa).trans (fb.trans (fc.trans (fd.trans (fe.trans (widen_frame ft)))))⟩
  unfold stageCost at hc0 hc5
  have hsq : (8*(B+1)+2)^2≤100*(B+2)^2 := by
    calc
      _ ≤ (10*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  nlinarith only [hc0,hc1,hc2,hc3,hc4,hc5,hsq,Nat.zero_le ((B+2)^2)]

#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.PortArithmetic
