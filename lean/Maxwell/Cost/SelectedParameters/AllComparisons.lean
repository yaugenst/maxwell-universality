import Maxwell.Cost.SelectedParameters.Compare
import Maxwell.Cost.Execution

/-! A finite conjunction of stored positive-denominator rational comparisons.
Evaluation stops at the first failed comparison and retains every operand. -/

namespace Maxwell.Cost.SelectedParameters.AllComparisons
open Structured
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev Test := (ℕ×ℕ)×(ℕ×ℕ)
def failed (v : ℕ→ℕ) (q : Test) : Bool :=
  decide ((v q.2.1:ℚ)/v q.2.2 < (v q.1.1:ℚ)/v q.1.2)
def Valid (extra : Finset ℕ) (q : Test) : Prop :=
  q.1.1∈extra ∧ q.1.2∈extra ∧ q.2.1∈extra ∧ q.2.2∈extra
def Enabled (v : ℕ→ℕ) (q : Test) : Prop := 0<v q.1.2 ∧ 0<v q.2.2

def success : BitRAM := ⟨[.literal 35 false,.halt]⟩
def code : List Test→Code
  | [] => .call success
  | q::qs => .seq (Compare.code q.2.1 q.2.2 q.1.1 q.1.2) (.branch 35 .skip (code qs))
def unitCost (B : ℕ) : ℕ := 3000*8^4*(B+2)^2+8000*(B+2)^2

theorem failures_congr (extra : Finset ℕ) (qs : List Test)
    (hv : ∀ q ∈ qs, Valid extra q) (v w : ℕ→ℕ) (he : ∀ i ∈ extra, v i=w i) :
    qs.any (failed v)=qs.any (failed w) := by
  have hm : qs.map (failed v)=qs.map (failed w) := by
    apply List.map_congr_left
    intro r hr
    have ht := hv r hr
    simp only [failed,he r.1.1 ht.1,he r.1.2 ht.2.1,he r.2.1 ht.2.2.1,he r.2.2 ht.2.2.2]
  simpa only [List.any_map,Function.comp_def,id_eq] using congrArg (fun xs : List Bool => xs.any id) hm

theorem executes (extra : Finset ℕ) (he : ∀ i ∈ extra, 40 ≤ i)
    (qs : List Test) (hv : ∀ q ∈ qs, Valid extra q)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀ i ∈ Compare.ids extra, (v i).bits.length≤B)
    (hen : ∀ q ∈ qs, Enabled v q) (h35 : v 35=0) (h36 : v 36=0)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank (Compare.ids extra) v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t w, Executes input randomTape (code qs) cost s t ∧
      cost≤qs.length*(unitCost B+2)+2 ∧ t.val.registers 35=qs.any (failed v) ∧
      NatAssign.Bank (Compare.ids extra) w t.val ∧ NatAssign.Scratch t.val ∧
      (∀ i ∈ extra, w i=v i) ∧ (∀ i ∈ Compare.ids extra, (w i).bits.length≤B) ∧
      w 35=0 ∧ w 36=0 ∧ BinaryPrecision.Frame Compare.workspace s.val t.val := by
  induction qs generalizing v s with
  | nil =>
    let t := Store.ofState {s.val with registers:=Function.update s.val.registers 35 false}
    have et : Executes input randomTape (.call success) 2 s t := by
      apply Executes.call success s {s.val with pc:=1,registers:=Function.update s.val.registers 35 false} 1
      · apply executeInstructions_sound (instructions:=1)
        simp [executeInstructions,success,BitRAM.next,s.property,BitRAMState.setRegister]
      · rfl
    exact ⟨2,t,v,et,by simp,by simp [t,Store.ofState],hb,hs,
      by intro i hi;rfl,hw,h35,h36,⟨rfl,rfl,rfl,rfl,rfl,by intro i hi;rfl⟩⟩
  | cons q qs ih =>
    have hq := hv q (by simp)
    have hqe := hen q (by simp)
    obtain ⟨ac,u,ea,ha,hr,bu,su,fu⟩ := Compare.executes extra he
      q.2.1 q.2.2 q.1.1 q.1.2 hq.2.2.1 hq.2.2.2 hq.1 hq.2.1
      v B hw hqe.2 hqe.1 h35 h36 input randomTape s hb hs
    change ac≤unitCost B at ha
    let w := NatAssign.values (Compare.prepare q.2.1 q.2.2 q.1.1 q.1.2) v
    have wh := Compare.prepared q.2.1 q.2.2 q.1.1 q.1.2
      (he _ hq.2.2.1) (he _ hq.2.2.2) (he _ hq.1) (he _ hq.2.1) v
    have wk (i : ℕ) (hi : i∈extra) : w i=v i := by
      have hge := he i hi
      simp [w,wh,show i≠30 by omega,show i≠31 by omega,show i≠32 by omega,show i≠33 by omega]
    have w35 : w 35=0 := by simp [w,wh,h35]
    have w36 : w 36=0 := by simp [w,wh,h36]
    have ww (i : ℕ) (hi : i∈Compare.ids extra) : (w i).bits.length≤B := by
      by_cases h30 : i=30
      · subst i;simpa [w,wh] using hw q.2.1 (Finset.mem_union_left _ hq.2.2.1)
      by_cases h31 : i=31
      · subst i;simpa [w,wh] using hw q.2.2 (Finset.mem_union_left _ hq.2.2.2)
      by_cases h32 : i=32
      · subst i;simpa [w,wh] using hw q.1.1 (Finset.mem_union_left _ hq.1)
      by_cases h33 : i=33
      · subst i;simpa [w,wh] using hw q.1.2 (Finset.mem_union_left _ hq.2.1)
      simpa [w,wh,h30,h31,h32,h33] using hw i hi
    have htail : ∀ r ∈ qs, Valid extra r := fun r hr => hv r (by simp [hr])
    have hetail : ∀ r ∈ qs, Enabled w r := by
      intro r hr
      have ht := htail r hr
      simpa only [Enabled,wk r.1.2 ht.2.1,wk r.2.2 ht.2.2.2] using hen r (by simp [hr])
    have hsame := failures_congr extra qs htail w v wk
    change u.val.registers 35=failed v q at hr
    cases hf : failed v q with
    | true =>
      refine ⟨ac+2,u,w,ea.seq (Executes.yes (hr.trans hf) (Executes.skip u)),?_,?_,bu,su,
        wk,ww,w35,w36,fu⟩
      · simp only [List.length_cons];nlinarith only [ha,Nat.zero_le (qs.length*(unitCost B+2))]
      · simp [List.any_cons,hf,hr]
    | false =>
      obtain ⟨bc,t,z,eb,hbc,hbr,bt,st,zk,zw,z35,z36,ft⟩ :=
        ih htail w ww hetail w35 w36 u bu su
      refine ⟨ac+(1+bc),t,z,ea.seq (Executes.no (hr.trans hf) eb),?_,?_,bt,st,
        fun i hi => (zk i hi).trans (wk i hi),zw,z35,z36,fu.trans ft⟩
      · simp only [List.length_cons];nlinarith only [ha,hbc]
      · simpa only [List.any_cons,hf,Bool.false_or,hsame] using hbr

#print axioms executes

end Maxwell.Cost.SelectedParameters.AllComparisons
