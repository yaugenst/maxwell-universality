import Maxwell.Continuum.RationalDataflowRowWrite
import Maxwell.Continuum.RationalDataflowRowPlan

/-! Fixed row-write plans materialize several cached outputs in one pass. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem Table.OutputReady.rowPlan_frame {n : ℕ} {S : Finset ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : RowPlanFrame S s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  have keep (j : ℕ) (hj : 10 ≤ j) (hj' : j<1000) (hw : j∉RowIndex.ids) :=
    f.tapes j hj (by
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
      have hp := positivePort_ge i
      have hn := negativePort_ge i
      have hd := denominatorPort_ge i
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega) hw
  refine ⟨hz,h7,RationalAccumulator.blank_of_eq (keep 37 (by decide) (by decide) (by decide)) h.packing,
    BankArray.word_of_eq (keep 210 (by decide) (by decide) (by decide)) h.width,
    BankArray.word_of_eq (keep 212 (by decide) (by decide) (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 213 (by decide) (by decide) (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 214 (by decide) (by decide) (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 215 (by decide) (by decide) (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

def Table.setD {n : ℕ} (a : Table n) (i : ℕ) (x : Parts) : Table n :=
  if hi : i<n then a.set ⟨i,hi⟩ x else a

def rowWritePlanCode (stride : ℕ) : List (ℕ×ℕ)→Code
  | [] => .skip
  | (offset,entry)::rest => .seq (rowWriteCode stride offset entry) (rowWritePlanCode stride rest)

def rowWriteTable {n : ℕ} (stride row : ℕ) : List (ℕ×ℕ)→(ℕ→Parts)→Table n→Table n
  | [],_,b => b
  | (offset,entry)::rest,v,b => rowWriteTable stride row rest v (b.setD (stride*row+offset) (v entry))

theorem RowWriteFrame.refl (s : BitRAMState) : RowWriteFrame s s :=
  ⟨rfl,rfl,rfl,fun _ _ _ _ => rfl⟩

theorem RowWriteFrame.trans {s t u : BitRAMState}
    (f : RowWriteFrame s t) (g : RowWriteFrame t u) : RowWriteFrame s u :=
  ⟨g.inputHead.trans f.inputHead,g.randomCursor.trans f.randomCursor,
    g.output.trans f.output,fun i hi hp hr => (g.tapes i hi hp hr).trans (f.tapes i hi hp hr)⟩

theorem RowWriteFrame.counter {s t : BitRAMState} (f : RowWriteFrame s t) : t.tapes 201=s.tapes 201 :=
  f.tapes 201 (by decide) (by decide) (by decide)

theorem rowWritePlan_executes {n m : ℕ} (a : Table n) (b : Table m) (S : Finset ℕ)
    (stride O W : ℕ) (plan : List (ℕ×ℕ)) (hvalid : ∀x∈plan,x.2∈S)
    (hoff : ∀x∈plan,x.1.bits.length≤O) (hm : b.MetadataWidth W)
    (v : ℕ→Parts) (hfit : ∀x∈plan,(v x.2).Width (addressValue b.width))
    (hpositive : 0<addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (hix : ∀x∈plan,stride*addressValue word+x.1<m)
    (s : Store) (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t, Executes input tape (rowWritePlanCode stride plan) cost s t ∧
      cost≤rowPlanCost stride O W plan ∧ RationalDataflow.Ready S v t ∧ a.Ready t ∧
      (rowWriteTable stride (addressValue word) plan v b).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧ RowWriteFrame s.val t.val := by
  induction plan generalizing b s with
  | nil => exact ⟨1,s,.skip s,by simp [rowPlanCost],hs,ha,hb,hblank,RowWriteFrame.refl _⟩
  | cons x rest ih =>
    have hxi := hix x (by simp)
    obtain ⟨cw,r,ew,hcw,br,ar,bor,zr,_,fr⟩ := rowWrite_executes a b S stride x.1 x.2
      (hvalid x (by simp)) v hpositive (hfit x (by simp)) hsep hdisjoint input tape word hxi s hs ha hb hi hblank
    have heq : b.setD (stride*addressValue word+x.1) (v x.2)=
        b.set ⟨stride*addressValue word+x.1,hxi⟩ (v x.2) := by
      simp only [Table.setD,dite_eq_left hxi]
    obtain ⟨ct,t,et,hct,bt,at',bot,zt,ft⟩ := ih (b.set ⟨stride*addressValue word+x.1,hxi⟩ (v x.2))
      (fun y hy => hvalid y (by simp [hy])) (fun y hy => hoff y (by simp [hy]))
      ⟨hm.width,hm.basePositive,hm.baseNegative,hm.baseDenominator,hm.clock⟩
      (fun y hy => hfit y (by simp [hy])) hpositive hsep hdisjoint
      (fun y hy => hix y (by simp [hy])) r br ar bor (BankArray.word_of_eq fr.counter hi) zr
    refine ⟨cw+ct,t,ew.seq et,?_,bt,at',?_,zt,fr.trans ft⟩
    · have hb' := (rowWriteCost_polynomial b word (v x.2) stride x.1 W hm hlen).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hoff x (by simp);omega :
          W+stride.bits.length+x.1.bits.length+5≤W+stride.bits.length+O+5) 2))
      simp only [rowPlanCost,List.length_cons,Nat.add_mul,Nat.one_mul] at hct ⊢
      omega
    · simpa only [rowWriteTable,heq] using bot

#print axioms rowWritePlan_executes
end Maxwell.Continuum.RationalDataflow.PartArray
