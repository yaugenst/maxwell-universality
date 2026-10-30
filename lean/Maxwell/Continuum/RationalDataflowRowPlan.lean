import Maxwell.Continuum.RationalDataflowRowRead
import Maxwell.Continuum.RationalDataflowArrayLoop
import Maxwell.Continuum.RationalDataflowTrace

/-! Fixed finite read plans assemble a row in the arithmetic register
bank. Their code is independent of the runtime table length and row. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def rowPlanCode (stride : ℕ) : List (ℕ×ℕ) → Code
  | [] => .skip
  | (offset,target)::rest => .seq (rowReadCode stride offset target) (rowPlanCode stride rest)

def rowPlanValues {n : ℕ} (a : Table n) (stride row : ℕ) : List (ℕ×ℕ) → (ℕ→Parts) → (ℕ→Parts)
  | [],v => v
  | (offset,target)::rest,v =>
      rowPlanValues a stride row rest (Function.update v target (a.getD (stride*row+offset)))

def rowPlanCost (stride O W : ℕ) (plan : List (ℕ×ℕ)) : ℕ :=
  plan.length*(2^30*(W+stride.bits.length+O+5)^2)+1

structure RowPlanFrame (S : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,10 ≤ i → i∉ports S → i∉RowIndex.ids → t.tapes i=s.tapes i

theorem RowPlanFrame.refl (S : Finset ℕ) (s : BitRAMState) : RowPlanFrame S s s :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ _ => rfl⟩

theorem RowPlanFrame.trans {S : Finset ℕ} {s t u : BitRAMState}
    (f : RowPlanFrame S s t) (g : RowPlanFrame S t u) : RowPlanFrame S s u :=
  ⟨g.memory.trans f.memory,g.inputHead.trans f.inputHead,g.randomCursor.trans f.randomCursor,
    g.output.trans f.output,fun i hi hp hr => (g.tapes i hi hp hr).trans (f.tapes i hi hp hr)⟩

theorem RowFrame.toPlan {S : Finset ℕ} {target : ℕ} {s t : BitRAMState}
    (f : RowFrame target s t) (ht : target∈S) : RowPlanFrame S s t := by
  refine ⟨f.memory,f.inputHead,f.randomCursor,f.output,?_⟩
  intro i hi hp hr
  apply f.tapes i hi _ hr
  intro hic
  exact hp (Finset.mem_biUnion.mpr ⟨target,ht,hic⟩)

theorem RowPlanFrame.counter {S : Finset ℕ} {s t : BitRAMState} (f : RowPlanFrame S s t) :
    t.tapes 201=s.tapes 201 := by
  apply f.tapes 201 (by decide) _ (by decide)
  intro hm
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
  have hp := positivePort_ge i
  have hn := negativePort_ge i
  have hd := denominatorPort_ge i
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem Table.get_width {n : ℕ} (a : Table n) (W : ℕ) (hm : a.MetadataWidth W)
    (s : Store) (ha : a.Ready s) (i : Fin n) : (a.get i).Width W := by
  have hbits (xs : List Bool) : (addressValue xs).bits.length≤xs.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)
  have hw : addressValue a.width≤W := by rw [←a.clock_length]; exact hm.clock
  refine ⟨?_,?_,?_⟩
  · exact (hbits _).trans ((ha.positive.length i).le.trans hw)
  · exact (hbits _).trans ((ha.negative.length i).le.trans hw)
  · exact (hbits _).trans ((ha.denominator.length i).le.trans hw)

theorem rowPlan_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (stride O W : ℕ)
    (plan : List (ℕ×ℕ)) (hvalid : ∀x∈plan,x.2∈S)
    (hoff : ∀x∈plan,x.1.bits.length≤O) (hm : a.MetadataWidth W)
    (v : ℕ→Parts) (hv : WidthBank S W v)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (hix : ∀x∈plan,stride*addressValue word+x.1<n)
    (s : Store) (hs : RationalDataflow.Ready S v s) (ha : a.Ready s)
    (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t, Executes input tape (rowPlanCode stride plan) cost s t ∧
      cost≤rowPlanCost stride O W plan ∧
      RationalDataflow.Ready S (rowPlanValues a stride (addressValue word) plan v) t ∧
      WidthBank S W (rowPlanValues a stride (addressValue word) plan v) ∧
      a.Ready t ∧ (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧ RowPlanFrame S s.val t.val := by
  induction plan generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp [rowPlanCost],hs,hv,ha,hblank,RowPlanFrame.refl _ _⟩
  | cons x rest ih =>
    have hxt := hvalid x (by simp)
    have hxi := hix x (by simp)
    obtain ⟨cr,r,er,hcr,br,ar,zr,fr⟩ := rowRead_executes a S stride x.1 x.2 hxt v input tape
      word hxi s hs ha hi hblank
    have hget : a.getD (stride*addressValue word+x.1)=a.get ⟨stride*addressValue word+x.1,hxi⟩ := by
      simp only [Table.getD,dite_eq_left hxi]
    have br' : RationalDataflow.Ready S (Function.update v x.2 (a.getD (stride*addressValue word+x.1))) r := by
      simpa only [hget] using br
    have vr : WidthBank S W (Function.update v x.2 (a.getD (stride*addressValue word+x.1))) :=
      hv.update x.2 (by rw [hget]; exact a.get_width W hm s ha _)
    have fplan := fr.toPlan hxt
    obtain ⟨ct,t,et,hct,bt,wt,at',zt,ft⟩ := ih
      (fun y hy => hvalid y (by simp [hy])) (fun y hy => hoff y (by simp [hy]))
      (Function.update v x.2 (a.getD (stride*addressValue word+x.1))) vr
      (fun y hy => hix y (by simp [hy])) r br' ar (BankArray.word_of_eq fplan.counter hi) zr
    refine ⟨cr+ct,t,er.seq et,?_,bt,wt,at',zt,fplan.trans ft⟩
    have hb := (rowReadCost_polynomial a word (v x.2) stride x.1 W hm hlen (hv x.2 hxt)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hoff x (by simp);omega :
        W+stride.bits.length+x.1.bits.length+5≤W+stride.bits.length+O+5) 2))
    simp only [rowPlanCost,List.length_cons,Nat.add_mul,Nat.one_mul] at hct ⊢
    omega

#print axioms rowPlan_executes
end Maxwell.Continuum.RationalDataflow.PartArray
