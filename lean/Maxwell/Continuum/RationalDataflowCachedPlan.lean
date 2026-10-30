import Maxwell.Continuum.RationalDataflowCachedRow
import Maxwell.Continuum.RationalDataflowRowPlan

/-! Fixed read plans for a table produced in the output bank. The original
input table remains represented throughout the reads. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def cachedPlanCode (stride : ℕ) : List (ℕ×ℕ) → Code
  | [] => .skip
  | (offset,target)::rest => .seq (cachedRowCode stride offset target) (cachedPlanCode stride rest)

theorem Table.OutputReady.get_width {n : ℕ} {a : Table n} {s : Store}
    (ha : a.OutputReady s) (W : ℕ) (hm : a.MetadataWidth W) (i : Fin n) :
    (a.get i).Width W := by
  have hbits (xs : List Bool) : (addressValue xs).bits.length ≤ xs.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length xs)
  have hw : addressValue a.width ≤ W := by rw [←a.clock_length];exact hm.clock
  exact ⟨(hbits _).trans ((ha.positive.length i).le.trans hw),
    (hbits _).trans ((ha.negative.length i).le.trans hw),
    (hbits _).trans ((ha.denominator.length i).le.trans hw)⟩

theorem cachedPlan_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (stride O W : ℕ)
    (plan : List (ℕ×ℕ)) (hvalid : ∀x∈plan,x.2∈S)
    (hoff : ∀x∈plan,x.1.bits.length ≤ O) (hm : a.MetadataWidth W)
    (v : ℕ→Parts) (hv : WidthBank S W v)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length ≤ W)
    (hix : ∀x∈plan,stride*addressValue word+x.1<n)
    (s : Store) (hs : RationalDataflow.Ready S v s) (ha : a.OutputReady s)
    (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (cachedPlanCode stride plan) cost s t ∧
      cost ≤ rowPlanCost stride O W plan ∧
      RationalDataflow.Ready S (rowPlanValues a stride (addressValue word) plan v) t ∧
      WidthBank S W (rowPlanValues a stride (addressValue word) plan v) ∧
      a.OutputReady t ∧ (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      RowPlanFrame S s.val t.val := by
  induction plan generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp [rowPlanCost],hs,hv,ha,hblank,RowPlanFrame.refl _ _⟩
  | cons x rest ih =>
    have hxt := hvalid x (by simp)
    have hxi := hix x (by simp)
    obtain ⟨cr,r,er,hcr,br,ar,zr,fr⟩ := cachedRow_executes a S stride x.1 x.2 hxt v input tape
      word hxi s hs ha hi hblank
    have hget : a.getD (stride*addressValue word+x.1)=a.get ⟨stride*addressValue word+x.1,hxi⟩ := by
      simp only [Table.getD,dite_eq_left hxi]
    have br' : RationalDataflow.Ready S (Function.update v x.2 (a.getD (stride*addressValue word+x.1))) r := by
      simpa only [hget] using br
    have vr : WidthBank S W (Function.update v x.2 (a.getD (stride*addressValue word+x.1))) :=
      hv.update x.2 (by rw [hget];exact ha.get_width W hm _)
    have fplan := fr.toPlan hxt
    obtain ⟨ct,t,et,hct,bt,wt,at',zt,ft⟩ := ih
      (fun y hy => hvalid y (by simp [hy])) (fun y hy => hoff y (by simp [hy]))
      (Function.update v x.2 (a.getD (stride*addressValue word+x.1))) vr
      (fun y hy => hix y (by simp [hy])) r br' ar (BankArray.word_of_eq fplan.counter hi) zr
    refine ⟨cr+ct,t,er.seq et,?_,bt,wt,at',zt,fplan.trans ft⟩
    have hb := (rowReadCost_polynomial a word (v x.2) stride x.1 W hm hlen (hv x.2 hxt)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hoff x (by simp);omega :
        W+stride.bits.length+x.1.bits.length+5 ≤ W+stride.bits.length+O+5) 2))
    simp only [rowPlanCost,List.length_cons,Nat.add_mul,Nat.one_mul] at hct ⊢
    omega

theorem Table.Ready.cachedPlan_frame {n : ℕ} {S : Finset ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : RowPlanFrame S s.val t.val) (hz : BankArray.Scratch t.val)
    (h7 : RationalAccumulator.Blank t.val 7) : a.Ready t := by
  have keep (i : ℕ) (hlo : 10 ≤ i) (hhi : i<1000) (hindex : i∉RowIndex.ids) := f.tapes i hlo (by
    intro hi
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hi
    have hp := positivePort_ge k
    have hn := negativePort_ge k
    have hd := denominatorPort_ge k
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    omega) hindex
  refine ⟨hz,h7,BankArray.word_of_eq (keep 200 (by decide) (by decide) (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide) (by decide) (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide) (by decide) (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide) (by decide) (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide) (by decide) (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

#print axioms cachedPlan_executes
end Maxwell.Continuum.RationalDataflow.PartArray
