import Maxwell.Continuum.WellOriginalPassEntry
import Maxwell.Continuum.RationalDataflowTableWritePrefix

/-! Chronological original strengths are computed by the actual counted
loop. Each body reads the next two source words, rounds and writes one
strength, resets its arithmetic workspace, and increments both cursors. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def Plan.parts {n J : ℕ} (p : Plan n J) (i : ℕ) : Parts :=
  if h : i<n then p.part ⟨i,h⟩ else Parts.literal 0

theorem Plan.parts_eq {n J : ℕ} (p : Plan n J) (i : ℕ) (hi : i<n) :
    p.parts i=p.part ⟨i,hi⟩ := by simp only [Plan.parts,dite_eq_left hi]

def stepCode : Code := .seq entryCode incrementCode

def stepCost {n J : ℕ} (p : Plan n J) : ℕ := entryCost p+24*p.budget+36

def preserved (k : ℕ) : Prop :=
  300 ≤ k ∧ k<1000 ∧ k ≠ 972 ∧ k ≠ 995 ∧ k ≠ 996 ∧ k ≠ 998 ∧ k ≠ 999

theorem step_executes {n J i : ℕ} (p : Plan n J) (a : PartArray.Table J) (hi : i<n)
    (memory : ℕ→Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a i memory s) :
    ∃cost t,Executes input tape stepCode cost s t ∧ cost ≤ stepCost p ∧
      State p (a.set ⟨i,hi.trans_le p.capacity⟩ (p.part ⟨i,hi⟩)) (i+1) memory t ∧
      (p.part ⟨i,hi⟩).Width (addressValue a.width) ∧
      t.val.tapes 972=s.val.tapes 972 ∧
      (∀k,preserved k→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,hc0,h0,_,width,keep0⟩ := entry_executes p a hi memory input tape s h
  obtain ⟨c1,t,e1,hc1,h1,f1⟩ := increment_executes input tape u h0
  have ibits : i.bits.length ≤ p.budget := by
    apply le_trans _ p.count_width
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size hi.le
  refine ⟨c0+c1,t,e0.seq e1,by unfold stepCost;nlinarith,h1,width,?_,?_⟩
  · exact (f1.tapes 972 (by decide)).trans (keep0 972 (by decide) (by decide) (by decide) (by decide))
  · intro k hk
    exact (f1.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or];exact ⟨hk.2.2.2.2.2.1,hk.2.2.2.2.2.2⟩)).trans
      (keep0 k hk.1 hk.2.1 hk.2.2.2.1 hk.2.2.2.2.1)

def code : Code := CountedShifted.code 972 stepCode

def Invariant {n J : ℕ} (p : Plan n J) (memory : ℕ→Bool) (original : Store)
    (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃a : PartArray.Table J, State p a (n-remaining) memory s ∧
    a.CorrectPrefix p.parts (n-remaining) ∧
    ∀k,preserved k→s.val.tapes k=original.val.tapes k

theorem executes {n J : ℕ} (p : Plan n J) (a : PartArray.Table J) (memory : ℕ→Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a 0 memory s)
    (xs : List Bool) (origin : ℤ) (hvalue : addressValue xs=n) (hword : s.val.tapes 972=BitTape.shifted xs origin) :
    ∃cost t a' finalWord,Executes input tape code cost s t ∧
      cost ≤ (n+1)*(13*xs.length+15)+n*stepCost p ∧
      State p a' n memory t ∧ a'.CorrectPrefix p.parts n ∧
      t.val.tapes 972=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      t.val.registers 29=false ∧ (∀k,preserved k→t.val.tapes k=s.val.tapes k) := by
  have stable : ∀r u v,CountedShifted.Frame 972 u v→Invariant p memory s r u→Invariant p memory s r v := by
    intro r u v f ⟨hr,b,hb,completed,keep⟩
    refine ⟨hr,b,hb.count_frame f,completed,?_⟩
    intro k hk
    exact (f.2.2.2.2.2.1 k hk.2.2.1).trans (keep k hk)
  have bodyCorrect : ∀r ys u,Invariant p memory s (r+1) u→
      u.val.tapes 972=BitTape.shifted ys origin→addressValue ys=r→
      ∃c v,Executes input tape stepCode c u v ∧ Invariant p memory s r v ∧
        v.val.tapes 972=BitTape.shifted ys origin ∧ c ≤ stepCost p := by
    intro r ys u ⟨hr,b,hb,completed,keep⟩ word _
    have hi : n-(r+1)<n := by omega
    obtain ⟨c,v,e,hc,hv,width,counter,frame⟩ := step_executes p b hi memory input tape u hb
    have index : n-(r+1)+1=n-r := by omega
    have next := completed.next ⟨n-(r+1),hi.trans_le p.capacity⟩ (by rw [p.parts_eq _ hi];exact width)
    rw [p.parts_eq _ hi] at next
    refine ⟨c,v,e,⟨by omega,b.set ⟨n-(r+1),hi.trans_le p.capacity⟩ (p.part ⟨n-(r+1),hi⟩),?_,?_,?_⟩,counter.trans word,hc⟩
    · simpa only [index] using hv
    · simpa only [index] using next
    · intro k hk
      exact (frame k hk).trans (keep k hk)
  have initial : Invariant p memory s n s := by
    refine ⟨le_rfl,a,?_,?_,fun _ _=>rfl⟩
    · simpa only [Nat.sub_self] using h
    · simpa only [Nat.sub_self] using PartArray.Table.CorrectPrefix.empty a p.parts
  obtain ⟨c,t,finalWord,e,ht,word,len,done,hc⟩ :=
    CountedShifted.executes 972 origin stepCode input tape (Invariant p memory s) (fun _=>stepCost p)
      stable bodyCorrect n xs s hvalue hword initial
  obtain ⟨_,a',state,completed,keep⟩ := ht
  refine ⟨c,t,a',finalWord,e,?_,?_,?_,word,len,done,keep⟩
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hc
  · simpa only [Nat.sub_zero] using state
  · simpa only [Nat.sub_zero] using completed

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
