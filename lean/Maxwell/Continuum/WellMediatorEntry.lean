import Maxwell.Continuum.WellMediatorLoad

/-! One mediator strength imports the actual pair of point words, selects
its axis, computes and stores its rounded strength, then restores the
canonical parameter bank. -/
namespace Maxwell.Continuum.RationalDataflow.WellMediatorEntry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def code : Code := .seq WellMediatorLoad.code (.seq WellMediatorWrite.code WellStrengthReset.code)

def target (geometry : ℕ→ℕ) (v : ℕ→Parts) : ℚ := -(WellMediatorLoad.coupling geometry v)^2/(v 4).value

def part (P : ℕ) (geometry : ℕ→ℕ) (v : ℕ→Parts) : Parts :=
  Parts.literal (WellStrength.numerator P (v 1).value (target geometry v):ℚ)

def costBound (P B M : ℕ) : ℕ := 4*(37*B+39)+1+
  (2^126*(B+2)^2+2^184*(P+256*(B+1)+16)^2+2^20*(M+5)^2)+
    (11*operationCost (P+4096*(256*(B+1))+4179)+1)

theorem executes {n : ℕ} (a : PartArray.Table n) (P B M : ℕ)
    (hB : 4 ≤ B) (hP : (2^P).bits.length ≤ B)
    (geometry : ℕ→ℕ) (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (hw : WidthBank WellStrength.bank B v) (hg : Good WellStrength.bank v)
    (ha : (v 4).value ≠ 0) (hn : (v 1).value+target geometry v ≠ 0)
    (gw : ∀x∈WellMediatorLoad.plan,(geometry x.1).bits.length ≤ B)
    (i : Fin n) (index : List Bool) (hindex : addressValue index=i.val) (hlen : index.length ≤ M)
    (hmeta : a.MetadataWidth M) (hfit : P+4096*(256*(B+1))+4179 ≤ addressValue a.width)
    (hsep : a.Separated) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready WellStrength.bank v s) (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P))
    (hout : a.OutputReady s) (hi : BankArray.Word s.val 999 index)
    (words : ∀x∈WellMediatorLoad.plan,Word s.val x.1 (geometry x.1)) :
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ costBound P B M ∧
      Ready WellStrength.bank v t ∧ (a.set i (part P geometry v)).OutputReady t ∧
      t.val.memory=a.writeMemory i (part P geometry v) s.val.memory ∧
      (part P geometry v).Width (addressValue a.width) ∧ DyadicFloor.Clean t.val ∧
      Word t.val 144 (2^P) ∧ BankArray.Word t.val 999 index ∧
      (∀k,300 ≤ k→k<1000→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,e0,hc0,r0,w0,g0,f0⟩ := WellMediatorLoad.executes geometry v B hw hg gw input tape s hr words
  have arithmetic0 : BinaryPrecision.Frame (workspace WellStrength.bank) s.val u.val :=
    f0.mono Finset.subset_union_right
  have keep0 (k : ℕ) (hk : 107 ≤ k) (hk' : k<1000) : u.val.tapes k=s.val.tapes k :=
    f0.tapes k (fun h=>(outside_workspace WellStrength.bank k (Or.inr ⟨hk,hk'⟩))
      (Finset.mem_union_right _ h))
  have midpoint0 := WellMediatorLoad.preserves geometry v 1 (by decide)
  have scale0 := WellMediatorLoad.preserves geometry v 4 (by decide)
  have target0 : WellMediatorWrite.target (WellMediatorLoad.values geometry v)=target geometry v := by
    rw [WellMediatorWrite.target,WellMediatorLoad.selected geometry v canonical,scale0]
    rfl
  have table0 := hout.rounded_frame r0
    (arithmetic0.mono (RoundedInteger.arithmetic_workspace_subset WellStrength.bank))
  obtain ⟨c1,w,e1,hc1,r1,g1,w1,value1,table1,memory1,z1,power1,index1,keep1⟩ :=
    WellMediatorWrite.executes a P B M hB hP _ w0 g0 (by rwa [scale0])
      (by rwa [midpoint0,target0]) i index hindex hlen hmeta hfit hsep input tape u r0
      (hz.arithmetic_frame arithmetic0) (word_of_eq (keep0 144 (by decide) (by decide)) hp)
      table0 (BankArray.word_of_eq (keep0 999 (by decide) (by decide)) hi)
  have widthParameters : ∀k∈WellStrengthReset.parameters,
      (WellMediatorWrite.output P (WellMediatorLoad.values geometry v) k).Width B := by
    intro k hk
    rw [WellStrengthReset.mediator_parameter _ _ k hk,WellMediatorLoad.preserves]
    · apply hw
      simp only [WellStrengthReset.parameters,Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl <;> decide
    · simp only [WellStrengthReset.parameters,Finset.mem_insert,Finset.mem_singleton] at hk
      omega
  obtain ⟨c2,t,e2,hc2,r2,_,_,f2⟩ := WellStrengthReset.executes _
    (P+4096*(256*(B+1))+4179) B (by omega) (by omega) w1 g1 widthParameters input tape w r1
  rw [WellStrengthReset.reset_mediator,WellMediatorLoad.resets,canonical] at r2
  rw [midpoint0,target0] at value1
  change WellMediatorWrite.output P (WellMediatorLoad.values geometry v) 0=part P geometry v at value1
  have table2 := table1.rounded_frame r2
    (f2.mono (RoundedInteger.arithmetic_workspace_subset WellStrength.bank))
  rw [value1] at table2 memory1
  have width : (part P geometry v).Width (addressValue a.width) := by
    rw [←value1]
    exact (w1 0 (by decide)).mono hfit
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by unfold costBound;omega,r2,table2,?_,width,
    z1.arithmetic_frame f2,word_of_eq (f2.tapes 144 (outside_workspace _ _ (by decide))) power1,
    BankArray.word_of_eq (f2.tapes 999 (outside_workspace _ _ (by decide))) index1,?_⟩
  · rw [f2.memory,memory1,f0.memory]
  · intro k hk hk'
    exact (f2.tapes k (outside_workspace _ _ (Or.inr ⟨by omega,hk'⟩))).trans
      ((keep1 k hk hk').trans (keep0 k (by omega) hk'))

#print axioms executes
end Maxwell.Continuum.RationalDataflow.WellMediatorEntry
