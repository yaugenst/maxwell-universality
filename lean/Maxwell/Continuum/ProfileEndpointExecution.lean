import Maxwell.Continuum.ProfileEndpointSemantics

/-! Actual stored-table endpoint moment execution, including resetting the
shared registers. No sum or corrected coefficient is supplied as input. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def endpointWorkingWidth (n W : ℕ) : ℕ := W+5*n+5
def endpointProgram : Code := .seq (program dftReset) endpointCode
def endpointCost (n W len : ℕ) : ℕ :=
  11*operationCost W+1+(n+1)*(13*len+15)+
    n*(2^20*(endpointWorkingWidth n W+5)^2+5*operationCost (endpointWorkingWidth n W)+1)

theorem endpoint_loop_executes {n : ℕ} (a : PartArray.Table n) (W : ℕ) (hW : 1≤W)
    (hm : a.MetadataWidth W) (ha : ∀i,(a.get i).Width W) (hd : ∀i,(a.get i).denominator=1)
    (v : ℕ→Parts) (hv : IntegerBank dftRegisters v) (hw : WidthBank dftRegisters W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hc : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : Ready dftRegisters v s) (ht : a.Ready s) :
    ∃cost t finalWord,Executes input tape endpointCode cost s t ∧
      Ready dftRegisters (endpointValues a v n) t ∧ a.Ready t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤(n+1)*(13*xs.length+15)+
        n*(2^20*(endpointWorkingWidth n W+5)^2+(5*operationCost (endpointWorkingWidth n W)+1)) := by
  have hbase : W≤endpointWorkingWidth n W := by unfold endpointWorkingWidth;omega
  have before (k : ℕ) (hk : k<n) :
      WidthBank dftRegisters (endpointWorkingWidth n W) (endpointValues a v k) :=
    (endpointValues_width a v W hW ha hd hv hw k hk.le).2.mono (by
      unfold endpointWorkingWidth;omega)
  have body (k : ℕ) (hk : k<n) (st : Store)
      (hr : Ready dftRegisters (endpointLoaded a v k) st) :
      ∃cost t,Executes input tape (program endpointBody) cost st t ∧
        cost≤5*operationCost (endpointWorkingWidth n W)+1 ∧
        Ready dftRegisters (endpointStep (endpointLoaded a v k)) t ∧
        BinaryPrecision.Frame (workspace dftRegisters) st.val t.val := by
    obtain ⟨hg,hb⟩ := endpointValues_width a v W hW ha hd hv hw k hk.le
    have hi : n-1-k<n := by omega
    have hg' : IntegerBank dftRegisters (endpointLoaded a v k) := hg.update 1 (by
      simpa only [PartArray.Table.getD,dite_eq_left hi] using hd ⟨n-1-k,hi⟩)
    have hb' : WidthBank dftRegisters (W+5*k) (endpointLoaded a v k) :=
      hb.update 1 ((a.getD_width W hW ha _).mono (by omega))
    have trace := (endpointStep_trace _ _ hg' hb').2.2
    have bound : W+5*k+5≤endpointWorkingWidth n W := by unfold endpointWorkingWidth;omega
    obtain ⟨cost,t,e,h,b,f⟩ := RationalDataflow.program_executes dftRegisters endpointBody
      endpointBody_valid _ (endpointWorkingWidth n W)
      (WidthTrace.mono _ _ _ _ _ bound trace) input tape st hr
    exact ⟨cost,t,e,by simpa only [endpointBody,List.length_cons,List.length_nil] using h,b,f⟩
  unfold endpointCode
  exact PartArray.program_executes a dftRegisters 1 (by decide) (program endpointBody)
    endpointStep v (endpointWorkingWidth n W) (5*operationCost (endpointWorkingWidth n W)+1)
    (hm.mono hbase) before input tape body xs origin (hlen.trans hbase) s hn hc hs ht

theorem endpoint_executes {n : ℕ} (a : PartArray.Table n) (W : ℕ) (hW : 1≤W)
    (hm : a.MetadataWidth W) (ha : ∀i,(a.get i).Width W) (hd : ∀i,(a.get i).denominator=1)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hc : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : Ready dftRegisters v s) (ht : a.Ready s) :
    ∃cost t finalWord,Executes input tape endpointProgram cost s t ∧
      Ready dftRegisters (endpointValues a (dftResetValues v) n) t ∧ a.Ready t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤endpointCost n W xs.length ∧
      IntegerBank dftRegisters (endpointValues a (dftResetValues v) n) ∧
      WidthBank dftRegisters (endpointWorkingWidth n W) (endpointValues a (dftResetValues v) n) ∧
      (endpointValues a (dftResetValues v) n 0).value=∑j∈Finset.range n,(a.getD j).value ∧
      (endpointValues a (dftResetValues v) n 3).value=∑j∈Finset.range n,(j:ℚ)^2*(a.getD j).value := by
  obtain ⟨c0,t0,e0,h0,r0,f0⟩ := RationalDataflow.program_executes dftRegisters dftReset
    dftReset_valid v W (dftReset_width v W hW hw) input tape s hs
  have initialInteger : IntegerBank dftRegisters (dftResetValues v) := by
    intro i hi
    rw [dftResetValues_eq,ite_eq_left (Finset.mem_range.mp hi)]
    rfl
  have initialWidth := (dftResetValues_width v).mono hW
  obtain ⟨c1,t,word,e1,r1,a1,counter,len,cost⟩ := endpoint_loop_executes a W hW hm ha hd
    (dftResetValues v) initialInteger initialWidth input tape xs origin hlen t0 hn
    ((f0.tapes 201 (outside_workspace _ _ (by decide))).trans hc) r0
    (ht.arithmetic_frame _ f0 r0.2)
  obtain ⟨hg,hb⟩ := endpointValues_width a (dftResetValues v) W hW ha hd
    initialInteger initialWidth n le_rfl
  have values := endpointValues_final a (dftResetValues v)
    (fun i => by simp only [Parts.Valid,hd i];exact Nat.zero_lt_one) initialInteger.good (by
      simp [dftResetValues_eq,Parts.literal_value])
  refine ⟨c0+c1,t,word,e0.seq e1,r1,a1,counter,len,?_,hg,
    hb.mono (by unfold endpointWorkingWidth;omega),values⟩
  simp only [dftReset,List.length_map,List.length_range] at h0
  unfold endpointCost
  simp only [Nat.add_assoc] at cost ⊢
  omega

#print axioms endpoint_executes
end Maxwell.Continuum.Profile.Runtime
