import Maxwell.Continuum.StoredDecoderRowValues

/-! The row loop invariant contains the actual array representations and
runtime bank words. Its fixed configuration supplies only mathematical
metadata bounds and the values of retained constant channels. -/
namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure Plan (n J : ℕ) where
  data : Vector ℕ n
  table : Table J
  base : ℕ
  slotWidth : ℕ
  geometryWidth : ℕ
  bankWidth : ℕ
  workspaceWidth : ℕ
  clock : List Bool
  geometryConstants : ℕ→ℕ
  constants : ℕ→ℕ
  slotPositive : 0<slotWidth
  slotBound : slotWidth≤geometryWidth
  clockLength : clock.length=slotWidth
  countWidth : n.bits.length≤geometryWidth
  fits : ∀i,(data.get i).bits.length≤slotWidth
  baseValue : geometryConstants 960=base
  widthValue : geometryConstants 961=slotWidth
  oneValue : geometryConstants 970=1
  bankWidth_two : 2≤bankWidth
  geometry_bank : geometryWidth≤bankWidth
  tableWidth : table.MetadataWidth bankWidth
  indexWidth : J.bits.length≤bankWidth
  powerPositive : 0<constants 144
  scalePositive : 0<constants 4708

structure State {n J : ℕ} (p : Plan n J) (j : ℕ) (gv v : ℕ→ℕ) (rv : ℕ→Parts)
    (s : Store) : Prop where
  geometry : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.geometryConstants gv s
  table : p.table.Ready s
  raw : RationalDataflow.Ready StoredInteger.slots rv s
  rawWidth : WidthBank StoredInteger.slots p.bankWidth rv
  index : Word s.val 728 j
  one : Word s.val 727 1
  bank : NatAssign.Bank ids v s.val
  bankWidth : ∀k∈ids,(v k).bits.length≤p.bankWidth
  workspace : WordCleanup.Bounded RationalCanonical.workspace p.workspaceWidth s.val
  fixed : ∀k∈constantPorts,v k=p.constants k
  cursor : gv 971=3*j

theorem State.count_frame {n J j : ℕ} {p : Plan n J} {gv v : ℕ→ℕ} {rv : ℕ→Parts}
    {s t : Store} (h : State p j gv v rv s) (f : CountedShifted.Frame 972 s t):State p j gv v rv t:=by
  have keep (k : ℕ) (hk : k≠972):=f.2.2.2.2.2.1 k hk
  have geometry:=h.geometry.count_frame 972 (by decide) f
  have table:=h.table.storage_frame f.2.2.1
    (fun k hk=>keep k (by simp only [Finset.mem_insert,Finset.mem_singleton] at hk;omega))
    geometry.ready.scratch geometry.ready.seven
  refine ⟨geometry,table,?_,h.rawWidth,word_of_eq (keep 728 (by decide)) h.index,
    word_of_eq (keep 727 (by decide)) h.one,?_,h.bankWidth,?_,h.fixed,h.cursor⟩
  · refine ⟨?_,?_⟩
    · intro k hk
      have hn : k≠972:=by
        intro he;subst k;exact (by decide : 972∉RationalDataflow.ids StoredInteger.slots) hk
      exact word_of_eq (keep k hn) (h.raw.1 k hk)
    · intro k hk
      exact blank_of_eq (keep k (by omega)) (h.raw.2 k hk)
  · intro k hk
    exact word_of_eq (keep k (by intro he;subst k;exact (by decide : 972∉ids) hk)) (h.bank k hk)
  · intro k hk
    obtain ⟨word,hw,stored⟩:=h.workspace k hk
    exact ⟨word,hw,BankArray.word_of_eq (keep k (by
      simp only [RationalCanonical.workspace,List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) stored⟩

theorem State.step {n J j : ℕ} {p : Plan n J} {gv v : ℕ→ℕ} {rv : ℕ→Parts}
    {s : Store} (h : State p j gv v rv s) (hj : j<J) (span : 3*j+3≤n)
    (input : List Bool) (tape : ℕ→Bool):
    ∃cost t gv' v' rv',Executes input tape stepCode cost s t ∧cost≤stepCost p.bankWidth p.workspaceWidth ∧
      State p (j+1) gv' v' rv' t ∧
      t.val.output=(bits (rowValues p.data p.constants j (p.table.get ⟨j,hj⟩))).reverse++s.val.output ∧
      GeometryOutput.OutputFrame stepWork s.val t.val:=by
  have hjw0 : j.bits.length≤J.bits.length:=by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hj.le
  have hjw : j.bits.length≤p.bankWidth:=hjw0.trans p.indexWidth
  obtain ⟨cost,t,ex,hc,out,gt,arrayT,rt,wt,it,ot,bt,wb,clean,frame⟩:=step_executes h.geometry p.slotPositive
    p.slotBound p.clockLength p.countWidth p.fits p.baseValue p.widthValue p.oneValue
    (by rw [h.cursor];exact span) p.table h.table rv h.raw ⟨j,hj⟩ h.index h.one v p.bankWidth p.workspaceWidth
    p.bankWidth_two p.geometry_bank h.bank h.bankWidth h.rawWidth p.tableWidth hjw
    (by rw [h.fixed 144 (by decide)];exact p.powerPositive)
    (by rw [h.fixed 4708 (by decide)];exact p.scalePositive) h.workspace input tape
  refine ⟨cost,t,_,_,_,ex,hc,⟨gt,arrayT,rt,wt,it,ot,bt,wb,?_,step_fixed _ _ _ _ _ h.fixed,?_⟩,?_,frame⟩
  · intro k hk
    exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr (clean k hk)⟩
  · rw [GeometryOutput.readPlanValues_cursor,GeometryOutput.tripleTargets_length,h.cursor]
    omega
  · rw [out,loaded_row _ _ _ _ _ _ h.fixed h.cursor]

#print axioms State.step
end Maxwell.Continuum.DecoderRow
