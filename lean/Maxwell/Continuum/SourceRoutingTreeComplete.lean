import Maxwell.Continuum.SourceRoutingTreeStartupExecution

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.CompleteTree
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def rootWork : Finset ℕ := Division.work∪PrivateNode.banks.toFinset∪{37,831,830}
def work : Finset ℕ := TreeStartup.work∪rootWork
def code : Code := .seq TreeStartup.code RootRun.code
def cost (total forward backward : ℕ) : ℕ := TreeStartup.cost total forward backward+
  RootRun.cost (TreeStartup.heap total backward) total total

theorem archive {s t : BitRAMState} (hf : Traversal.Frame s t) : ArchiveFrame rootWork s t := by
  refine ⟨hf.inputHead,hf.randomCursor,hf.output,?_⟩
  intro i hi hn
  simp only [rootWork,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hn
  exact hf.tapes i hi hn.2.1 hn.1.1 (by simpa only [List.mem_toFinset] using hn.1.2) hn.2.2.1 hn.2.2.2

theorem count_width (total : ℕ) : (TreeStartup.count total).bits.length=TreeStartup.wordWidth total := by
  rw [TreeStartup.count,Nat.size_eq_bits_len,Nat.size_pow]
  rfl

theorem permutation_preserved {rows columns base width heap span : ℕ} {root : Targets.Target rows columns}
    {before after : ℕ→Bool} (hs : Storage.Permutation rows columns root before base width)
    (hf : Memory.Frame heap span before after) (hbefore : base+2^(columns+rows)*width ≤ heap) :
    Storage.Permutation rows columns root after base width := by
  apply IndexedMemory.same_memory _ _ before after _ _ _ hs
  intro p _ hp
  exact hf p (Or.inl (lt_of_lt_of_le hp hbefore))

theorem executes (total : ℕ) (ht : 1 ≤ total) (l : Layout (TreeStartup.count total))
    (root : Targets.Target total total)
    (hbefore : l.forward+TreeStartup.count total*TreeStartup.wordWidth total ≤ TreeStartup.heap total l.backward)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hm : Metadata l s.val) (hc : PrivateVisit.Clean s) (he : PrivateZero.Clean s)
    (hz : ∀i∈Division.ids,Blank s.val i) (h839 : Blank s.val 839) (h831 : Blank s.val 831) (h830 : Blank s.val 830)
    (hf : Storage.Permutation total total root s.val.memory l.forward (TreeStartup.wordWidth total))
    (hi : Storage.Permutation total total root.symm s.val.memory l.backward (TreeStartup.wordWidth total)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost total l.forward l.backward ∧
      LabelsAt (TreeStartup.heap total l.backward) (TreeStartup.count total) (TreeStartup.wordWidth total)
        0 total total root t.val.memory ∧
      PrivateVisit.Clean t ∧ Blank t.val 839 ∧ Blank t.val 831 ∧ Blank t.val 830 ∧
      (∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Blank t.val i) ∧ Metadata l t.val ∧
      Memory.Frame (TreeStartup.heap total l.backward)
        ((2^(total+1)-1)*stride (TreeStartup.count total) (TreeStartup.wordWidth total)) s.val.memory t.val.memory ∧
      ArchiveFrame work s.val t.val := by
  have seed:=SourceArithmetic.seed_bank l s hm hz
  rw [count_width total] at seed
  obtain ⟨c0,a,e0,h0,ba,za,_aExtra,a839,a830,zero,ma,fa,sourceWords⟩:=TreeStartup.executes total l.forward l.backward
    input tape s seed hc he h839 h830
  have a831:=RationalAccumulator.blank_of_eq (fa.tapes 831 (by omega) (by decide)) h831
  have hback : l.backward+TreeStartup.count total*TreeStartup.wordWidth total=TreeStartup.heap total l.backward := by
    dsimp only [TreeStartup.heap]
    rw [Nat.mul_comm]
  have forwardStored:=permutation_preserved hf ma hbefore
  have backwardStored:=permutation_preserved hi ma (Nat.le_of_eq hback)
  have leaves:=AssemblyTraversal.Frontier.initialized (TreeStartup.heap total l.backward) total total root _ zero
  let v:=TreeStartup.output total l.forward l.backward
  have base:=TreeStartup.output_base total l.forward l.backward
  have count:=TreeStartup.output_count total l.forward l.backward
  have width:=TreeStartup.output_width total l.forward l.backward
  have forward:=TreeStartup.output_forward total l.forward l.backward
  have backward:=TreeStartup.output_backward total l.forward l.backward
  have separated : IncidenceEncoding.Separated (v 803) ((v 801)*(v 802)) (v 804) ((v 801)*(v 802)) := by
    dsimp only [v]
    rw [count,width,forward,backward,←count_width]
    exact l.separated
  obtain ⟨c1,t,e1,h1,labels,zt,t839,t831,t830,quotientClean,ft,mt⟩:=RootRun.executes v (TreeStartup.heap total l.backward)
    total total root (TreeStartup.root_setup total l.forward l.backward ht (by omega)) separated
    (by simpa only [v,count,width,forward] using hbefore)
    (by simpa only [v,count,width,backward] using Nat.le_of_eq hback)
    input tape a ba za a839 a831 a830
    (by simpa only [v,forward,width] using forwardStored)
    (by simpa only [v,backward,width] using backwardStored) leaves
  have kept (i : ℕ) (hi : i∈SourceArithmetic.sourcePorts) :
      RationalAccumulator.Word t.val i (TreeStartup.seed total l.forward l.backward i) := by
    have hlo : 10 ≤ i := by simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    have hn : i∉rootWork := by
      simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    exact RationalAccumulator.word_of_eq ((archive ft).tapes i (Or.inr hlo) hn) (sourceWords i hi)
  have metadata : Metadata l t.val := by
    refine ⟨kept 709 (by decide),?_,kept 716 (by decide),kept 717 (by decide),?_⟩
    · rw [count_width]
      exact kept 711 (by decide)
    · exact BankArray.word_of_eq (((archive ft).tapes 718 (by omega) (by decide)).trans
        (fa.tapes 718 (by omega) (by decide))) hm.clock
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,labels,zt,t839,t831,t830,quotientClean,metadata,ma.trans ?_,
    (fa.mono Finset.subset_union_left).trans ((archive ft).mono Finset.subset_union_right)⟩
  intro p hp
  apply mt p
  rcases hp with hp|hp
  · exact Or.inl hp
  · right
    have powers : (2 : ℕ)^total ≤ 2^(total+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have spans:=Nat.mul_le_mul_right (stride (TreeStartup.count total) (TreeStartup.wordWidth total))
      (show 2^total-1 ≤ 2^(total+1)-1 by omega)
    exact (Nat.add_le_add_left spans _).trans hp

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.CompleteTree
