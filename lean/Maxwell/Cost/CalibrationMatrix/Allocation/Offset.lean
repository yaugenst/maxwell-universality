import Maxwell.Cost.CalibrationMatrix.Allocation.Bounds
import Maxwell.Cost.RationalCanonical.Transfer
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.CalibrationMatrix.Allocation.Offset
open Structured RationalAccumulator
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

/-- Routing publishes its first unused memory address in bank190. Bank252
retains that frontier while the matrix generator reuses low metadata. -/
def targets : List ℕ := [110,111,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,251]
def plan : List NatAssign.Instruction := targets.map (NatAssign.Instruction.add 252)
def ids : Finset ℕ := insert 252 targets.toFinset

def initial (heap n width capacity i : ℕ) : ℕ :=
  if i=110 then 0 else if i=111 then matrixSpan n width else
  if 230 ≤ i ∧ i < 244 then denseBase n width (i-230) else
  if 244 ≤ i ∧ i < 247 then sparseBase n width capacity (i-244) else
  if i=251 then memoryEnd n width capacity else if i=252 then heap else 0

def code (frontierBank : ℕ) : Code := .seq (.call (WordTransfer.clone frontierBank 252))
  (.seq Allocation.code (NatAssign.code plan))
def costCap (heap n width capacity : ℕ) : ℕ :=
  15*heap.bits.length+17+(Allocation.costCap n width capacity+
    NatAssign.price plan (initial heap n width capacity))

structure Stored (heap n width capacity : ℕ) (s : BitRAMState) : Prop where
  positive : Word s 110 heap
  negative : Word s 111 (heap+matrixSpan n width)
  dense : ∀ i : Fin 14, Word s (230+i.val) (heap+denseBase n width i.val)
  sparse : ∀ i : Fin 3, Word s (244+i.val) (heap+sparseBase n width capacity i.val)
  memoryEnd : Word s 251 (heap+memoryEnd n width capacity)
  temporary : ∀ i, 248 ≤ i → i ≤ 250 → Word s i 0
  frontier : Word s 252 heap

theorem translated_separated (heap : ℕ) {a an b bn : ℕ}
    (h : IncidenceEncoding.Separated a an b bn) :
    IncidenceEncoding.Separated (heap+a) an (heap+b) bn := by
  rcases h with h|h
  · left;omega
  · right;omega

theorem prefix_separated (heap offset count : ℕ) :
    IncidenceEncoding.Separated 0 heap (heap+offset) count := by left;omega

private theorem valid : ∀ op ∈ plan, op.Valid ids := by
  simp [plan,targets,NatAssign.Instruction.Valid,ids]
private theorem ids_ge : ∀ i ∈ ids, 4 ≤ i := by
  simp only [ids,targets,Finset.mem_insert,List.toFinset_cons,List.toFinset_nil,
    Finset.notMem_empty,or_false]
  omega

private theorem bank_before (heap n width capacity : ℕ) (s : BitRAMState)
    (hs : Allocation.Stored n width capacity s) (hheap : Word s 252 heap) :
    NatAssign.Bank ids (initial heap n width capacity) s := by
  intro i hi
  simp only [ids,targets,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,
    Finset.notMem_empty,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa [initial] using hheap
  · simpa [initial] using hs.positive
  · simpa [initial] using hs.negative
  all_goals first
    | simpa [initial] using hs.dense 0
    | simpa [initial] using hs.dense 1
    | simpa [initial] using hs.dense 2
    | simpa [initial] using hs.dense 3
    | simpa [initial] using hs.dense 4
    | simpa [initial] using hs.dense 5
    | simpa [initial] using hs.dense 6
    | simpa [initial] using hs.dense 7
    | simpa [initial] using hs.dense 8
    | simpa [initial] using hs.dense 9
    | simpa [initial] using hs.dense 10
    | simpa [initial] using hs.dense 11
    | simpa [initial] using hs.dense 12
    | simpa [initial] using hs.dense 13
    | simpa [initial] using hs.sparse 0
    | simpa [initial] using hs.sparse 1
    | simpa [initial] using hs.sparse 2
    | simpa [initial] using hs.memoryEnd

private theorem bank_after (heap n width capacity : ℕ) (s : BitRAMState)
    (hb : NatAssign.Bank ids (NatAssign.values plan (initial heap n width capacity)) s)
    (ht : ∀ i, 248 ≤ i → i ≤ 250 → Word s i 0) : Stored heap n width capacity s := by
  constructor
  · simpa [plan,targets,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial] using hb 110 (by decide)
  · simpa [plan,targets,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial] using hb 111 (by decide)
  · intro i
    have hh := hb (230+i.val) (by fin_cases i  <;> decide)
    fin_cases i  <;> simpa [plan,targets,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial] using hh
  · intro i
    have hh := hb (244+i.val) (by fin_cases i  <;> decide)
    fin_cases i  <;> simpa [plan,targets,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initial] using hh
  · simpa [plan,targets,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial] using hb 251 (by decide)
  · exact ht
  · simpa [plan,targets,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initial] using hb 252 (by decide)

def changed : Finset ℕ := NatAssign.changes Allocation.plan ∪ NatAssign.changes plan ∪ {252}

attribute [local irreducible] NatAssign.price

theorem executes (input : List Bool) (tape : ℕ → Bool) (frontierBank heap n width capacity : ℕ) (hfrontier : frontierBank ≠ 252) (s : Store)
    (hw : Word s.val 100 width) (hn : Word s.val 122 n) (hm : Word s.val 247 capacity)
    (hheap : Word s.val frontierBank heap) (h252 : Word s.val 252 0)
    (hz : ∀ i ∈ Allocation.ids, i ≠ 100 → i ≠ 122 → i ≠ 247 → Word s.val i 0)
    (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (code frontierBank) cost s t ∧ cost ≤ costCap heap n width capacity ∧
      Stored heap n width capacity t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨origin,hhw⟩ := hheap
  obtain ⟨targetOrigin,hzw⟩ := (zero_word_iff_blank _ _).mp h252
  obtain ⟨a,ea,atapes,fa⟩ := WordCall.clone frontierBank 252 hfrontier input tape heap.bits
    origin targetOrigin s hhw hzw
  have ha : Word a.val 252 heap := ⟨targetOrigin,by simp [atapes]⟩
  have keep (i : ℕ) (hi : i ≠ 252) : a.val.tapes i=s.val.tapes i := by simp [atapes,hi]
  obtain ⟨c1,b,eb,hc1,hb,sb,fb⟩ := Allocation.executes input tape n width capacity a
    (word_of_eq (keep 100 (by decide)) hw) (word_of_eq (keep 122 (by decide)) hn)
    (word_of_eq (keep 247 (by decide)) hm)
    (fun i hi h100 h122 h247 => word_of_eq (keep i (by
      simp only [Allocation.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
      omega)) (hz i hi h100 h122 h247))
    (fun i hi => blank_of_eq (keep i (by omega)) (hs i hi))
  have hbh : Word b.val 252 heap := word_of_eq (fb.tapes 252 (by decide)) ha
  obtain ⟨c2,t,et,hc2,bt,st,ft⟩ := NatAssign.executes ids ids_ge plan valid
    (initial heap n width capacity) input tape b (bank_before heap n width capacity b.val hb hbh) sb
  have fa' : BinaryPrecision.Frame changed s.val a.val := by
    refine ⟨fa.1,fa.2.1,fa.2.2.1,fa.2.2.2.1,fa.2.2.2.2.1,?_⟩
    intro i hi
    exact keep i (by intro he; subst i; exact hi (by simp [changed]))
  refine ⟨15*heap.bits.length+17+(c1+c2),t,ea.seq (eb.seq et),
    Nat.add_le_add_left (Nat.add_le_add hc1 hc2) (15*heap.bits.length+17),
    bank_after heap n width capacity t.val bt (fun i hi hj =>
      word_of_eq (ft.tapes i (by interval_cases i  <;> decide)) (hb.temporary i hi hj)),st,
    (fa'.trans (fb.mono (by intro i hi; simp only [changed,Finset.mem_union]; tauto))).trans
      (ft.mono (by intro i hi; simp only [changed,Finset.mem_union]; tauto))⟩

theorem costCap_le (heap n width capacity B : ℕ)
    (hh : heap.bits.length ≤ B) (hn : n.bits.length ≤ B)
    (hw : width.bits.length ≤ B) (hc : capacity.bits.length ≤ B) :
    costCap heap n width capacity ≤
      (3000*8^48+16*3000*8^20+40)*(B+2)^2 := by
  have hi : ∀ i ∈ ids, (initial heap n width capacity i).bits.length ≤ 4*B+6 := by
    intro i _
    unfold initial
    split_ifs with h110 h111 hd hs he hf
    · simp
    · have h1 := bits_mul_le n n
      have h2 := bits_mul_le (n*n) width
      dsimp [matrixSpan]
      omega
    · have h := dense_bits n width (i-230) (by omega)
      omega
    · have h := sparse_bits n width capacity (i-244) (by omega)
      omega
    · have h := memoryEnd_bits n width capacity
      omega
    · omega
    · simp
  have hp := NatAssign.price_bound ids plan valid (initial heap n width capacity) (4*B+6) hi (by
    simp [plan,targets,NatAssign.Instruction.literalWidth])
  have hlen : plan.length=20 := by decide
  rw [hlen] at hp
  have hz := Allocation.costCap_le n width capacity B hn hw hc
  have hp' : (4*B+6+2)^2=16*(B+2)^2 := by ring
  rw [hp'] at hp
  have budget (x y z : ℕ) (hx : x ≤ B)
      (hy : y ≤ 3000*8^48*(B+2)^2)
      (hz : z ≤ 3000*8^20*(16*(B+2)^2)) :
      15*x+17+(y+z) ≤ (3000*8^48+16*3000*8^20+40)*(B+2)^2 := by nlinarith
  exact budget _ _ _ hh hz hp

end Maxwell.Cost.CalibrationMatrix.Allocation.Offset
