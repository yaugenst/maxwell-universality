import Maxwell.Cost.RoutingPorts.Complete.Data
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop

/-! Semantic invariant of the sentinel-directed two-pointer completion.
The missing-port lists specify the result, but are not machine inputs. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Logical.Routing
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem table_sentinel_exact {n : ℕ} (entries : List (Fin n×Fin n)) (i : Fin n) :
    (table entries).get i=n ↔ i ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp [table,Vector.get,Fin.cast]
  | cons p entries ih =>
    change ((table entries).set p.1.val p.2.val p.1.isLt).get i=n ↔ _
    rw [DummyFill.get_set]
    by_cases he : p.1=i
    · simp only [he,↓reduceIte,List.map_cons,List.mem_cons,not_or,not_true_eq_false,false_and]
      exact iff_false_intro (Nat.ne_of_lt p.2.isLt)
    · simpa only [he,↓reduceIte,List.map_cons,List.mem_cons,Ne.symm he,false_or] using ih

theorem fill_sentinel_exact {n : ℕ} (entries completed : List (Fin n×Fin n)) (i : Fin n) :
    (fill entries completed).get i=n ↔
      i ∉ entries.map Prod.fst ∧ i ∉ completed.map Prod.fst := by
  rw [fill_table,table_sentinel_exact]
  simp only [List.map_append,List.map_reverse,List.mem_append,List.mem_reverse,not_or,and_comm]

theorem mem_drop_of_nodup {α : Type*} {xs : List α} (hn : xs.Nodup) (d : ℕ) (a : α) :
    a∈xs.drop d ↔ a∈xs ∧ a∉xs.take d := by
  have hn' : (xs.take d++xs.drop d).Nodup := by simpa only [List.take_append_drop] using hn
  have hd := (List.nodup_append.mp hn').2.2
  constructor
  · intro h
    refine ⟨List.mem_of_mem_drop h,?_⟩
    intro hm
    exact hd a hm a h rfl
  · rintro ⟨h,hm⟩
    have hh : a∈xs.take d++xs.drop d := by simpa only [List.take_append_drop] using h
    exact (List.mem_append.mp hh).resolve_left hm

structure CompletionPlan (n : ℕ) where
  entries : List (Fin n×Fin n)
  left : List (Fin n)
  right : List (Fin n)
  left_unused : ∀i, i ∉ entries.map Prod.fst ↔ i∈left
  right_unused : ∀i, i ∉ entries.map Prod.snd ↔ i∈right
  left_sorted : left.Pairwise (fun a b => a.val<b.val)
  right_sorted : right.Pairwise (fun a b => a.val<b.val)
  equal_length : left.length=right.length

namespace CompletionPlan

def remainingPairs {n : ℕ} (p : CompletionPlan n) : List (Fin n×Fin n) := p.left.zip p.right
def forward {n : ℕ} (p : CompletionPlan n) (d : ℕ) : Vector ℕ n :=
  fill p.entries (p.remainingPairs.take d)
def backward {n : ℕ} (p : CompletionPlan n) (d : ℕ) : Vector ℕ n :=
  fill (p.entries.map Prod.swap) ((p.remainingPairs.take d).map Prod.swap)

theorem left_nodup {n : ℕ} (p : CompletionPlan n) : p.left.Nodup :=
  p.left_sorted.imp (fun h he => (Nat.ne_of_lt h) (congrArg Fin.val he))
theorem right_nodup {n : ℕ} (p : CompletionPlan n) : p.right.Nodup :=
  p.right_sorted.imp (fun h he => (Nat.ne_of_lt h) (congrArg Fin.val he))

theorem forward_sentinel {n : ℕ} (p : CompletionPlan n) (d : ℕ) (i : Fin n) :
    (p.forward d).get i=n ↔ i∈p.left.drop d := by
  rw [forward,fill_sentinel_exact,p.left_unused,List.map_take,
    remainingPairs,List.map_fst_zip p.equal_length.le]
  exact (mem_drop_of_nodup p.left_nodup d i).symm

theorem backward_sentinel {n : ℕ} (p : CompletionPlan n) (d : ℕ) (j : Fin n) :
    (p.backward d).get j=n ↔ j∈p.right.drop d := by
  rw [backward,fill_sentinel_exact]
  simp only [List.map_map,Function.comp_def,Prod.fst_swap]
  rw [p.right_unused,List.map_take,remainingPairs,List.map_snd_zip p.equal_length.symm.le]
  exact (mem_drop_of_nodup p.right_nodup d j).symm

theorem forward_le {n : ℕ} (p : CompletionPlan n) (d : ℕ) (i : Fin n) :
    (p.forward d).get i≤n := by rw [forward,fill_table]; exact table_le _ _
theorem backward_le {n : ℕ} (p : CompletionPlan n) (d : ℕ) (j : Fin n) :
    (p.backward d).get j≤n := by rw [backward,fill_table]; exact table_le _ _

structure Cursor {n : ℕ} (p : CompletionPlan n) (d i j : ℕ) : Prop where
  done_le : d≤p.left.length
  left_le : i≤n
  right_le : j≤n
  left_remaining : ∀a∈p.left.drop d, i≤a.val
  right_remaining : ∀b∈p.right.drop d, j≤b.val

theorem initial {n : ℕ} (p : CompletionPlan n) : p.Cursor 0 0 0 :=
  ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,fun _ _ => Nat.zero_le _,fun _ _ => Nat.zero_le _⟩

theorem advance_left {n : ℕ} {p : CompletionPlan n} {d i j : ℕ}
    (h : p.Cursor d i j) (hi : i<n) (ho : (p.forward d).get ⟨i,hi⟩<n) :
    p.Cursor d (i+1) j := by
  refine ⟨h.done_le,by omega,h.right_le,?_,h.right_remaining⟩
  intro a ha
  have hl := h.left_remaining a ha
  have hn : a.val≠i := by
    intro he
    have hae : a=⟨i,hi⟩ := Fin.ext he
    rw [hae] at ha
    have := (p.forward_sentinel d ⟨i,hi⟩).mpr ha
    omega
  omega

theorem advance_right {n : ℕ} {p : CompletionPlan n} {d i j : ℕ}
    (h : p.Cursor d i j) (hj : j<n) (ho : (p.backward d).get ⟨j,hj⟩<n) :
    p.Cursor d i (j+1) := by
  refine ⟨h.done_le,h.left_le,by omega,h.left_remaining,?_⟩
  intro b hb
  have hl := h.right_remaining b hb
  have hn : b.val≠j := by
    intro he
    have hbe : b=⟨j,hj⟩ := Fin.ext he
    rw [hbe] at hb
    have := (p.backward_sentinel d ⟨j,hj⟩).mpr hb
    omega
  omega

theorem head_eq_of_minimum {n : ℕ} (xs : List (Fin n))
    (hs : xs.Pairwise (fun a b => a.val<b.val)) (d : ℕ) (a : Fin n)
    (ha : a∈xs.drop d) (hm : ∀b∈xs.drop d, a.val≤b.val) :
    ∃hd : d<xs.length, xs[d]=a := by
  have hd : d<xs.length := by
    by_contra hh
    rw [List.drop_of_length_le (by omega)] at ha
    exact List.not_mem_nil ha
  refine ⟨hd,?_⟩
  have hs' := hs.drop (i := d)
  rw [List.drop_eq_getElem_cons hd] at ha hs' hm
  rcases List.mem_cons.mp ha with ha | ha
  · exact ha.symm
  · have hlt := (List.pairwise_cons.mp hs').1 a ha
    have hle := hm xs[d] (List.mem_cons_self)
    omega

theorem right_available {n : ℕ} {p : CompletionPlan n} {d i j : ℕ}
    (h : p.Cursor d i j) (hi : i<n) (he : (p.forward d).get ⟨i,hi⟩=n) : j<n := by
  have hm := (p.forward_sentinel d ⟨i,hi⟩).mp he
  obtain ⟨hd,_⟩ := head_eq_of_minimum p.left p.left_sorted d ⟨i,hi⟩ hm h.left_remaining
  have hdr : d<p.right.length := by rw [←p.equal_length]; exact hd
  have hb : p.right[d]∈p.right.drop d := by
    rw [List.drop_eq_getElem_cons hdr]
    exact List.mem_cons_self
  have hl := h.right_remaining p.right[d] hb
  exact hl.trans_lt p.right[d].isLt

theorem next_pair {n : ℕ} {p : CompletionPlan n} {d i j : ℕ}
    (h : p.Cursor d i j) (hi : i<n) (hj : j<n)
    (he : (p.forward d).get ⟨i,hi⟩=n) (hf : (p.backward d).get ⟨j,hj⟩=n) :
    ∃hd : d<p.remainingPairs.length,
      p.remainingPairs[d]=(⟨i,hi⟩,⟨j,hj⟩) ∧ p.Cursor (d+1) (i+1) (j+1) := by
  obtain ⟨hdl,hel⟩ := head_eq_of_minimum p.left p.left_sorted d ⟨i,hi⟩
    ((p.forward_sentinel d ⟨i,hi⟩).mp he) h.left_remaining
  obtain ⟨hdr,her⟩ := head_eq_of_minimum p.right p.right_sorted d ⟨j,hj⟩
    ((p.backward_sentinel d ⟨j,hj⟩).mp hf) h.right_remaining
  have hd : d<p.remainingPairs.length := by simp only [remainingPairs,List.length_zip]; omega
  refine ⟨hd,?_,⟨by omega,by omega,by omega,?_,?_⟩⟩
  · simp only [remainingPairs,List.getElem_zip,hel,her]
  · have hp := p.left_sorted.drop (i := d)
    rw [List.drop_eq_getElem_cons hdl,hel] at hp
    intro a ha
    exact (List.pairwise_cons.mp hp).1 a ha
  · have hp := p.right_sorted.drop (i := d)
    rw [List.drop_eq_getElem_cons hdr,her] at hp
    intro b hb
    exact (List.pairwise_cons.mp hp).1 b hb

theorem write_next {n : ℕ} (p : CompletionPlan n) (d : ℕ)
    (hd : d<p.remainingPairs.length) (a b : Fin n) (he : p.remainingPairs[d]=(a,b)) :
    p.forward (d+1)=(p.forward d).set a b.val ∧
      p.backward (d+1)=(p.backward d).set b a.val := by
  constructor
  · rw [forward,List.take_succ_eq_append_getElem hd,he,fill_append]
    rfl
  · rw [backward,List.take_succ_eq_append_getElem hd,he,List.map_append]
    change fill (p.entries.map Prod.swap) ((p.remainingPairs.take d).map Prod.swap++[(b,a)])=_
    rw [fill_append]
    rfl

theorem finished {n : ℕ} {p : CompletionPlan n} {d i j : ℕ}
    (h : p.Cursor d i j) (hi : i=n) : d=p.left.length := by
  by_contra hn
  have hd : d<p.left.length := by have := h.done_le; omega
  have hm : p.left[d]∈p.left.drop d := by
    rw [List.drop_eq_getElem_cons hd]
    exact List.mem_cons_self
  have hl := h.left_remaining p.left[d] hm
  have hb := p.left[d].isLt
  omega

end CompletionPlan

def incidenceCompletionPlan {k n : ℕ} (source target : Fin k→Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) : CompletionPlan n where
  entries := realPairs source target
  left := DummyFill.unused (DummyFill.incidencePorts source)
  right := DummyFill.unused (DummyFill.incidencePorts target)
  left_unused i := by simpa [realPairs,DummyFill.incidencePorts,List.map_map] using
    (DummyFill.mem_unused (DummyFill.incidencePorts source) i).symm
  right_unused i := by simpa [realPairs,DummyFill.incidencePorts,List.map_map] using
    (DummyFill.mem_unused (DummyFill.incidencePorts target) i).symm
  left_sorted := by
    apply List.Pairwise.filter
    rw [←List.ofFn_id,List.pairwise_ofFn]
    intro a b hab
    exact hab
  right_sorted := by
    apply List.Pairwise.filter
    rw [←List.ofFn_id,List.pairwise_ofFn]
    intro a b hab
    exact hab
  equal_length := DummyFill.unused_lengths source target hs ht

theorem incidenceCompletionPlan_forward {k n : ℕ} (source target : Fin k→Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    let p := incidenceCompletionPlan source target hs ht
    p.forward p.left.length=(DummyFill.scatter (DummyFill.pairs source target)).map Fin.val := by
  dsimp only
  rw [CompletionPlan.forward,List.take_of_length_le (by
    simp [CompletionPlan.remainingPairs,incidenceCompletionPlan,List.length_zip,
      DummyFill.unused_lengths source target hs ht])]
  exact fill_eq_permutation source target hs ht

#print axioms CompletionPlan.next_pair
#print axioms CompletionPlan.finished
#print axioms incidenceCompletionPlan_forward

end Maxwell.Cost.RoutingPorts.Complete
