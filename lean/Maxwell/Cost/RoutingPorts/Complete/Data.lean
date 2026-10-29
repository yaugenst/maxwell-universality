import Maxwell.Logical.Routing.DummyFill
import Maxwell.Cost.FixedWidth
import Maxwell.Cost.Array

namespace Maxwell.Cost.RoutingPorts.Complete
open Logical.Routing

/-- A natural-valued partial table uses the out-of-range value n as its
sentinel. Thus every occupied slot and every unused slot are distinguishable
at the same fixed binary width, including n a power of two. -/
def table {n : ℕ} (entries : List (Fin n × Fin n)) : Vector ℕ n :=
  entries.foldr (fun p saved => saved.set p.1.val p.2.val p.1.isLt) (Vector.replicate n n)

theorem table_absent {n : ℕ} (entries : List (Fin n × Fin n)) (i : Fin n)
    (hi : i ∉ entries.map Prod.fst) : (table entries).get i=n := by
  induction entries with
  | nil => simp [table,Vector.get,Fin.cast]
  | cons p entries ih =>
    have hn : p.1 ≠ i := by intro he;apply hi;simp [he]
    have ht : i ∉ entries.map Prod.fst := by intro h;apply hi;simp [h]
    change ((table entries).set p.1.val p.2.val p.1.isLt).get i=_
    rw [DummyFill.get_set]
    simp only [hn,↓reduceIte,ih ht]

theorem table_mem {n : ℕ} (entries : List (Fin n × Fin n))
    (hn : (entries.map Prod.fst).Nodup) (p : Fin n × Fin n) (hp : p ∈ entries) :
    (table entries).get p.1=p.2.val := by
  induction entries with
  | nil => simp at hp
  | cons a entries ih =>
    have hhead := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with he|hp
    · subst p
      change ((table entries).set a.1.val a.2.val a.1.isLt).get a.1=_
      simp [DummyFill.get_set]
    · have hne : a.1 ≠ p.1 := by
        intro he
        apply hhead.1
        exact List.mem_map.mpr ⟨p,hp,he.symm⟩
      change ((table entries).set a.1.val a.2.val a.1.isLt).get p.1=_
      rw [DummyFill.get_set]
      simp only [hne,↓reduceIte,ih hhead.2 hp]

theorem table_le {n : ℕ} (entries : List (Fin n × Fin n)) (i : Fin n) :
    (table entries).get i ≤ n := by
  induction entries with
  | nil => simp [table,Vector.get,Fin.cast]
  | cons p entries ih =>
    change ((table entries).set p.1.val p.2.val p.1.isLt).get i ≤ _
    rw [DummyFill.get_set]
    split
    · exact Nat.le_of_lt p.2.isLt
    · exact ih

theorem table_sentinel {n : ℕ} (entries : List (Fin n × Fin n))
    (hn : (entries.map Prod.fst).Nodup) (i : Fin n) :
    (table entries).get i=n ↔ i ∉ entries.map Prod.fst := by
  constructor
  · intro he hm
    obtain ⟨p,hp,hpi⟩ := List.mem_map.mp hm
    have h := table_mem entries hn p hp
    rw [hpi,he] at h
    omega
  · exact table_absent entries i

theorem table_perm {n : ℕ} {entries other : List (Fin n × Fin n)}
    (hp : entries.Perm other) (hn : (entries.map Prod.fst).Nodup) :
    table entries=table other := by
  have hn' := hn.perm (hp.map Prod.fst)
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i,hi⟩
  change (table entries).get j=(table other).get j
  by_cases hm : j ∈ entries.map Prod.fst
  · obtain ⟨p,hp',hpi⟩ := List.mem_map.mp hm
    rw [←hpi,table_mem entries hn p hp',table_mem other hn' p (hp.mem_iff.mp hp')]
  · rw [table_absent entries j hm,table_absent other j (by
      intro h;exact hm ((hp.map Prod.fst).mem_iff.mpr h))]

/-- On a complete pair list, the sentinel implementation is exactly the
paper's stored permutation table, independently of the default array. -/
theorem table_eq_scatter {n : ℕ} (entries : List (Fin n × Fin n))
    (hp : (entries.map Prod.fst).Perm (List.finRange n)) :
    table entries=(DummyFill.scatter entries).map Fin.val := by
  have hn := (List.nodup_finRange n).perm hp.symm
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i,hi⟩
  have hm : j ∈ entries.map Prod.fst := hp.mem_iff.mpr (List.mem_finRange j)
  obtain ⟨p,hp',hpi⟩ := List.mem_map.mp hm
  change (table entries).get j=((DummyFill.scatter entries).map Fin.val).get j
  have hg : ((DummyFill.scatter entries).map Fin.val).get j=((DummyFill.scatter entries).get j).val := by
    simp [Vector.get,Fin.cast]
  rw [hg,←hpi,table_mem entries hn p hp',DummyFill.scatter_mem entries hn p hp']

/-- Chronological writes add one actual occupied source/target pair. -/
def fill {n : ℕ} (entries completed : List (Fin n × Fin n)) : Vector ℕ n :=
  completed.foldl (fun saved p => saved.set p.1.val p.2.val p.1.isLt) (table entries)

theorem fill_table {n : ℕ} (entries completed : List (Fin n × Fin n)) :
    fill entries completed=table (completed.reverse++entries) := by
  induction completed using List.reverseRecOn with
  | nil => simp [fill,table]
  | append_singleton xs p ih =>
    simp only [fill,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (fill entries xs).set p.1.val p.2.val p.1.isLt=_
    rw [ih]
    simp [List.reverse_append,table]

theorem fill_append {n : ℕ} (entries completed : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    fill entries (completed++[p])=(fill entries completed).set p.1.val p.2.val p.1.isLt := by
  simp [fill,List.foldl_append]

def realPairs {k n : ℕ} (source target : Fin k→Fin n) : List (Fin n × Fin n) :=
  (List.finRange k).map (fun i => (source i,target i))

def missingPairs {k n : ℕ} (source target : Fin k→Fin n) : List (Fin n × Fin n) :=
  (DummyFill.unused (DummyFill.incidencePorts source)).zip
    (DummyFill.unused (DummyFill.incidencePorts target))

/-- Pure semantic identification of the completed runtime scatter. The
complement lists specify the result; the machine must discover the same pairs
by sentinel reads, never receive these lists as input. -/
theorem fill_eq_permutation {k n : ℕ} (source target : Fin k→Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    fill (realPairs source target) (missingPairs source target)=
      (DummyFill.scatter (DummyFill.pairs source target)).map Fin.val := by
  rw [fill_table]
  have hp : ((missingPairs source target).reverse++realPairs source target).Perm
      (DummyFill.pairs source target) := by
    change List.Perm ((missingPairs source target).reverse++realPairs source target)
      (realPairs source target++missingPairs source target)
    exact ((List.reverse_perm _).append_right _).trans (List.perm_append_comm ..)
  have hn := (List.nodup_finRange n).perm (DummyFill.pairs_fst_perm source target hs ht).symm
  rw [table_perm hp (hn.perm (hp.map Prod.fst).symm)]
  exact table_eq_scatter _ (DummyFill.pairs_fst_perm source target hs ht)

end Maxwell.Cost.RoutingPorts.Complete
