import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! Deterministic completion of an injective partial permutation.  Incidence
ports are marked by array writes, unused ports are enumerated in increasing
order, and the two equal-sized unused lists are zipped.  Forward and inverse
permutations are materialized by scattering the resulting complete pair list. -/

namespace Maxwell.Logical.Routing.DummyFill

theorem get_set {α : Type*} {n : ℕ} (saved : Vector α n) (i j : Fin n) (value : α) :
    (saved.set i.val value i.isLt).get j = if i = j then value else saved.get j := by
  simp [Vector.get, Fin.cast, Array.getElem_set, Fin.ext_iff]

/-- One stored membership array; its construction performs one write per port. -/
def marks {n : ℕ} (ports : List (Fin n)) : Vector Bool n :=
  ports.foldr (fun i saved => saved.set i.val true i.isLt) (Vector.replicate n false)

theorem marks_get {n : ℕ} (ports : List (Fin n)) (i : Fin n) :
    (marks ports).get i = true ↔ i ∈ ports := by
  induction ports with
  | nil => simp [marks, Vector.get, Fin.cast]
  | cons j ports ih =>
    change ((marks ports).set j.val true j.isLt).get i = true ↔ _
    rw [get_set]
    by_cases h : j = i
    · subst j
      simp
    · simp only [h, ↓reduceIte, ih, List.mem_cons]
      simp only [Ne.symm h, false_or]

/-- A single increasing pass over all ports, after sharing the membership array. -/
def unused {n : ℕ} (ports : List (Fin n)) : List (Fin n) :=
  let used := marks ports
  (List.finRange n).filter (fun i => !(used.get i))

theorem mem_unused {n : ℕ} (ports : List (Fin n)) (i : Fin n) :
    i ∈ unused ports ↔ i ∉ ports := by
  simp only [unused, List.mem_filter, List.mem_finRange, true_and]
  have hm := marks_get ports i
  cases he : (marks ports).get i <;> simp_all

theorem unused_nodup {n : ℕ} (ports : List (Fin n)) : (unused ports).Nodup :=
  (List.nodup_finRange n).filter _

/-- The given ports followed by their increasing complement enumerate all
ports exactly once. -/
theorem complete_perm {n : ℕ} (ports : List (Fin n)) (hn : ports.Nodup) :
    (ports ++ unused ports).Perm (List.finRange n) := by
  have hc : (ports ++ unused ports).Nodup := by
    rw [List.nodup_append]
    refine ⟨hn, unused_nodup ports, ?_⟩
    intro i hi j hj he
    subst j
    exact (mem_unused ports i).mp hj hi
  apply (List.perm_ext_iff_of_nodup hc (List.nodup_finRange n)).mpr
  intro i
  simp only [List.mem_append, mem_unused, List.mem_finRange, iff_true]
  exact em _

theorem complete_length {n : ℕ} (ports : List (Fin n)) (hn : ports.Nodup) :
    ports.length + (unused ports).length = n := by
  simpa using (complete_perm ports hn).length_eq

/-- A stored lookup array populated by a list of address/value pairs.  A
reverse pass followed by an iterative write pass implements this fold. -/
def scatter {n : ℕ} (pairs : List (Fin n × Fin n)) : Vector (Fin n) n :=
  pairs.foldr (fun p saved => saved.set p.1.val p.2 p.1.isLt) (Vector.ofFn id)

/-- Every supplied pair is realized when its write address is unique. -/
theorem scatter_mem {n : ℕ} (pairs : List (Fin n × Fin n))
    (hn : (pairs.map Prod.fst).Nodup) (p : Fin n × Fin n) (hp : p ∈ pairs) :
    (scatter pairs).get p.1 = p.2 := by
  induction pairs with
  | nil => simp at hp
  | cons a pairs ih =>
    have hh := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      change ((scatter pairs).set a.1.val a.2 a.1.isLt).get a.1 = _
      simp [get_set]
    · have hne : a.1.val ≠ p.1.val := by
        intro he
        apply hh.1
        exact List.mem_map.mpr ⟨p, hp, Fin.ext he.symm⟩
      have ht := ih hh.2 hp
      change ((scatter pairs).set a.1.val a.2 a.1.isLt).get p.1 = _
      rw [get_set]
      simpa only [show a.1 ≠ p.1 from fun he => hne (congrArg Fin.val he), ↓reduceIte] using ht

def incidencePorts {k n : ℕ} (source : Fin k → Fin n) : List (Fin n) :=
  (List.finRange k).map source

theorem incidencePorts_nodup {k n : ℕ} (source : Fin k → Fin n)
    (hs : Function.Injective source) : (incidencePorts source).Nodup :=
  (List.nodup_finRange k).map hs

theorem unused_lengths {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    (unused (incidencePorts source)).length = (unused (incidencePorts target)).length := by
  have ha := complete_length _ (incidencePorts_nodup source hs)
  have hb := complete_length _ (incidencePorts_nodup target ht)
  have hla : (incidencePorts source).length = k := by simp [incidencePorts]
  have hlb : (incidencePorts target).length = k := by simp [incidencePorts]
  rw [hla] at ha
  rw [hlb] at hb
  omega

/-- Real incidences retain their prescribed destinations; increasing unused
source and target ports are paired by one linear zip. -/
def pairs {k n : ℕ} (source target : Fin k → Fin n) : List (Fin n × Fin n) :=
  (List.finRange k).map (fun i => (source i, target i)) ++
    (unused (incidencePorts source)).zip (unused (incidencePorts target))

theorem pairs_fst {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    (pairs source target).map Prod.fst = incidencePorts source ++ unused (incidencePorts source) := by
  simp only [pairs, List.map_append, List.map_map]
  rw [List.map_fst_zip (le_of_eq (unused_lengths source target hs ht))]
  rfl

theorem pairs_snd {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    (pairs source target).map Prod.snd = incidencePorts target ++ unused (incidencePorts target) := by
  simp only [pairs, List.map_append, List.map_map]
  rw [List.map_snd_zip (le_of_eq (unused_lengths source target hs ht).symm)]
  rfl

theorem pairs_fst_perm {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    ((pairs source target).map Prod.fst).Perm (List.finRange n) := by
  rw [pairs_fst source target hs ht]
  exact complete_perm _ (incidencePorts_nodup source hs)

theorem pairs_snd_perm {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    ((pairs source target).map Prod.snd).Perm (List.finRange n) := by
  rw [pairs_snd source target hs ht]
  exact complete_perm _ (incidencePorts_nodup target ht)

theorem scatter_inverse {n : ℕ} (entries : List (Fin n × Fin n))
    (hf : (entries.map Prod.fst).Perm (List.finRange n))
    (hb : (entries.map Prod.snd).Perm (List.finRange n)) (i : Fin n) :
    (scatter (entries.map Prod.swap)).get ((scatter entries).get i) = i := by
  have hn := (List.nodup_finRange n).perm hf.symm
  have hbn : ((entries.map Prod.swap).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def, Prod.swap] using
      (List.nodup_finRange n).perm hb.symm
  have hi : i ∈ entries.map Prod.fst := hf.mem_iff.mpr (List.mem_finRange i)
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hi
  rw [← he, scatter_mem entries hn p hp]
  exact scatter_mem (entries.map Prod.swap) hbn p.swap (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- A concrete permutation with stored forward and inverse arrays.  The
complement matching is deterministic, using the increasing port order. -/
def extension {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) : Equiv.Perm (Fin n) :=
  let entries := pairs source target
  let forward := scatter entries
  let backward := scatter (entries.map Prod.swap)
  { toFun := fun i => forward.get i
    invFun := fun i => backward.get i
    left_inv := scatter_inverse entries (pairs_fst_perm source target hs ht)
      (pairs_snd_perm source target hs ht)
    right_inv := by
      intro i
      have h := scatter_inverse (entries.map Prod.swap)
        (by simpa only [entries, List.map_map, Function.comp_def, Prod.swap] using pairs_snd_perm source target hs ht)
        (by simpa only [entries, List.map_map, Function.comp_def, Prod.swap] using pairs_fst_perm source target hs ht) i
      simpa [forward, backward, List.map_map, Function.comp_def, Prod.swap] using h }

/-- Every prescribed incidence mapping is preserved by the materialized
completion, for all finite injective source and destination tables. -/
theorem exact_extension {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) (i : Fin k) :
    extension source target hs ht (source i) = target i := by
  apply scatter_mem (pairs source target)
    ((List.nodup_finRange n).perm (pairs_fst_perm source target hs ht).symm)
    (source i, target i)
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- The completed pair table has exactly one entry per port. -/
theorem pairs_length {k n : ℕ} (source target : Fin k → Fin n)
    (hs : Function.Injective source) (ht : Function.Injective target) :
    (pairs source target).length = n := by
  simpa only [List.length_map, List.length_finRange] using
    (pairs_fst_perm source target hs ht).length_eq

end Maxwell.Logical.Routing.DummyFill
