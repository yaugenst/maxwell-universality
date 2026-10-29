import Maxwell.Logical.Routing.DummyFill

/-! Linear-pass incidence ranks.  Each incidence reads its vertex's saved
counter, stores that count as its rank, then increments the counter.  Finset
prefixes below specify the result; they are not evaluated by the algorithm. -/

namespace Maxwell.Logical.Routing.IncidenceRanks

open DummyFill

private theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (j : Fin n) :
    (Vector.ofFn f).get j = f j := by simp [Vector.get, Fin.cast]

def prior {i v : ℕ} (endpoint : Fin i → Fin v) (limit : ℕ) (vertex : Fin v) : Finset (Fin i) :=
  Finset.univ.filter (fun incidence => incidence.val < limit ∧ endpoint incidence = vertex)

def priorCount {i v : ℕ} (endpoint : Fin i → Fin v) (limit : ℕ) (vertex : Fin v) : ℕ :=
  (prior endpoint limit vertex).card

@[simp] theorem mem_prior {i v : ℕ} (endpoint : Fin i → Fin v) (limit : ℕ)
    (vertex : Fin v) (incidence : Fin i) :
    incidence ∈ prior endpoint limit vertex ↔ incidence.val < limit ∧ endpoint incidence = vertex := by
  simp [prior]

theorem priorCount_zero {i v : ℕ} (endpoint : Fin i → Fin v) (vertex : Fin v) :
    priorCount endpoint 0 vertex = 0 := by simp [priorCount, prior]

theorem priorCount_succ {i v : ℕ} (endpoint : Fin i → Fin v) (limit : ℕ)
    (hl : limit < i) (vertex : Fin v) :
    priorCount endpoint (limit + 1) vertex = priorCount endpoint limit vertex +
      if endpoint ⟨limit, hl⟩ = vertex then 1 else 0 := by
  have hnot : (⟨limit, hl⟩ : Fin i) ∉ prior endpoint limit vertex := by simp
  by_cases he : endpoint ⟨limit, hl⟩ = vertex
  · have hp : prior endpoint (limit + 1) vertex = insert ⟨limit, hl⟩ (prior endpoint limit vertex) := by
      ext incidence
      simp only [mem_prior, Finset.mem_insert]
      constructor
      · intro hh
        by_cases hlt : incidence.val < limit
        · exact Or.inr ⟨hlt, hh.2⟩
        · exact Or.inl (Fin.ext (show incidence.val = limit by omega))
      · intro hh
        rcases hh with hh | hh
        · subst incidence
          exact ⟨show limit < limit + 1 by omega, he⟩
        · exact ⟨by omega, hh.2⟩
    simp only [priorCount, hp, Finset.card_insert_of_notMem hnot, he, ↓reduceIte]
  · have hp : prior endpoint (limit + 1) vertex = prior endpoint limit vertex := by
      ext incidence
      simp only [mem_prior]
      constructor
      · intro hh
        refine ⟨?_, hh.2⟩
        by_contra hlt
        have hi : incidence = ⟨limit, hl⟩ := Fin.ext (show incidence.val = limit by omega)
        exact he (hi ▸ hh.2)
      · intro hh
        exact ⟨by omega, hh.2⟩
    simp only [priorCount, hp, he, ↓reduceIte, add_zero]

structure State (vertices incidences : ℕ) where
  counters : Vector ℕ vertices
  ranks : Vector ℕ incidences

def initial (vertices incidences : ℕ) : State vertices incidences :=
  ⟨Vector.replicate vertices 0, Vector.replicate incidences 0⟩

/-- Constant many array accesses per incidence, using only the saved state. -/
def step {i v : ℕ} (endpoint : Fin i → Fin v) (incidence : Fin i) (saved : State v i) : State v i :=
  let vertex := endpoint incidence
  let rank := saved.counters.get vertex
  ⟨saved.counters.set vertex.val (rank + 1) vertex.isLt,
    saved.ranks.set incidence.val rank incidence.isLt⟩

theorem step_ranks {i v : ℕ} (endpoint : Fin i → Fin v) (incidence queried : Fin i) (saved : State v i) :
    (step endpoint incidence saved).ranks.get queried =
      if incidence = queried then saved.counters.get (endpoint incidence) else saved.ranks.get queried :=
  get_set saved.ranks incidence queried _

def run {i v : ℕ} (endpoint : Fin i → Fin v) : (limit : ℕ) → limit ≤ i → State v i
  | 0, _ => initial v i
  | limit + 1, hl =>
      let saved := run endpoint limit (by omega)
      step endpoint ⟨limit, by omega⟩ saved

theorem counters_eq {i v : ℕ} (endpoint : Fin i → Fin v) (limit : ℕ)
    (hl : limit ≤ i) (vertex : Fin v) :
    (run endpoint limit hl).counters.get vertex = priorCount endpoint limit vertex := by
  induction limit generalizing vertex with
  | zero => simp [run, initial, Vector.get, Fin.cast, priorCount_zero]
  | succ limit ih =>
    simp only [run, step, get_set, ih]
    rw [priorCount_succ endpoint limit (by omega)]
    split_ifs with he
    · rw [he]
    · rfl

theorem rank_eq {i v : ℕ} (endpoint : Fin i → Fin v) (limit : ℕ)
    (hl : limit ≤ i) (incidence : Fin i) (hi : incidence.val < limit) :
    (run endpoint limit hl).ranks.get incidence = priorCount endpoint incidence.val (endpoint incidence) := by
  induction limit with
  | zero => omega
  | succ limit ih =>
    simp only [run, step_ranks]
    by_cases he : (⟨limit, by omega⟩ : Fin i) = incidence
    · simp only [he, ↓reduceIte]
      have hv : limit = incidence.val := congrArg Fin.val he
      rw [counters_eq]
      exact congrArg (fun limit => priorCount endpoint limit (endpoint incidence)) hv
    · simp only [he, ↓reduceIte]
      apply ih
      have hv : incidence.val ≠ limit := fun hh => he (Fin.ext hh.symm)
      omega

def DegreeBound {i v : ℕ} (endpoint : Fin i → Fin v) : Prop :=
  ∀ vertex, (Finset.univ.filter (fun incidence => endpoint incidence = vertex)).card ≤ 3

theorem priorCount_lt_three {i v : ℕ} (endpoint : Fin i → Fin v)
    (hd : DegreeBound endpoint) (incidence : Fin i) :
    priorCount endpoint incidence.val (endpoint incidence) < 3 := by
  have hnot : incidence ∉ prior endpoint incidence.val (endpoint incidence) := by simp
  have hsub : insert incidence (prior endpoint incidence.val (endpoint incidence)) ⊆
      Finset.univ.filter (fun j => endpoint j = endpoint incidence) := by
    intro j hj
    simp only [Finset.mem_insert, mem_prior] at hj
    rcases hj with rfl | hj
    · simp
    · simpa using hj.2
  have hc := (Finset.card_le_card hsub).trans (hd (endpoint incidence))
  rw [Finset.card_insert_of_notMem hnot] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

/-- The result consists of actual saved ranks; the final linear pass packages
the already computed values in Fin 3 using the erased degree-bound proof. -/
def ranks {i v : ℕ} (endpoint : Fin i → Fin v) (hd : DegreeBound endpoint) : Vector (Fin 3) i :=
  let saved := run endpoint i le_rfl
  Vector.ofFn (fun incidence => ⟨saved.ranks.get incidence, by
    rw [rank_eq endpoint i le_rfl incidence incidence.isLt]
    exact priorCount_lt_three endpoint hd incidence⟩)

@[simp] theorem ranks_get_val {i v : ℕ} (endpoint : Fin i → Fin v)
    (hd : DegreeBound endpoint) (incidence : Fin i) :
    ((ranks endpoint hd).get incidence).val = priorCount endpoint incidence.val (endpoint incidence) := by
  simp only [ranks, get_ofFn]
  exact rank_eq endpoint i le_rfl incidence incidence.isLt

theorem priorCount_strict {i v : ℕ} (endpoint : Fin i → Fin v) (a b : Fin i)
    (hab : a.val < b.val) (he : endpoint a = endpoint b) :
    priorCount endpoint a.val (endpoint a) < priorCount endpoint b.val (endpoint b) := by
  have hnot : a ∉ prior endpoint a.val (endpoint a) := by simp
  have hsub : insert a (prior endpoint a.val (endpoint a)) ⊆ prior endpoint b.val (endpoint b) := by
    intro j hj
    simp only [Finset.mem_insert, mem_prior] at hj ⊢
    rcases hj with rfl | hj
    · exact ⟨hab, he⟩
    · exact ⟨by omega, hj.2.trans he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

/-- A vertex and its saved rank uniquely identify the input incidence. -/
theorem endpoint_rank_injective {i v : ℕ} (endpoint : Fin i → Fin v) (hd : DegreeBound endpoint) :
    Function.Injective (fun incidence => (endpoint incidence, (ranks endpoint hd).get incidence)) := by
  intro a b he
  have hv := congrArg Prod.fst he
  have hr := congrArg (fun p : Fin v × Fin 3 => p.2.val) he
  simp only [ranks_get_val] at hr
  apply Fin.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hc := priorCount_strict endpoint a b hlt hv
    omega
  · have hc := priorCount_strict endpoint b a hgt hv.symm
    omega

end Maxwell.Logical.Routing.IncidenceRanks
