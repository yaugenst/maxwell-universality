import Maxwell.Logical.SourceCircuit

namespace Maxwell.Logical

theorem Expression.inputUses_occurrences {v d : ℕ} (e : Expression v)
    (ids : Fin v → Fin d) (k : Fin d) :
    e.inputUses ids k = (e.occurrences.map (fun i => Circuit.hit k (ids i))).sum := by
  induction e with
  | var i => simp [Expression.inputUses, Expression.occurrences]
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb => simp [Expression.inputUses, Expression.occurrences, iha, ihb]

theorem forest_inputUses_occurrences {v d : ℕ} (es : List (Expression v))
    (ids : Fin v → Fin d) (k : Fin d) :
    (es.map (fun e => e.inputUses ids k)).sum =
      ((es.map Expression.occurrences).flatten.map (fun i => Circuit.hit k (ids i))).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
        List.sum_append, e.inputUses_occurrences, ih]

theorem hit_sum_injective {v d : ℕ} (ids : Fin v → Fin d) (hinj : Function.Injective ids)
    (k : Fin d) : (∑ i, Circuit.hit k (ids i)) ≤ 1 := by
  by_cases hex : ∃ i, k = ids i
  · obtain ⟨i, rfl⟩ := hex
    have he (j : Fin v) : Circuit.hit (ids i) (ids j) = if j = i then 1 else 0 := by
      simp [Circuit.hit, hinj.eq_iff, eq_comm]
    simp_rw [he]
    simp
  · have hne (i : Fin v) : k ≠ ids i := fun h => hex ⟨i, h⟩
    simp [Circuit.hit, hne]

theorem linearizedRows_inputUses_le_one {n d : ℕ} (rows : List (Expression n))
    (ids : Fin (forestLeafCount rows) → Fin d) (hinj : Function.Injective ids) (k : Fin d) :
    ((linearizedRows rows).map (fun e => e.inputUses ids k)).sum ≤ 1 := by
  rw [forest_inputUses_occurrences, linearizedRows_occurrences, ← List.ofFn_eq_map,
    List.sum_ofFn]
  exact hit_sum_injective ids hinj k

theorem forest_inputUses_pos {v d : ℕ} (es : List (Expression v))
    (ids : Fin v → Fin d) (k : Fin d)
    (h : 0 < (es.map (fun e => e.inputUses ids k)).sum) : ∃ i, k = ids i := by
  by_contra hnone
  have hne (i : Fin v) : k ≠ ids i := fun hi => hnone ⟨i, hi⟩
  have hz (e : Expression v) := e.inputUses_zero ids k hne
  simp only [hz, List.map_const', List.sum_replicate, smul_zero] at h
  omega

/-- All source-output reads are counted as downstream uses. The actual
compiled copy-plus-row graph has at most two such uses at every vertex. -/
theorem compileCopiedForest_charged {n : ℕ} (rows : List (Expression n))
    (k : Fin (compileCopiedForest rows).size) :
    (compileCopiedForest rows).circuit.chargedList (compileCopiedForest rows).outputs k ≤ 2 := by
  let result := compileCopiedForest rows
  let bank := (forestCopies rows).bank
  by_cases hk : k.val < bank.size
  · let j : Fin bank.size := ⟨k.val, hk⟩
    have he : k = Fin.castLE result.size_le j := by apply Fin.ext; rfl
    rw [he]
    have h := result.charged_old j
    have hu := linearizedRows_inputUses_le_one rows (copiedForestInputs rows)
      (copiedForestInputs_injective rows) j
    by_cases hz : ((linearizedRows rows).map
        (fun e => e.inputUses (copiedForestInputs rows) j)).sum = 0
    · rw [hz, Nat.add_zero] at h
      exact h.trans (bank.uses_bound j)
    · have hp : 0 < ((linearizedRows rows).map
          (fun e => e.inputUses (copiedForestInputs rows) j)).sum := Nat.pos_of_ne_zero hz
      obtain ⟨i, hi⟩ := forest_inputUses_pos (linearizedRows rows) (copiedForestInputs rows) j hp
      have hj : bank.circuit.uses j = 0 := by
        rw [hi]
        exact copiedForestInputs_unused rows i
      rw [hj, Nat.zero_add] at h
      exact h.trans (hu.trans (by omega))
  · exact (result.charged_new k (Nat.le_of_not_gt hk)).trans (by omega)

theorem sourceCircuit_charged (S : Source.SparseSystem) (precision : ℕ)
    (k : Fin (sourceCircuit S precision).size) :
    (sourceCircuit S precision).circuit.chargedList (sourceCircuit S precision).outputs k ≤ 2 :=
  compileCopiedForest_charged _ k

end Maxwell.Logical
