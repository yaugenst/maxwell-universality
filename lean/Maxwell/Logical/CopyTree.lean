import Maxwell.Logical.Compile

/-! Actual bounded-branching copy-tree allocation. A requested `extra+1`
leaves uses exactly `2*extra` new unary copy equations. Distinct leaves and
preservation of all old coordinates are proved for every input size.
-/

namespace Maxwell.Logical

structure CopyCompilation {n d : ℕ} (prior : Circuit n d) (parent : Fin d)
    (extra : ℕ) where
  size : ℕ
  size_le : d ≤ size
  circuit : Circuit n size
  extension : prior.Extends circuit
  leaves : List (Fin size)
  leaf_count : leaves.length = extra + 1
  leaf_nodup : leaves.Nodup
  allocation : size = d + 2 * extra
  preserves : ∀ (input : Fin n → ℝ) (i : Fin d),
    circuit.evaluate input 0 (Fin.castLE size_le i) = prior.evaluate input 0 i
  correct : ∀ (input : Fin n → ℝ) (leaf : Fin size), leaf ∈ leaves →
    circuit.evaluate input 0 leaf = prior.evaluate input 0 parent
  lower : ∀ leaf ∈ leaves, parent.val ≤ leaf.val
  old_usage : ∀ i : Fin d,
    circuit.uses (Fin.castLE size_le i) = prior.uses i +
      if extra = 0 then 0 else if i = parent then 2 else 0
  leaf_usage : ∀ leaf ∈ leaves,
    circuit.uses leaf = if extra = 0 then prior.uses parent else 0
  new_usage : ∀ i : Fin size, d ≤ i.val → circuit.uses i ≤ 2

def copyStep {n d : ℕ} (prior : Circuit n d) (parent : Fin d)
    (extra : ℕ)
    (result : CopyCompilation ((prior.copyGate parent).copyGate parent.castSucc)
      (Fin.last (d + 1)) extra) : CopyCompilation prior parent (extra + 1) := by
      let first : Fin result.size := Fin.castLE result.size_le (Fin.last d).castSucc
      have hsize : d ≤ result.size := (Nat.le_add_right d 2).trans result.size_le
      refine {
        size := result.size
        size_le := hsize
        circuit := result.circuit
        extension := (Circuit.Extends.append (Circuit.Extends.append .refl _) _).trans
          result.extension
        leaves := first :: result.leaves
        leaf_count := ?_
        leaf_nodup := ?_
        allocation := ?_
        preserves := ?_
        correct := ?_
        lower := ?_
        old_usage := ?_
        leaf_usage := ?_
        new_usage := ?_ }
      · simp only [List.length_cons, result.leaf_count]
      · apply List.nodup_cons.mpr
        refine ⟨?_, result.leaf_nodup⟩
        intro hm
        have h := result.lower first hm
        change d + 1 ≤ d at h
        omega
      · rw [result.allocation]
        omega
      · intro input i
        have he : Fin.castLE hsize i = Fin.castLE result.size_le i.castSucc.castSucc := by
          apply Fin.ext
          rfl
        rw [he, result.preserves]
        change ((prior.copyGate parent).append _).evaluate input 0 i.castSucc.castSucc = _
        rw [Circuit.evaluate_zero_append_old]
        change (prior.append _).evaluate input 0 i.castSucc = _
        exact prior.evaluate_zero_append_old _ input i
      · intro input leaf hm
        rcases List.mem_cons.mp hm with he | ht
        · subst leaf
          rw [show first = Fin.castLE result.size_le (Fin.last d).castSucc from rfl,
            result.preserves]
          change ((prior.copyGate parent).append _).evaluate input 0 (Fin.last d).castSucc = _
          rw [Circuit.evaluate_zero_append_old, Circuit.copyGate_last]
          change prior.evaluate input 0 parent + 0 = _
          simp
        · rw [result.correct input leaf ht]
          rw [Circuit.copyGate_last]
          change (prior.copyGate parent).evaluate input 0 parent.castSucc + 0 = _
          simp only [add_zero]
          exact prior.evaluate_zero_append_old _ input parent
      · intro leaf hm
        rcases List.mem_cons.mp hm with he | ht
        · subst leaf
          change parent.val ≤ d
          exact Nat.le_of_lt parent.isLt
        · have h := result.lower leaf ht
          change d + 1 ≤ leaf.val at h
          have hp := parent.isLt
          omega
      · intro i
        have he : Fin.castLE hsize i = Fin.castLE result.size_le i.castSucc.castSucc := by
          apply Fin.ext
          rfl
        rw [he, result.old_usage]
        have hne : i.castSucc.castSucc ≠ Fin.last (d + 1) := by
          intro h
          have hv := congrArg (fun k : Fin (d + 2) => k.val) h
          have hi := i.isLt
          simp only [Fin.val_castSucc, Fin.val_last] at hv
          omega
        simp only [Circuit.uses_copy_old, hne, ↓reduceIte, Nat.add_eq_zero_iff,
          Nat.one_ne_zero, and_false]
        by_cases hip : i = parent
        · subst i
          simp
        · have hic : i.castSucc ≠ parent.castSucc := by
            intro h
            apply hip
            exact Fin.ext (congrArg (fun k : Fin (d + 1) => k.val) h)
          simp [hip, hic]
      · intro leaf hm
        rcases List.mem_cons.mp hm with he | ht
        · subst leaf
          rw [show first = Fin.castLE result.size_le (Fin.last d).castSucc from rfl,
            result.old_usage]
          have hne : (Fin.last d).castSucc ≠ Fin.last (d + 1) := by
            intro h
            have hv := congrArg (fun k : Fin (d + 2) => k.val) h
            simp at hv
          have hp : Fin.last d ≠ parent.castSucc := by
            intro h
            have hv := congrArg (fun k : Fin (d + 1) => k.val) h
            have hi := parent.isLt
            simp only [Fin.val_last, Fin.val_castSucc] at hv
            omega
          simp [Circuit.uses_copy_old, hne, hp]
        · rw [result.leaf_usage leaf ht]
          simp
      · intro i hi
        by_cases hnew : d + 2 ≤ i.val
        · exact result.new_usage i hnew
        · have his : i.val < d + 2 := by omega
          let j : Fin (d + 2) := ⟨i.val, his⟩
          have he : i = Fin.castLE result.size_le j := by apply Fin.ext; rfl
          rw [he, result.old_usage]
          have casesj : j = (Fin.last d).castSucc ∨ j = Fin.last (d + 1) := by
            have hv : i.val = d ∨ i.val = d + 1 := by omega
            rcases hv with hv | hv
            · left; apply Fin.ext; exact hv
            · right; apply Fin.ext; exact hv
          rcases casesj with hj | hj
          · rw [hj]
            have hne : (Fin.last d).castSucc ≠ Fin.last (d + 1) := by
              intro h
              have hv := congrArg (fun k : Fin (d + 2) => k.val) h
              simp at hv
            have hp : Fin.last d ≠ parent.castSucc := by
              intro h
              have hv := congrArg (fun k : Fin (d + 1) => k.val) h
              have hip := parent.isLt
              simp only [Fin.val_last, Fin.val_castSucc] at hv
              omega
            simp [Circuit.uses_copy_old, hne, hp]
          · rw [hj]
            simp only [Circuit.uses_copy_new, ↓reduceIte, zero_add]
            split_ifs <;> omega

/-- Separating the verified step from recursion keeps proof terms shared;
the data still consist of the actual two-copy allocation at each step. -/
def copyLeaves {n d : ℕ} (prior : Circuit n d) (parent : Fin d)
    (extra : ℕ) : CopyCompilation prior parent extra :=
  match extra with
  | 0 => by
      exact {
        size := d
        size_le := le_refl _
        circuit := prior
        extension := .refl
        leaves := [parent]
        leaf_count := rfl
        leaf_nodup := by simp
        allocation := by omega
        preserves := by intro input i; rfl
        correct := by intro input leaf h; simpa using congrArg (prior.evaluate input 0) (List.mem_singleton.mp h)
        lower := by intro leaf h; simp [List.mem_singleton.mp h]
        old_usage := by intro i; simp
        leaf_usage := by intro leaf h; simp [List.mem_singleton.mp h]
        new_usage := by intro i hi; exact False.elim (Nat.not_lt_of_ge hi i.isLt) }
  | extra + 1 =>
      copyStep prior parent extra
        (copyLeaves ((prior.copyGate parent).copyGate parent.castSucc) (Fin.last (d + 1)) extra)

end Maxwell.Logical
