import Maxwell.Cost.PhysicalMaterial.ScatterMemory

namespace Maxwell.Cost.PhysicalMaterial.Scatter
set_option maxHeartbeats 1200000

/-- The proof-level contents after the first `k` runtime records. -/
def filledWords {n cells : ℕ} (locations : Fin n → List (Fin cells))
    (payload : Fin n → List Bool) (initial : Vector (List Bool) cells) : ℕ → Vector (List Bool) cells
  | 0 => initial
  | k+1 => if hk : k < n then
      scatterWords (filledWords locations payload initial k) (locations ⟨k,hk⟩) (payload ⟨k,hk⟩)
    else filledWords locations payload initial k

@[simp] theorem filledWords_zero {n cells : ℕ} (locations : Fin n → List (Fin cells))
    (payload : Fin n → List Bool) (initial : Vector (List Bool) cells) :
    filledWords locations payload initial 0 = initial := rfl

theorem filledWords_step {n cells : ℕ} (locations : Fin n → List (Fin cells))
    (payload : Fin n → List Bool) (initial : Vector (List Bool) cells) (i : Fin n) :
    filledWords locations payload initial (i.val+1) =
      scatterWords (filledWords locations payload initial i.val) (locations i) (payload i) := by
  simp only [filledWords, i.isLt, dite_true]

/-- An untouched cell retains its actual initial contents. -/
theorem filledWords_get_none {n cells : ℕ} (locations : Fin n → List (Fin cells))
    (payload : Fin n → List Bool) (initial : Vector (List Bool) cells) (k : ℕ) (x : Fin cells)
    (h : ∀ i : Fin n, i.val < k → x ∉ locations i) :
    (filledWords locations payload initial k).get x = initial.get x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [filledWords]
    split
    · rename_i hk
      rw [scatterWords_get, ite_eq_right (h ⟨k,hk⟩ (Nat.lt_succ_self k))]
      exact ih (fun i hi => h i (by omega))
    · exact ih (fun i hi => h i (by omega))

/-- A uniquely owned cell contains that record's payload after the owner has
been visited, regardless of its previous memory contents. -/
theorem filledWords_get_owner {n cells : ℕ} (locations : Fin n → List (Fin cells))
    (payload : Fin n → List Bool) (initial : Vector (List Bool) cells)
    (owner : Fin n) (x : Fin cells) (hx : x ∈ locations owner)
    (unique : ∀ i : Fin n, i ≠ owner → x ∉ locations i) (k : ℕ) (hk : owner.val < k) :
    (filledWords locations payload initial k).get x = payload owner := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [filledWords]
    split
    · rename_i hkn
      rw [scatterWords_get]
      by_cases he : (⟨k,hkn⟩ : Fin n) = owner
      · subst owner
        simp only [hx, ite_true]
      · rw [ite_eq_right (unique ⟨k,hkn⟩ he)]
        apply ih
        have hv : k ≠ owner.val := fun h => he (Fin.ext h)
        omega
    · apply ih
      have := owner.isLt
      omega

def rowNums {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (i : Fin n) (words : Vector (List Bool) cells) : Vector (List Bool) cells :=
  scatterWords words (points.map (locations i))
    (FixedWidth.bits (addressValue l.width) (Descriptors.value d i 3).bits)

def rowDens {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (i : Fin n) (words : Vector (List Bool) cells) : Vector (List Bool) cells :=
  scatterWords words (points.map (locations i))
    (FixedWidth.bits (addressValue l.width) (Descriptors.value d i 4).bits)

def filledNums {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (words : Vector (List Bool) cells) : ℕ → Vector (List Bool) cells :=
  filledWords (fun i => points.map (locations i))
    (fun i => FixedWidth.bits (addressValue l.width) (Descriptors.value d i 3).bits) words

def filledDens {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (words : Vector (List Bool) cells) : ℕ → Vector (List Bool) cells :=
  filledWords (fun i => points.map (locations i))
    (fun i => FixedWidth.bits (addressValue l.width) (Descriptors.value d i 4).bits) words

@[simp] theorem filledNums_zero {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (words : Vector (List Bool) cells) : filledNums d l points locations words 0 = words := rfl
@[simp] theorem filledDens_zero {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (words : Vector (List Bool) cells) : filledDens d l points locations words 0 = words := rfl

theorem filledNums_step {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (words : Vector (List Bool) cells) (i : Fin n) :
    filledNums d l points locations words (i.val+1) = rowNums d l points locations i
      (filledNums d l points locations words i.val) := filledWords_step _ _ _ i

theorem filledDens_step {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (points : List (Fin 3 → ℤ)) (locations : Fin n → (Fin 3 → ℤ) → Fin cells)
    (words : Vector (List Bool) cells) (i : Fin n) :
    filledDens d l points locations words (i.val+1) = rowDens d l points locations i
      (filledDens d l points locations words i.val) := filledWords_step _ _ _ i

end Maxwell.Cost.PhysicalMaterial.Scatter
