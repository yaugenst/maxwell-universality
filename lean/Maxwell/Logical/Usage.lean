import Maxwell.Logical.Circuit

/-! Actual graph fanout of a finite circuit. This definition counts each
nonzero downstream incidence once; equation diagonals are counted separately.
-/

namespace Maxwell.Logical.Circuit

noncomputable def uses {n d : ℕ} (c : Circuit n d) : Fin d → ℕ := by
  classical
  exact match c with
  | .input => 0
  | .append prior coefficient =>
      Fin.snoc (fun i => prior.uses i + if coefficient i = 0 then 0 else 1) 0

@[simp] theorem uses_input {n : ℕ} (i : Fin n) :
    (Circuit.input : Circuit n n).uses i = 0 := rfl

@[simp] theorem uses_append_old {n d : ℕ} (c : Circuit n d)
    (coefficient : Fin d → ℝ) (i : Fin d) :
    (c.append coefficient).uses i.castSucc = c.uses i + if coefficient i = 0 then 0 else 1 := by
  classical
  simp [uses]

@[simp] theorem uses_append_new {n d : ℕ} (c : Circuit n d)
    (coefficient : Fin d → ℝ) : (c.append coefficient).uses (Fin.last d) = 0 := by
  simp [uses]

@[simp] theorem uses_copy_old {n d : ℕ} (c : Circuit n d)
    (parent i : Fin d) :
    (c.copyGate parent).uses i.castSucc = c.uses i + if i = parent then 1 else 0 := by
  by_cases h : i = parent <;> simp [copyGate, h]

@[simp] theorem uses_copy_new {n d : ℕ} (c : Circuit n d) (parent : Fin d) :
    (c.copyGate parent).uses (Fin.last d) = 0 := by simp [copyGate]

theorem uses_copy_other {n d : ℕ} (c : Circuit n d) (parent i : Fin d)
    (h : i ≠ parent) : (c.copyGate parent).uses i.castSucc = c.uses i := by simp [h]

theorem uses_copy_parent {n d : ℕ} (c : Circuit n d) (parent : Fin d) :
    (c.copyGate parent).uses parent.castSucc = c.uses parent + 1 := by simp

def hit {d : ℕ} (i j : Fin d) : ℕ := if i = j then 1 else 0

noncomputable def charged {n d : ℕ} (c : Circuit n d) (output i : Fin d) : ℕ :=
  c.uses i + hit i output

theorem uses_le_charged {n d : ℕ} (c : Circuit n d) (output i : Fin d) :
    c.uses i ≤ c.charged output i := Nat.le_add_right _ _

@[simp] theorem charged_append_new {n d : ℕ} (c : Circuit n d) (a : Fin d → ℝ) :
    (c.append a).charged (Fin.last d) (Fin.last d) = 1 := by simp [charged, hit]

@[simp] theorem charged_append_old {n d : ℕ} (c : Circuit n d) (a : Fin d → ℝ)
    (i : Fin d) : (c.append a).charged (Fin.last d) i.castSucc =
      c.uses i + if a i = 0 then 0 else 1 := by
  have hne : i.castSucc ≠ Fin.last d := by
    intro h
    have hv := congrArg (fun j : Fin (d + 1) => j.val) h
    have hi := i.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp [charged, hit, hne]

theorem charged_scaled_old_le {n d : ℕ} (c : Circuit n d) (parent i : Fin d) (w : ℝ) :
    (c.scaledGate parent w).charged (Fin.last d) i.castSucc ≤ c.charged parent i := by
  by_cases hi : i = parent <;> by_cases hw : w = 0 <;> simp [scaledGate, charged, hit, hi, hw]

theorem charged_add_old_le {n d : ℕ} (c : Circuit n d) (left right i : Fin d) :
    (c.additionGate left right).charged (Fin.last d) i.castSucc ≤
      c.uses i + hit i left + hit i right := by
  simp only [additionGate, charged_append_old]
  by_cases h : i = left ∨ i = right
  · have hd : 1 ≤ hit i left + hit i right := by
      rcases h with h | h <;> simp [hit, h]
    split_ifs <;> omega
  · push Not at h
    simp [hit, h.1, h.2]

theorem hit_castLE {d s : ℕ} (h : d ≤ s) (i j : Fin d) :
    hit (Fin.castLE h i) (Fin.castLE h j) = hit i j := by
  simp [hit, Fin.ext_iff]

end Maxwell.Logical.Circuit
