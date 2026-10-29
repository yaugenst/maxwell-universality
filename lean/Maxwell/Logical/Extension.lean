import Maxwell.Logical.Circuit
import Maxwell.Logical.Usage

namespace Maxwell.Logical.Circuit

/-- A concrete sequence of appended equations. -/
inductive Extends {n d : ℕ} (prior : Circuit n d) :
    {s : ℕ} → Circuit n s → Prop where
  | refl : Extends prior prior
  | append {s : ℕ} {current : Circuit n s} (h : Extends prior current)
      (coefficient : Fin s → ℝ) : Extends prior (current.append coefficient)

namespace Extends

theorem size_le {n d s : ℕ} {prior : Circuit n d} {current : Circuit n s}
    (h : Extends prior current) : d ≤ s := by
  induction h with
  | refl => exact le_refl _
  | append _ _ ih => exact ih.trans (Nat.le_succ _)

theorem trans {n d s t : ℕ} {a : Circuit n d} {b : Circuit n s}
    {c : Circuit n t} (hab : Extends a b) (hbc : Extends b c) : Extends a c := by
  induction hbc with
  | refl => exact hab
  | append _ coefficient ih => exact ih.append coefficient

/-- Every old equation receives its own actual residual coordinate. -/
theorem evaluate_old {n d s : ℕ} {prior : Circuit n d} {current : Circuit n s}
    (h : Extends prior current) (input : Fin n → ℝ) (error : Fin s → ℝ)
    (i : Fin d) :
    current.evaluate input error (Fin.castLE h.size_le i) =
      prior.evaluate input (fun j => error (Fin.castLE h.size_le j)) i := by
  induction h with
  | refl => rfl
  | @append s current h coefficient ih =>
      have hi : Fin.castLE (h.append coefficient).size_le i =
          (Fin.castLE h.size_le i).castSucc := by apply Fin.ext; rfl
      rw [hi, evaluate_append_castSucc, ih]
      rfl

theorem uses_old_mono {n d s : ℕ} {prior : Circuit n d} {current : Circuit n s}
    (h : Extends prior current) (i : Fin d) :
    prior.uses i ≤ current.uses (Fin.castLE h.size_le i) := by
  induction h with
  | refl => exact le_refl _
  | @append s current h coefficient ih =>
      have hi : Fin.castLE (h.append coefficient).size_le i =
          (Fin.castLE h.size_le i).castSucc := by apply Fin.ext; rfl
      rw [hi, uses_append_old]
      exact ih.trans (Nat.le_add_right _ _)

theorem residual_old {n d s : ℕ} {prior : Circuit n d} {current : Circuit n s}
    (h : Extends prior current) (input : Fin n → ℝ) (state : Fin s → ℝ)
    (i : Fin d) :
    current.residual input state (Fin.castLE h.size_le i) =
      prior.residual input (fun j => state (Fin.castLE h.size_le j)) i := by
  induction h with
  | refl => rfl
  | @append s current h coefficient ih =>
      have hi : Fin.castLE (h.append coefficient).size_le i =
          (Fin.castLE h.size_le i).castSucc := by apply Fin.ext; rfl
      rw [hi]
      simp only [residual, Fin.snoc_castSucc]
      rw [ih]
      rfl

end Extends
end Maxwell.Logical.Circuit
