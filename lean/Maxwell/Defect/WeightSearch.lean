import Maxwell.Defect.WeightEnclosure

/-! Executable rational square-root weight enclosures. Search enumerates
finite rational vectors and checks exact squared-error inequalities. -/

namespace Maxwell.Defect
variable {n : ℕ}

def sqrtWeightCheck (W : Fin n → ℚ) (δ : ℚ) (code : ℕ) : Bool :=
  match Encodable.decode (α := Fin n → ℚ) code with
  | none => false
  | some r => decide (∀ i, 0 ≤ r i ∧ r i ≤ 1 ∧ |r i ^ 2 - W i| ≤ δ ^ 2)

theorem sqrtWeightCheck_complete (W : Fin n → ℚ) (δ : ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 < δ) :
    ∃ code, sqrtWeightCheck W δ code = true := by
  obtain ⟨r, hr⟩ := exists_finite_rational_sqrt_proposal W δ hW hW1 hδ
  exact ⟨Encodable.encode r, by simp [sqrtWeightCheck, hr]⟩

/-- Termination follows from density of the rationals. The extracted
program uses only decoding and rational squared-error comparisons. -/
def sqrtWeightSearch (W : Fin n → ℚ) (δ : ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 < δ) : Fin n → ℚ :=
  (Encodable.decode (α := Fin n → ℚ)
    (Nat.find (sqrtWeightCheck_complete W δ hW hW1 hδ))).getD 0

theorem sqrtWeightCheck_sound (W : Fin n → ℚ) (δ : ℚ) (code : ℕ)
    (hc : sqrtWeightCheck W δ code = true) :
    ∀ i, 0 ≤ (Encodable.decode (α := Fin n → ℚ) code).getD 0 i ∧
      (Encodable.decode (α := Fin n → ℚ) code).getD 0 i ≤ 1 ∧
      |(Encodable.decode (α := Fin n → ℚ) code).getD 0 i ^ 2 - W i| ≤ δ ^ 2 := by
  cases hd : Encodable.decode (α := Fin n → ℚ) code with
  | none => simp [sqrtWeightCheck, hd] at hc
  | some r => simpa only [sqrtWeightCheck, hd, Option.getD_some, decide_eq_true_eq] using hc

theorem sqrtWeightSearch_spec (W : Fin n → ℚ) (δ : ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 < δ) :
    ∀ i, 0 ≤ sqrtWeightSearch W δ hW hW1 hδ i ∧
      sqrtWeightSearch W δ hW hW1 hδ i ≤ 1 ∧
      |sqrtWeightSearch W δ hW hW1 hδ i ^ 2 - W i| ≤ δ ^ 2 := by
  exact sqrtWeightCheck_sound W δ _
    (Nat.find_spec (sqrtWeightCheck_complete W δ hW hW1 hδ))

end Maxwell.Defect
