import Maxwell.Continuum.CalibrationInverseDescriptorBounds

/-! The executed descriptor formulas discharge the inverse kernel's storage
requirements, including conversion, preparation, arithmetic, and addresses. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] budget rawWidth dimension slotWidth bankWidth values

theorem slot_factor (v : ℕ→ℕ) :
    slotWidth v=2^60*(dimension v+1)^2*(v 304+2)*bankWidth v := by
  unfold slotWidth bankWidth
  rw [show (2:ℕ)^140=2^60*2^80 by decide]
  ring

theorem slot_lower (v : ℕ→ℕ) : 2^60*bankWidth v≤slotWidth v := by
  have h:bankWidth v≤((dimension v+1)^2*(v 304+2))*bankWidth v:=
    Nat.le_mul_of_pos_left _ (by positivity)
  calc
    _ ≤ 2^60*(((dimension v+1)^2*(v 304+2))*bankWidth v) := Nat.mul_le_mul_left _ h
    _ = slotWidth v := by rw [slot_factor];ring

theorem bankWidth_pos (v : ℕ→ℕ) : 1≤bankWidth v := by
  have h:=rawWidth_bound v
  omega

theorem continuation_eq (v : ℕ→ℕ) :
    continuationBudget (rawWidth v) (bankWidth v)=2^14*(bankWidth v+1) := by
  unfold continuationBudget
  apply max_eq_right
  have h:=rawWidth_bound v
  omega

theorem shared (v : ℕ→ℕ) :
    PartArray.sharedWidth (v 570) (rawWidth v)≤continuationBudget (rawWidth v) (bankWidth v) := by
  rw [continuation_eq]
  have h:=sharedWidth_bound v
  omega

theorem prepare (v : ℕ→ℕ) :
    2^CopyPlan.plan.length*(continuationBudget (rawWidth v) (bankWidth v)+1)≤values v 301 := by
  rw [(outputs v).2.1,continuation_eq]
  have hb:=bankWidth_pos v
  have hs:=slot_lower v
  change 2^17*(2^14*(bankWidth v+1)+1)≤slotWidth v
  omega

theorem arithmetic (v : ℕ→ℕ) :
    commonWidth (dimension v) (values v 304) (rawWidth v+1)≤values v 301 := by
  rw [(outputs v).2.2.2.1,(outputs v).2.1,slot_factor]
  have h:=rawWidth_bound v
  unfold commonWidth
  have coef:32≤(2:ℕ)^60:=by decide
  calc
    32*(dimension v+1)^2*(v 304+2)*(rawWidth v+1+1)
        ≤ 2^60*(dimension v+1)^2*(v 304+2)*bankWidth v := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ coef)) (by omega)

theorem address (v : ℕ→ℕ) :
    (values v 302).bits.length+2*(dimension v).bits.length+(values v 301).bits.length+10≤values v 301 := by
  have hh:=values_width v 302 (by decide)
  have hn:=values_width v 300 (by decide)
  have hw:=values_width v 301 (by decide)
  rw [(outputs v).1] at hn
  have hb:=bankWidth_pos v
  have hs:=slot_lower v
  rw [(outputs v).2.1]
  rw [(outputs v).2.1] at hw
  omega

#print axioms prepare
#print axioms arithmetic
#print axioms address
end Maxwell.Continuum.Calibration.InverseDescriptor
